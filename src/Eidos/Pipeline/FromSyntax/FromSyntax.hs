-- | Build the intermediate representation ('Theory') from a parsed 'TheoryDecl'.
module Eidos.Pipeline.FromSyntax.FromSyntax
  ( buildTheoryFromFile
  , buildTheoryPure
  , buildTheoryFromResolved
  , buildTheoryWithResolver
  , BuildError
  ) where

import           Control.Monad        (forM_, when, unless, foldM)
import           Data.Char            (isUpper)
import           Data.List            (find, intercalate, isSuffixOf)
import qualified Data.Map.Strict      as Map
import           Data.Maybe           (fromJust, fromMaybe, mapMaybe)
import           System.FilePath      (takeDirectory)

import           Eidos.Pipeline.Parse.AST            hiding (theoryBody, theoryName, funcName, funcDomain, relName)
import qualified Eidos.Pipeline.Parse.AST            as AST

import           Eidos.Pipeline.Resolution.ExternalRef    hiding (mockResolver)
import           Eidos.Pipeline.FromSyntax.IR
import           Eidos.Pipeline.Parse.Parser         (parseString)
import           Eidos.Pipeline.FromSyntax.Check.TypeCheck
import           Eidos.Pipeline.FromSyntax.Check.SubLanguage

import           Eidos.Pipeline.Resolution.Resolution    (resolveExternalRefs, resolveWithFn, BuildError)
import qualified Eidos.Pipeline.IRProcessing.NamingConventions as NC

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

-- | Build a 'Theory' from a pre-resolved reference map and a 'TheoryDecl'.
buildTheoryFromResolved
  :: Map.Map String (TheoryBody, TheoryType)
  -> [TheoryType]         -- ^ sub-language constraints from the top-level file extension
  -> TheoryDecl
  -> Either BuildError Theory
buildTheoryFromResolved refMap constraints td =
  decorateTheoryBody refMap (AST.theoryBody td) Nothing "" False constraints


-- | IO entry point: runs the external-reference pre-pass, then builds the IR.
buildTheoryFromFile :: FilePath -> TheoryDecl -> IO (Either BuildError Theory)
buildTheoryFromFile filePath td = do
  let tt = theoryTypeFromFilePath filePath
  resolveResult <- resolveExternalRefs filePath td
  case resolveResult of
    Left err     -> return (Left err)
    Right refMap -> return $ buildTheoryFromResolved refMap [tt] td

-- | Pure entry point with no external references (for @--pure@ mode and testing).
buildTheoryPure :: TheoryDecl -> Either BuildError Theory
buildTheoryPure td = buildTheoryFromResolved Map.empty [] td

-- | Pure entry point with a custom resolver function (for testing external references).
buildTheoryWithResolver
  :: (Maybe String -> String -> Either ExternalRefError ExternalRefResult)
  -> Maybe String
  -> TheoryDecl
  -> Either BuildError Theory
buildTheoryWithResolver fn baseCtx td =
  case resolveWithFn fn baseCtx td of
    Left err    -> Left err
    Right refMap -> buildTheoryFromResolved refMap [] td

-- ---------------------------------------------------------------------------
-- Core theory builder (pure)
-- ---------------------------------------------------------------------------

-- | Build a 'Theory' from a 'TheoryBody'.
--
-- 'refMap' supplies all external subtheories already loaded by the pre-pass.
-- 'constraints' is the accumulated list of 'TheoryType' restrictions in
-- force for this body.
decorateTheoryBody
  :: Map.Map String (TheoryBody, TheoryType)
  -> TheoryBody
  -> Maybe Theory
  -> String
  -> Bool
  -> [TheoryType]
  -> Either BuildError Theory
decorateTheoryBody refMap body parentMaybe name isReflection constraints = do

  -- ── Sublanguage check (before anything else) ──────────────────────────
  either Left Right $ checkTheoryBody constraints body

  -- ── Base theory skeleton ──────────────────────────────────────────────
  let th0 = createTheory parentMaybe name isReflection

  -- ── Register built-in sorts ───────────────────────────────────────────
  let thA = addSortToTh th0 (theoryUniverse th0)
      thB = addSortToTh thA (theoryDomain   th0)
      thC = addSortToTh thB (theoryProp     th0)

  -- ── Pass 1: subtheories ───────────────────────────────────────────────
  (th1, subtheories) <- foldM (buildSubtheoryEntry refMap constraints) (thC, []) (sections body)
  let th2 = th1 { theorySubtheories = subtheories }

  -- ── Pass 2: signature ─────────────────────────────────────────────────
  th3 <- foldM (buildSignatureSection th2) th2 (sections body)

  -- ── Pass 2.5: abbreviations ───────────────────────────────────────────
  -- Abbreviation entities are added to theoryObjectsByName so that Pass 3
  -- name resolution can find them when they are called in axiom bodies.
  th3a <- foldM buildAbbreviationsSection th3 (sections body)

  -- ── Pass 3: axioms ────────────────────────────────────────────────────
  th4 <- foldM (buildAxiomsSection th3a) th3a (sections body)

  -- ── Mereological translations ─────────────────────────────────────────
  let translations = concatMap (mereologicalTranslation th4) (theoryFacts th4)
  let th5 = th4 { theoryFacts = theoryFacts th4 ++ translations }

  return th5

-- ---------------------------------------------------------------------------
-- Pass 1 — Subtheories
-- ---------------------------------------------------------------------------

buildSubtheoryEntry
  :: Map.Map String (TheoryBody, TheoryType)
  -> [TheoryType]
  -> (Theory, [Theory])
  -> Section
  -> Either BuildError (Theory, [Theory])
buildSubtheoryEntry refMap constraints (th, acc) (SectionSubtheories (SubtheoriesSection entries)) =
  foldM (processEntry refMap constraints) (th, acc) entries
buildSubtheoryEntry _ _ (th, acc) _ = Right (th, acc)

processEntry
  :: Map.Map String (TheoryBody, TheoryType)
  -> [TheoryType]
  -> (Theory, [Theory])
  -> SubtheoryEntry
  -> Either BuildError (Theory, [Theory])
processEntry refMap constraints (th, subs) entry = case entry of
  SubtheoryEntryGroup (SubtheoryGroup kw items) ->
    foldM (processItem refMap constraints kw) (th, subs) items
  SubtheoryEntryItem item ->
    let kw = fromMaybe "named" (itemQualifier item)
    in processItem refMap constraints kw (th, subs) item

processItem
  :: Map.Map String (TheoryBody, TheoryType)
  -> [TheoryType]
  -> String
  -> (Theory, [Theory])
  -> SubtheoryItem
  -> Either BuildError (Theory, [Theory])
processItem refMap constraints kw (th, subs) item = do
  let subName = fromMaybe "" (itemName item)

  when (subName == "") $
    Left "All subtheories must have names."

  let isRefl     = kw == "reflection"
      isImplicit = kw == "implicit"

  (subBody, extInfo) <- resolveSubtheoryBody refMap item

  let subConstraints = case extInfo of
        Nothing           -> constraints
        Just (_, extType) -> addConstraint constraints extType

  sub <- decorateTheoryBody refMap subBody (Just th) subName isRefl subConstraints

  let th'    = addSubtheoryToTheory th sub
  th''      <- propagateSubtheory th' subName isImplicit isRefl sub
  let thFinal =
        if isImplicit
          then th''
            { theoryUsesDomain = theoryUsesDomain th'' || theoryUsesDomain sub
            , theoryUsesProp   = theoryUsesProp th'' || theoryUsesProp sub
            }
          else th''

  return (thFinal, subs ++ [sub])

-- | Add a 'TheoryType' to the constraint list, skipping 'PlainTheory' and
-- 'SOLTheory' (which are maximally permissive) and avoiding duplicates.
addConstraint :: [TheoryType] -> TheoryType -> [TheoryType]
addConstraint existing tt
  | tt `elem` [PlainTheory, SOLTheory] = existing
  | tt `elem` existing                 = existing
  | otherwise                           = existing ++ [tt]

-- | Resolve a subtheory definition: inline bodies are returned directly;
-- external refs are looked up in the pre-pass map.
-- The second component carries the resolved 'TheoryType' for external refs
-- so the caller can extend the constraint list.
resolveSubtheoryBody
  :: Map.Map String (TheoryBody, TheoryType)
  -> SubtheoryItem
  -> Either BuildError (TheoryBody, Maybe (String, TheoryType))
resolveSubtheoryBody _refMap (SubtheoryItem _ _ (SubtheoryBody b)) =
  Right (b, Nothing)
resolveSubtheoryBody refMap (SubtheoryItem _ _ (SubtheoryExternalRef ref)) =
  let refPath = case ref of { ('@':rest) -> rest; _ -> ref }
  in case Map.lookup refPath refMap of
       Nothing         -> Left $ "External reference not found in pre-pass map: " ++ refPath
       Just (body, tt) -> Right (body, Just (refPath, tt))

addSubtheoryToTheory :: Theory -> Theory -> Theory
addSubtheoryToTheory th sub =
  th { theorySubtheories = theorySubtheories th ++ [sub] }

-- ---------------------------------------------------------------------------
-- Pass 2 — Signature
-- ---------------------------------------------------------------------------

buildSignatureSection
  :: Theory -> Theory -> Section -> Either BuildError Theory
buildSignatureSection th0 th (SectionSignature (SignatureSection items)) =
  foldM (buildSignatureItem th0) th items
buildSignatureSection _ th _ = Right th

buildSignatureItem
  :: Theory -> Theory -> SignatureItem -> Either BuildError Theory
buildSignatureItem th0 th item = do
  let shouldInsertDeclaration name newEntity =
        case Map.lookup name (theoryObjectsByName th) of
          Nothing -> Right True
          Just existing
            | all (entitiesCompatible newEntity) existing -> Right False
            | otherwise ->
                Left $ "Name conflict: '" ++ name ++ "' already refers to a different entity"

  case item of

    SigSimpleSort (SimpleSortDeclaration nm) -> do
      let s = mkSort th SortKindFromSignature nm FromSignature
          entity = EntitySort s
      shouldInsert <- shouldInsertDeclaration nm entity
      return (if shouldInsert then addSortToTh th s else th)

    SigRelationalSort (RelationalSortDeclaration nm rel sortExprAST) -> do
      parentSort <- lookupSortByExpr th sortExprAST
      let th' = markTheorySortExprUsage th sortExprAST
          s   = mkRelatedSort th' rel nm parentSort
          entity = EntitySort s
      shouldInsert <- shouldInsertDeclaration nm entity
      if shouldInsert
        then do
          let th1 = addSortToTh th' s
              th2 = relationalSortFacts th1 rel s parentSort
          return th2
        else return th'

    SigFunction (FunctionDeclaration nm domainExprs codomainExpr) -> do
      argSorts <- mapM (lookupSortByExpr th) domainExprs
      resSort  <- lookupSortByExpr th codomainExpr
      let th' = foldl markTheorySortExprUsage (markTheorySortExprUsage th codomainExpr) domainExprs
      if firstLetterIsUppercase nm
        then do
          let f = mkSOLFunction th' nm FunctionKindSOLFunctionFromTheory argSorts resSort FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityFunction f)
          return (if shouldInsert then addEntityToTh th' (EntityFunction f) else th')
        else do
          let (f, domSort, invFn, dirImg, invImg) =
                mkFOLFunction th' nm argSorts resSort FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityFunction f)
          if shouldInsert
            then do
              let th1  = addEntityToTh th'  (EntitySort domSort)
                  th2  = addEntityToTh th1 (EntityMereological (sortMin domSort))
                  th3  = addEntityToTh th2 (EntityMereological (sortMax domSort))
                  invDomSort = case funcDomain invFn of { Just d -> d; Nothing -> domSort }
                  th4  = addEntityToTh th3 (EntitySort invDomSort)
                  th5  = addEntityToTh th4 (EntityMereological (sortMin invDomSort))
                  th6  = addEntityToTh th5 (EntityMereological (sortMax invDomSort))
                  th7  = addEntityToTh th6 (EntityFunction f)
                  th8  = addEntityToTh th7 (EntityFunction invFn)
                  th9  = addEntityToTh th8 (EntityFunction dirImg)
                  th10 = addEntityToTh th9 (EntityFunction invImg)
              return th10
            else return th'

    SigIndividual (IndividualDeclaration nm sortExprAST) -> do
      s <- lookupSortByExpr th sortExprAST
      let th' = markTheorySortExprUsage th sortExprAST
      let isPropSort'    = sortKind s == SortKindProp
          isUniverseSort' = sortKind s == SortKindUniverse

      when (isPropSort' && not (firstLetterIsUppercase nm)) $
        Left $ "Proposition names must start with uppercase: " ++ nm
      when (isUniverseSort' && not (firstLetterIsUppercase nm)) $
        Left $ "Bare mereological object names must start with uppercase: " ++ nm
      when (not isPropSort' && not isUniverseSort' && firstLetterIsUppercase nm) $
        Left $ "Individual names must start with lowercase: " ++ nm

      let moKind =
            if isPropSort'
              then MereologicalEntityKindProposition
              else if isUniverseSort'
                then MereologicalEntityKindIndividual
                else MereologicalEntityKindIndividual
          mo     = mkMereo th' moKind nm s FromSignature
          entity = EntityMereological mo
      shouldInsert <- shouldInsertDeclaration nm entity
      return (if shouldInsert then addEntityToTh th' entity else th')

    SigSet (SetDeclaration nm sortExprs) -> do
      when (not (firstLetterIsUppercase nm)) $
        Left $ "Set/relation names must start with uppercase: " ++ nm
      argSorts <- mapM (lookupSortByExpr th) sortExprs
      let th' = foldl markTheorySortExprUsage th sortExprs
      if length argSorts == 1
        then do
          let mo     = mkMereo th' MereologicalEntityKindSet nm (head argSorts) FromSignature
              entity = EntityMereological mo
          shouldInsert <- shouldInsertDeclaration nm entity
          return (if shouldInsert then addEntityToTh th' entity else th')
        else do
          let rel = mkRelation th' nm argSorts FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityRelation rel)
          return (if shouldInsert then addEntityToTh th' (EntityRelation rel) else th')

-- ---------------------------------------------------------------------------
-- Pass 2.5 — Abbreviations
-- ---------------------------------------------------------------------------

-- | Process a single 'SectionAbbreviations' section.
-- Each item is validated, converted to an 'AbbrevDef', stored in
-- 'theoryUserAbbrevDefs', and also registered in 'theoryObjectsByName' as a
-- synthetic SOL-function-shaped entity so that Pass 3 name resolution can
-- resolve calls to user abbreviations inside axiom bodies.
buildAbbreviationsSection :: Theory -> Section -> Either BuildError Theory
buildAbbreviationsSection th (SectionAbbreviations (AbbreviationsSection items)) =
  foldM buildAbbrevDefItem th items
buildAbbreviationsSection th _ = Right th

buildAbbrevDefItem :: Theory -> AbbrevDefItem -> Either BuildError Theory
buildAbbrevDefItem th item = do
  let nm     = abbrevItemName   item
      params = abbrevItemParams item
      bodyT  = abbrevItemBody   item

  -- Validate: name must start uppercase (already checked in parser, but
  -- defensive check here too).
  when (null nm || not (firstLetterIsUppercase nm)) $
    Left $ "Abbreviation name must start with uppercase: " ++ nm

  -- Validate: no duplicate parameter names.
  let dupParams = [ p | p <- params, length (filter (== p) params) > 1 ]
  case dupParams of
    (p:_) -> Left $ "Duplicate parameter name '" ++ p ++ "' in abbreviation '" ++ nm ++ "'"
    []    -> return ()

  -- Validate: name must not clash with a compiler-internal abbreviation.
  when (nm `elem` map abbrevName allAbbrevDefs) $
    Left $ "Abbreviation name '" ++ nm ++ "' clashes with a compiler-internal abbreviation"

  -- Collect the set of known abbreviation names so the body can reference
  -- previously-defined user abbreviations.
  let knownAbbrevNames = map abbrevName (theoryUserAbbrevDefs th)

  -- Convert AST Term body to MereoExpr, with params as bound variable names.
  body <- astTermToMereoExpr nm params knownAbbrevNames bodyT

  let ad = AbbrevDef nm params body

  -- Register as a synthetic SOL-function entity so name resolution finds it.
  let universe = theoryUniverse th
      syntheticFn = mkSOLFunction th nm FunctionKindUserAbbreviation
                      (replicate (length params) universe) universe FromSignature
      th1 = addEntityToTh th (EntityFunction syntheticFn)

  -- Store in theoryUserAbbrevDefs.
  let th2 = th1 { theoryUserAbbrevDefs = theoryUserAbbrevDefs th1 ++ [ad] }

  return th2

-- | Convert an AST 'Term' to a 'MereoExpr' for use as an abbreviation body.
-- Only mereological operators (+, ×, -, ⇒, ∸) are allowed; any other
-- construct is rejected with a descriptive error.
--
-- @params@ are the parameter names — they resolve as 'MVar'.
-- @knownAbbrevs@ are names of previously-defined abbreviations that may be
-- called inside this body.
astTermToMereoExpr
  :: String    -- ^ Abbreviation name (for error messages)
  -> [String]  -- ^ Parameter names
  -> [String]  -- ^ Known user abbreviation names
  -> Term
  -> Either BuildError MereoExpr
astTermToMereoExpr ctx params knownAbbrevs (Term leftF rests) = do
  l  <- goFactor leftF
  rs <- mapM goOFF rests
  return (foldl applyOp l rs)
  where
    applyOp acc (op, rhs) = case op of
      "+"  -> MSum     acc rhs
      "×"  -> MProd    acc rhs
      "*"  -> MProd    acc rhs
      "-"  -> MDiff    rhs  acc   -- MDiff(a,b) = b - a, i.e. b → a
      "⇒"  -> MRevDiff acc rhs
      "∸"  -> MSymDiff acc rhs
      "∪"  -> MSum     acc rhs
      "∩"  -> MProd    acc rhs
      other -> error $ "astTermToMereoExpr: unexpected op " ++ other

    goOFF (OperationFollowedByFactor _ op rightF) = do
      rhs <- goFactor rightF
      return (op, rhs)

    goFactor (Factor base suffixes) = case suffixes of
      [] -> goBase base
      [SuffixCall (CallSuffix args)] -> do
        -- Abbreviation application: Name(arg1, arg2, …)
        name <- case base of
          BTAtomic (ConstantRef [] n) -> return n
          _ -> Left $ "In abbreviation '" ++ ctx ++ "': call target must be a plain name"
        unless (name `elem` knownAbbrevs
                || name `elem` map abbrevName allAbbrevDefs) $
          Left $ "In abbreviation '" ++ ctx ++ "': unknown abbreviation '" ++ name ++ "'"
        argExprs <- mapM (astTermToMereoExpr ctx params knownAbbrevs) args
        return (MAbbrevApp name argExprs)
      _ ->
        Left $ "In abbreviation '" ++ ctx ++ "': unsupported term suffix in body"

    goBase (BTAtomic (ConstantRef [] name))
      | name `elem` params = return (MVar name)
      | name `elem` knownAbbrevs
        || name `elem` map abbrevName allAbbrevDefs =
          -- Zero-argument abbreviation reference — unusual but allow it.
          return (MAbbrevApp name [])
      | otherwise =
          Left $ "In abbreviation '" ++ ctx ++ "': unknown name '" ++ name
              ++ "' (not a parameter or known abbreviation)"
    goBase (BTParen inner) = do
      -- Parenthesised expression: only pure-term form is accepted.
      case extractTermFromPropExpr inner of
        Just t  -> astTermToMereoExpr ctx params knownAbbrevs t
        Nothing -> Left $ "In abbreviation '" ++ ctx
                       ++ "': parenthesised body must be a mereological term, "
                       ++ "not a proposition"
    goBase other =
      Left $ "In abbreviation '" ++ ctx ++ "': unsupported base term in body: "
          ++ describeBase other

-- | Extract the inner 'Term' from a 'PropExpr' that is a plain term
-- (no propositional connectives, no quantifiers).
extractTermFromPropExpr :: PropExpr -> Maybe Term
extractTermFromPropExpr (PropExpr (RightImpl left Nothing) []) =
  case left of
    LeftImpl (Disj (Conj (NegChild (Quantified [] (AtomicProp (TermPair t [])))) []) []) [] ->
      Just t
    _ -> Nothing
extractTermFromPropExpr _ = Nothing

describeBase :: BaseTerm -> String
describeBase (BTAtomic _)                 = "qualified constant reference"
describeBase (BTEvaluationInTheory _)     = "evaluation-in-theory expression"
describeBase (BTProjectionToInterval _)   = "projection-to-interval"
describeBase (BTProjectionToSort _)       = "projection-to-sort"
describeBase (BTGeneralizedSumOrProduct _) = "generalized sum or product"
describeBase (BTSetComprehension _)       = "set comprehension"
describeBase (BTDescription _)            = "description (ι)"
describeBase (BTSingleton _)              = "singleton"
describeBase (BTParen _)                  = "parenthesised expression"

-- ---------------------------------------------------------------------------
-- Pass 3 — Axioms
-- ---------------------------------------------------------------------------

buildAxiomsSection
  :: Theory -> Theory -> Section -> Either BuildError Theory
buildAxiomsSection th0 th (SectionAxioms (AxiomsWrapper axSections)) =
  foldM (buildAxSection th0) th axSections
buildAxiomsSection th0 th (SectionBareAxioms axSection) =
  buildAxSection th0 th axSection
buildAxiomsSection _ th _ = Right th

buildAxSection
  :: Theory -> Theory -> AxiomsSection -> Either BuildError Theory
buildAxSection th0 th axSec = case axSec of
  AxAssertions (AssertionsSection props) ->
    foldM (addPropFact th0 FactKindAssertion) th props
  AxFacts (FactsSection props) ->
    foldM (addPropFact th0 FactKindFact) th props
  AxMetafacts (MetafactsSection props) ->
    foldM (addPropFact th0 FactKindMetafactsFact) th props

addPropFact :: Theory -> FactKind -> Theory -> PropExprInclVars -> Either BuildError Theory
addPropFact th0 fk th prop = do
  let ctx = emptyVarContext
      sourceCtx = propSourceContext prop
      (PropExprInclVars _ _ vars _) = prop
  (resolvedExpr, _ctx') <- resolvePropExprInclVars th0 ctx prop

  freeVars <- mapM (toResolvedVarDecl th0) vars

  case typeCheckResolvedExpr resolvedExpr of
    Left typeErr -> Left (sourceCtx ++ "Type error in " ++ show fk ++ ": " ++ typeErr)
    Right _ -> Right ()

  case validateAllTermPairs resolvedExpr of
    Left opErr -> Left (sourceCtx ++ "Operation error in " ++ show fk ++ ": " ++ opErr)
    Right _ -> Right ()

  case validateFactBody fk resolvedExpr of
    Left factErr -> Left (sourceCtx ++ factErr)
    Right _ -> Right ()

  let fact = Fact
        { factKind      = fk
        , factPropExpr  = Just resolvedExpr
        , factMereoExpr = Nothing
        , factFreeVars  = freeVars
        }
  let th' = markTheoryPropExprUsage th prop
  return (th' { theoryFacts = theoryFacts th' ++ [fact] })

-- Helper to convert AST VarDecl to ResolvedVarDecl
toResolvedVarDecl :: Theory -> VarDecl -> Either BuildError ResolvedVarDecl
toResolvedVarDecl th (VarDecl name op sortExpr) = do
  s <- lookupSortByExpr th sortExpr
  return $ ResolvedVarDecl name (varKindFromOpAndSort (op == "⊆") s) s

propSourceContext :: PropExprInclVars -> String
propSourceContext (PropExprInclVars line col _ _) =
  if line > 0 && col > 0
    then "At line " ++ show line ++ ", column " ++ show col ++ ": "
    else ""

markTheorySortExprUsage :: Theory -> SortExpr -> Theory
markTheorySortExprUsage th sexpr =
  let tok = sortConstant (sortRef sexpr)
  in th
      { theoryUsesDomain = theoryUsesDomain th || tok == "𝔻"
      , theoryUsesProp   = theoryUsesProp th   || tok == "ℙ" || tok == "Prop"
      }

markTheoryPropExprUsage :: Theory -> PropExprInclVars -> Theory
markTheoryPropExprUsage th (PropExprInclVars _ _ vars expr) =
  let thWithVars = foldl (\acc v -> markTheorySortExprUsage acc (varSort v)) th vars
  in if propExprUsesLogicalConnective expr
      then thWithVars { theoryUsesProp = True }
      else thWithVars

propExprUsesLogicalConnective :: PropExpr -> Bool
propExprUsesLogicalConnective (PropExpr left rests) =
  (not . null) rests || rightImplUsesLogicalConnective left

rightImplUsesLogicalConnective :: RightImpl -> Bool
rightImplUsesLogicalConnective (RightImpl li mRight) =
  leftImplUsesLogicalConnective li || case mRight of
    Nothing -> False
    Just _  -> True

leftImplUsesLogicalConnective :: LeftImpl -> Bool
leftImplUsesLogicalConnective (LeftImpl d rests) =
  disjUsesLogicalConnective d || (not . null) rests

disjUsesLogicalConnective :: Disj -> Bool
disjUsesLogicalConnective (Disj c rests) =
  conjUsesLogicalConnective c || (not . null) rests

conjUsesLogicalConnective :: Conj -> Bool
conjUsesLogicalConnective (Conj n rests) =
  negUsesLogicalConnective n || (not . null) rests

negUsesLogicalConnective :: Neg -> Bool
negUsesLogicalConnective (NegNot _)   = True
negUsesLogicalConnective (NegChild q) = quantifiedUsesLogicalConnective q

quantifiedUsesLogicalConnective :: Quantified -> Bool
quantifiedUsesLogicalConnective (Quantified qs _) = not (null qs)

-- ---------------------------------------------------------------------------
-- Theory skeleton construction
-- ---------------------------------------------------------------------------

createTheory :: Maybe Theory -> String -> Bool -> Theory
createTheory parentMaybe name isRefl =
  let fqn = case parentMaybe of
              Nothing  -> name
              Just par -> (if theoryFullyQualifiedName par == "" then "" else theoryFullyQualifiedName par ++ ".") ++ name

      closestRefl = case parentMaybe of
        Nothing  -> Nothing
        Just par -> if isRefl
                    then Just th
                    else theoryClosestReflectionAncestor par

      th = Theory
        { theoryParent                       = parentMaybe
        , theoryName                         = name
        , theoryFullyQualifiedName           = fqn
        , theoryReflection                   = isRefl
        , theoryUsesDomain                   = False
        , theoryUsesProp                     = False
        , theoryClosestReflectionAncestor    = closestRefl
        , theorySubtheories                  = []
        , theoryObjects                      = builtins
        , theoryObjectsByName                = builtinsByName
        , theoryFacts                        = builtinFacts
        , theoryUniverse                     = universe
        , theoryDomain                       = domain
        , theoryProp                         = prop
        , theoryTruth                        = truth
        , theoryFalsity                      = falsity
        , theorySum                          = sumF
        , theoryProd                         = prodF
        , theoryDiff                         = diffF
        , theoryRevDiff                      = revDiffF
        , theorySymDiff                      = symDiffF
        , theoryUserAbbrevDefs               = []
        }

      universe = mkSort th SortKindUniverse "𝕌" InEveryTheory
      domain   = mkSort th SortKindDomain   "𝔻" InEveryTheory
      prop     = mkSort th SortKindProp     "ℙ" InEveryTheory

      -- ⊤ and ⊥ are keyword aliases for the ℙ-sort bounds.
      -- They are registered under their keyword names so that source-level
      -- lookups for "⊤" / "⊥" succeed, and their 'mereoAlias' field causes
      -- 'resolveEntityAlias' to dereference to the canonical sort-limit entity.
      -- No separate equality fact is needed; the alias IS the relation.
      truth   = (mkMereo th MereologicalEntityKindProposition "⊤" prop InEveryTheory)
                  { mereoAlias = Just (EntityMereological (sortMin prop)) }
      falsity = (mkMereo th MereologicalEntityKindProposition "⊥" prop InEveryTheory)
                  { mereoAlias = Just (EntityMereological (sortMax prop)) }

      mkBinSOL sym = mkMereoOperation th sym [universe, universe] universe InEveryTheory

      sumF     = mkBinSOL "+"
      prodF    = mkBinSOL "×"
      diffF    = mkBinSOL "-"
      revDiffF = mkBinSOL "⇒"
      symDiffF = mkBinSOL "∸"

      builtins = map EntityMereological [truth, falsity]
              ++ map EntityFunction [sumF, prodF, diffF, revDiffF, symDiffF]

      builtinsByName = Map.fromListWith (++)
        [ (entityName e, [e]) | e <- builtins ]

      builtinFacts = []
        -- The ⊤ = ℙ_Min and ⊥ = ℙ_Max relationships are encoded directly
        -- via 'mereoAlias' on the truth/falsity entities; no equality fact
        -- is needed.

  in th


-- ---------------------------------------------------------------------------
-- Smart constructors for IR entities
-- ---------------------------------------------------------------------------

mkSort :: Theory -> EntityKind -> String -> Origin -> Sort
mkSort th k nm orig =
  let s = Sort
        { sortKind             = k
        , sortTheory           = th
        , sortOrigin           = orig
        , sortMin              = sMin
        , sortMax              = sMax
        , sortName             = nm
        , sortComponentSorts   = []
        , sortAssociatedEntity = Nothing
        , sortReflectedFrom    = Nothing
        , sortRelationship     = NotRelational
        , sortParent           = Nothing
        }
      sMin = MereologicalObject
        { mereoKind          = MereologicalEntityKindLowerLimitForSort
        , mereoOrigin        = orig
        , mereoTheory        = th
        , mereoName          = NC.sortMin nm
        , mereoSort          = s
        , mereoLimitForSort  = Just s
        , mereoReflectedFrom = Nothing
        , mereoAlias         = Nothing
        }
      sMax = MereologicalObject
        { mereoKind          = MereologicalEntityKindUpperLimitForSort
        , mereoOrigin        = orig
        , mereoTheory        = th
        , mereoName          = NC.sortMax nm
        , mereoSort          = s
        , mereoLimitForSort  = Just s
        , mereoReflectedFrom = Nothing
        , mereoAlias         = Nothing
        }
  in s

mkMereo :: Theory -> EntityKind -> String -> Sort -> Origin -> MereologicalObject
mkMereo th k nm s orig = MereologicalObject
  { mereoKind          = k
  , mereoOrigin        = orig
  , mereoTheory        = th
  , mereoName          = nm
  , mereoSort          = s
  , mereoLimitForSort  = Nothing
  , mereoReflectedFrom = Nothing
  , mereoAlias         = Nothing
  }

mkSOLFunction :: Theory -> String -> EntityKind -> [Sort] -> Sort -> Origin -> Function
mkSOLFunction th nm k argSorts resSort orig = Function
  { funcKind          = k
  , funcOrigin        = orig
  , funcTheory        = th
  , funcName          = nm
  , funcArgSorts      = argSorts
  , funcResSort       = resSort
  , funcResObject     = Just (mkMereo th MereologicalEntityKindResultOfSOLFunction (NC.funRes nm) resSort orig)
  , funcArgObjects    = zipWith (\s i -> mkMereo th MereologicalEntityKindArgumentOfSOLFunction
                                          (NC.funArgN nm i) s orig) argSorts [1..]
  , funcDomain        = Nothing
  , funcArgument      = Nothing
  , funcDirectImage   = Nothing
  , funcInverseImage  = Nothing
  , funcReflectedFrom = Nothing
  }

mkMereoOperation :: Theory -> String -> [Sort] -> Sort -> Origin -> Function
mkMereoOperation th nm argSorts resSort orig = Function
  { funcKind          = FunctionKindMereologicalOperation
  , funcOrigin        = orig
  , funcTheory        = th
  , funcName          = nm
  , funcArgSorts      = argSorts
  , funcResSort       = resSort
  , funcResObject     = Nothing
  , funcArgObjects    = []
  , funcDomain        = Nothing
  , funcArgument      = Nothing
  , funcDirectImage   = Nothing
  , funcInverseImage  = Nothing
  , funcReflectedFrom = Nothing
  }

mkFOLFunction :: Theory -> String -> [Sort] -> Sort -> Origin
              -> (Function, Sort, Function, Function, Function)
mkFOLFunction th nm argSorts resSort orig =
  let auxOrig = FromFunction
      f0 = mkSOLFunction th nm FunctionKindFOLFunctionFromTheory argSorts resSort orig
      domSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = auxOrig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (NC.sortMin (NC.funDom nm)) domSort auxOrig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (NC.sortMax (NC.funDom nm)) domSort auxOrig
        , sortName             = NC.funDom nm
        , sortComponentSorts   = argSorts
        , sortAssociatedEntity = Just (EntityFunction f)
        , sortReflectedFrom    = Nothing
        }
      domArg = mkMereo th MereologicalEntityKindArgumentOfSOLFunction (NC.funArg nm) domSort auxOrig
      dirImg = mkSOLFunction th (NC.funDirImg nm) FunctionKindDirectImageFunction [domSort] resSort auxOrig
      invImg = mkSOLFunction th (NC.funInvImg nm) FunctionKindInverseImageFunction [resSort] domSort auxOrig
      f = f0 { funcDomain      = Just domSort
             , funcArgument    = Just domArg
             , funcDirectImage  = Just dirImg
             , funcInverseImage = Just invImg
             }
      inv0 = mkSOLFunction th (NC.funInv nm) FunctionKindFOLFunctionFromTheory [resSort] domSort auxOrig
      invDomSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = auxOrig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (NC.sortMin (NC.funInvDom nm)) invDomSort auxOrig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (NC.sortMax (NC.funInvDom nm)) invDomSort auxOrig
        , sortName             = NC.funInvDom nm
        , sortComponentSorts   = [resSort]
        , sortAssociatedEntity = Just (EntityFunction invFn)
        , sortReflectedFrom    = Nothing
        }
      invArg = mkMereo th MereologicalEntityKindArgumentOfSOLFunction (NC.funInvArg nm) invDomSort auxOrig
      invFn = inv0 { funcDomain   = Just invDomSort
                   , funcArgument = Just invArg
                   }
  in (f, domSort, invFn, dirImg, invImg)

mkSortLimitFact :: MereologicalObject -> String -> MereologicalObject -> Fact
mkSortLimitFact l op r = Fact
  { factKind      = FactKindSortLimitation
  , factPropExpr  = Just (twoTermPropExpr l op r)
  , factMereoExpr = Nothing
  , factFreeVars  = []
  }

twoTermPropExpr :: MereologicalObject -> String -> MereologicalObject -> ResolvedPropExpr
twoTermPropExpr l op r =
  ResolvedPropBicond
    (ResolvedRightImpl
      (ResolvedLeftImpl
        (ResolvedDisj
          (ResolvedConj
            (ResolvedNegChild
              (ResolvedQuantified []
                (ResolvedAtomicTermPair
                  (ResolvedTermPair
                    (atomicTerm l) [rft] (mereoExprType l)))))
            [])
          [])
        [])
      Nothing)
    []
  where
    rft = ResolvedRelationFollowedByTerm [] op Nothing (atomicTerm r)
    atomicTerm mo = ResolvedTerm
      (ResolvedFactor
        (ResolvedBTAtomic (ResolvedConstantRef
          { resolvedConstRefName  = mereoName mo
          , resolvedConstEntity   = EntityMereological mo
          , resolvedConstType     = mereoExprType mo
          }))
        []
        (mereoExprType mo))
      []
      (mereoExprType mo)
    mereoExprType mo = case mereoKind mo of
      MereologicalEntityKindIndividual -> IndividualClass
      MereologicalEntityKindSet -> RelationClass 1
      MereologicalEntityKindProposition -> PropositionClass
      _ -> OtherMereologicalClass

addEntityToTh :: Theory -> Entity -> Theory
addEntityToTh th e =
  th { theoryObjects      = theoryObjects th ++ [e]
     , theoryObjectsByName = Map.insertWith (++) (entityName e) [e]
                               (theoryObjectsByName th)
     }

addFactToTh :: Theory -> Fact -> Theory
addFactToTh th f = th { theoryFacts = theoryFacts th ++ [f] }

relateSortToUniverse :: Theory -> Sort -> Theory
relateSortToUniverse th s
  | sortKind s == SortKindUniverse = th
  | otherwise =
      let u = theoryUniverse th
      in addFactToTh (addFactToTh th
           (mkSortLimitFact (sortMin u) "≤" (sortMin s)))
           (mkSortLimitFact (sortMax s) "≤" (sortMax u))

relateSortToProp :: Theory -> Sort -> Theory
relateSortToProp th s
  | sortKind s == SortKindUniverse = th
  | sortKind s == SortKindProp     = th
  | otherwise = addFactToTh th (mkSortLimitFact (sortMax (theoryProp th)) "≤" (sortMin s))

addSortToTh :: Theory -> Sort -> Theory
addSortToTh th s =
  let th1 = addEntityToTh th  (EntitySort s)
      th2 = addEntityToTh th1 (EntityMereological (sortMin s))
      th3 = addEntityToTh th2 (EntityMereological (sortMax s))
      th4 = relateSortToProp    th3 s
      th5 = relateSortToUniverse th4 s
  in th5

mkRelatedSort :: Theory -> String -> String -> Sort -> Sort
mkRelatedSort th rel nm parentS =
  let relationship = case rel of
        "subsort"     -> SubSort
        "quotient"    -> Quotient
        "subquotient" -> SubQuotient
        _             -> NotRelational
  in (mkSort th SortKindFromSignature nm FromSignature)
       { sortRelationship = relationship
       , sortParent       = Just parentS
       }

relationalSortFacts :: Theory -> String -> Sort -> Sort -> Theory
relationalSortFacts th rel newS parentS = case rel of
  "subsort" ->
    addFactToTh (addFactToTh th
      (mkSortLimitFact (sortMin newS) "=" (sortMin parentS)))
      (mkSortLimitFact (sortMax newS) "≤" (sortMax parentS))
  "quotient" ->
    addFactToTh (addFactToTh th
      (mkSortLimitFact (sortMin parentS) "≤" (sortMin newS)))
      (mkSortLimitFact (sortMax newS) "=" (sortMax parentS))
  "subquotient" ->
    addFactToTh (addFactToTh th
      (mkSortLimitFact (sortMin parentS) "≤" (sortMin newS)))
      (mkSortLimitFact (sortMax newS) "≤" (sortMax parentS))
  _ -> th

mkRelation :: Theory -> String -> [Sort] -> Origin -> Relation
mkRelation th nm argSorts orig =
  let domSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = orig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (NC.sortMin (NC.funDom nm)) domSort orig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (NC.sortMax (NC.funDom nm)) domSort orig
        , sortName             = NC.funDom nm
        , sortComponentSorts   = argSorts
        , sortAssociatedEntity = Just (EntityRelation rel)
        , sortReflectedFrom    = Nothing
        }
      domArg   = mkMereo th MereologicalEntityKindIndividual (NC.funArg nm) domSort orig
      assocSet = mkMereo th MereologicalEntityKindSet        (NC.funSet nm) (head argSorts) orig
      rel = Relation
        { relOrigin        = orig
        , relKind          = MereologicalEntityKindSet
        , relTheory        = th
        , relName          = nm
        , relArgSorts      = argSorts
        , relDomain        = domSort
        , relArgObjects    = zipWith (\s i -> mkMereo th MereologicalEntityKindArgumentOfSOLFunction
                                              (NC.funArgN nm i) s orig) argSorts [1..]
        , relArgument      = domArg
        , relAssociatedSet = assocSet
        , relReflectedFrom = Nothing
        }
  in rel

-- ---------------------------------------------------------------------------
-- Reflection: entity kind transformation
-- ---------------------------------------------------------------------------

reflectEntity :: Entity -> Entity
reflectEntity (EntityFunction f) =
  EntityFunction (f { funcKind          = FunctionKindFOLFunctionFromReflection
                    , funcOrigin        = FromReflection
                    , funcReflectedFrom = Just (funcTheory f) })
reflectEntity (EntitySort s) =
  EntitySort (s { sortKind          = SortKindFromReflection
                , sortOrigin        = FromReflection
                , sortReflectedFrom = Just (sortTheory s)
                , sortRelationship  = NotRelational
                , sortParent        = Nothing
                })
reflectEntity (EntityMereological m) =
  EntityMereological (m { mereoKind           = MereologicalEntityKindIndividual
                        , mereoOrigin         = FromReflection
                        , mereoReflectedFrom  = Just (mereoTheory m) })
reflectEntity (EntityRelation r) =
  EntityRelation (r { relOrigin        = FromReflection
                    , relReflectedFrom = Just (relTheory r) })
reflectEntity e = e

-- | After reflection, patch all sort references inside an entity to use the
-- qualified name (i.e. prefix each sort name with @subName ++ "."@).
-- This ensures that sort fields point to the reflected (renamed) sorts rather
-- than the originals.
qualifySortRefs :: String -> Entity -> Entity
qualifySortRefs subName (EntitySort s) =
  EntitySort (s { sortMin = qualMereo (sortMin s)
                , sortMax = qualMereo (sortMax s) })
  where qualMereo m = m { mereoName = subName ++ "." ++ mereoName m }
qualifySortRefs subName (EntityFunction f) =
  EntityFunction (f { funcArgSorts = map qualSort (funcArgSorts f)
                    , funcResSort  = qualSort (funcResSort f) })
  where qualSort s = s { sortName = subName ++ "." ++ sortName s }
qualifySortRefs subName (EntityMereological m) =
  EntityMereological (m { mereoSort        = qualSort (mereoSort m)
                        , mereoLimitForSort = fmap qualSort (mereoLimitForSort m) })
  where qualSort s = s { sortName = subName ++ "." ++ sortName s }
qualifySortRefs _ e = e

-- | Patch the primary name field of an entity.  Used when a reflected entity
-- enters the parent theory's object list under its qualified name.
renameEntity :: String -> Entity -> Entity
renameEntity nm (EntityMereological m) = EntityMereological (m { mereoName = nm })
renameEntity nm (EntitySort s)         = EntitySort         (s { sortName  = nm })
renameEntity nm (EntityFunction f)     = EntityFunction     (f { funcName  = nm })
renameEntity nm (EntityRelation r)     = EntityRelation     (r { relName   = nm })
renameEntity _  e                      = e

-- ---------------------------------------------------------------------------
-- Subtheory propagation
-- ---------------------------------------------------------------------------

propagateSubtheory :: Theory -> String -> Bool -> Bool -> Theory -> Either BuildError Theory
propagateSubtheory parentTh subName isImplicit isReflection subTh =
  foldM addEntry parentTh (Map.toList (theoryObjectsByName subTh))
  where
    addEntry th (name, entities) = do
      let transformed = if isReflection
                          then map (qualifySortRefs subName . reflectEntity) entities
                          else entities
          qualifiedName = if null subName then name else subName ++ "." ++ name
          localToSub = [e | e <- transformed, theoryFullyQualifiedName (entityTheory e) == theoryFullyQualifiedName subTh]

      -- Update the name map (existing behaviour).
      let th1 = foldl (\t e -> addEntityToParent t qualifiedName e) th transformed

      -- Also register in theoryObjects so the pipeline sees these entities:
      --   Reflection subtheories are skipped in block generation, so their
      --   reflected entities must be owned by the parent under a qualified name.
      --   Implicit subtheory entities enter under their original name; dedup
      --   ensures an entity shared by multiple implicit subtheories appears once.
      let th2
            | isReflection =
                let renamed = map (renameEntity qualifiedName) localToSub
                in th1 { theoryObjects = theoryObjects th1 ++ renamed }
            | isImplicit && not (all isInternalEntity transformed) && not (null localToSub) =
                let existingNames = map entityName (theoryObjects th1)
                    fresh = filter (\e -> entityName e `notElem` existingNames) localToSub
                in th1 { theoryObjects = theoryObjects th1 ++ fresh }
            | otherwise = th1

      if isImplicit && not (all isInternalEntity transformed) && not (null transformed)
        then if not (null localToSub)
               then foldM (addUnqualified name qualifiedName) th2 localToSub
               else Right $ foldl (\t e -> addEntityToParent t name e) th2 transformed
        else Right th2

termFromEntityWithName :: String -> Entity -> ResolvedTerm
termFromEntityWithName displayName entity =
  let constRef = ResolvedConstantRef
        { resolvedConstRefName = displayName
        , resolvedConstEntity  = entity
        , resolvedConstType    = entityToExprType entity
        }
      factor = ResolvedFactor (ResolvedBTAtomic constRef) [] (entityToExprType entity)
  in ResolvedTerm factor [] (entityToExprType entity)

termFromEntity :: Entity -> ResolvedTerm
termFromEntity e = termFromEntityWithName (entityName e) e

addMergeEqualityFact
  :: Theory
  -> String
  -> Entity
  -> String
  -> Entity
  -> Theory
addMergeEqualityFact th lhsName lhsEntity rhsName rhsEntity =
  let leftTerm  = termFromEntityWithName lhsName  lhsEntity
      rightTerm = termFromEntityWithName rhsName rhsEntity
      relation  = ResolvedRelationFollowedByTerm [] "=" Nothing rightTerm
      termPair  = ResolvedTermPair leftTerm [relation] OtherMereologicalClass
      atomicProp = ResolvedAtomicTermPair termPair
      quantified = ResolvedQuantified [] atomicProp
      neg       = ResolvedNegChild quantified
      conj      = ResolvedConj neg []
      disj      = ResolvedDisj conj []
      leftImpl  = ResolvedLeftImpl disj []
      rightImpl = ResolvedRightImpl leftImpl Nothing
      (kind, mereo) = case lhsEntity of
        EntityFunction _ ->
          (factKindImplicitMergeFunction, Nothing)
        _ ->
          (factKindImplicitMerge, Just (MAbbrevApp "WrapMetafact"
            [ MVar "𝕌_Min"
            , MSymDiff (MVar lhsName) (MVar rhsName)
            ]))
  in addFactToTh th (Fact
        { factKind      = kind
        , factPropExpr  = Just (ResolvedPropBicond rightImpl [])
        , factMereoExpr = mereo
        , factFreeVars  = []
        })

addMergeEqualityFacts
  :: Theory
  -> String
  -> Entity
  -> String
  -> Entity
  -> Theory
addMergeEqualityFacts th lhsName lhsEntity rhsName rhsEntity =
  foldl (\acc (l, r) -> addMergeEqualityFact acc l lhsEntity r rhsEntity) th mergePairs
  where
    rhsWithLeaf :: String -> String
    rhsWithLeaf leaf =
      case break (== '.') (reverse rhsName) of
        (_, "")      -> leaf
        (_, revRest) -> reverse revRest ++ leaf

    mergePairs
      | isSort lhsEntity =
          [ (NC.sortMin lhsName, rhsWithLeaf (NC.sortMin lhsName))
          , (NC.sortMax lhsName, rhsWithLeaf (NC.sortMax lhsName))
          ]
      | otherwise = case lhsName of
          "⊤" -> [(NC.sortMin "ℙ", rhsWithLeaf (NC.sortMin "ℙ"))]
          "⊥" -> [(NC.sortMax "ℙ", rhsWithLeaf (NC.sortMax "ℙ"))]
          _   -> [(lhsName, rhsName)]

    isSort (EntitySort _) = True
    isSort _ = False

builtInSortNames :: [String]
builtInSortNames = ["𝔻", "ℙ", "𝕌", "⊤", "⊥"]

isBuiltInSort :: String -> Bool
isBuiltInSort n = n `elem` builtInSortNames

isSortLimit :: Entity -> Bool
isSortLimit (EntityMereological m) = case mereoLimitForSort m of
  Just _  -> True
  Nothing -> False
isSortLimit _ = False

addUnqualified :: String -> String -> Theory -> Entity -> Either BuildError Theory
addUnqualified name qualifiedName th entity
  | isSortLimit entity = Right th
  | name == "⊤" = Right th
  | name == "⊥" = Right th
  | isBuiltInSort name =
      case ( Map.lookup name      (theoryObjectsByName th)
           , Map.lookup qualifiedName (theoryObjectsByName th) ) of
        (Just (parentEntity:_), Just (subEntity:_)) ->
          Right $ addMergeEqualityFacts th name parentEntity qualifiedName subEntity
        _ -> Right th
  | Nothing <- Map.lookup name (theoryObjectsByName th) =
      let canonical = createCanonicalEntity th entity
          th1       = addEntityToParent th name canonical
      in Right $ addMergeEqualityFacts th1 name canonical qualifiedName entity
  | Just (canonical : _) <- Map.lookup name (theoryObjectsByName th) =
      if entitiesCompatible canonical entity
        then Right $ addMergeEqualityFacts th name canonical qualifiedName entity
        else Left $ "Name conflict: '" ++ name
               ++ "' is defined in multiple implicit subtheories with incompatible signatures"
  | otherwise = Right th

createCanonicalEntity :: Theory -> Entity -> Entity
createCanonicalEntity parentTh (EntitySort s) =
  EntitySort s { sortTheory       = parentTh
               , sortOrigin       = FromSubtheory
               , sortReflectedFrom = Nothing
               }
createCanonicalEntity parentTh (EntityFunction f) =
  EntityFunction f { funcTheory       = parentTh
                   , funcOrigin       = FromSubtheory
                   , funcReflectedFrom = Nothing
                   }
createCanonicalEntity parentTh (EntityMereological m) =
  EntityMereological m { mereoTheory       = parentTh
                        , mereoOrigin       = FromSubtheory
                        , mereoReflectedFrom = Nothing
                        }
createCanonicalEntity parentTh (EntityRelation r) =
  EntityRelation r { relTheory       = parentTh
                   , relOrigin       = FromSubtheory
                   , relReflectedFrom = Nothing
                   }
createCanonicalEntity _ e = e

isInternalEntity :: Entity -> Bool
isInternalEntity (EntitySort s) =
  sortOrigin s == FromFunction || sortOrigin s == FromRelation
isInternalEntity (EntityFunction f) =
  funcOrigin f == FromFunction || funcOrigin f == FromRelation
isInternalEntity (EntityRelation r) =
  relOrigin r == FromFunction || relOrigin r == FromRelation
isInternalEntity (EntityMereological m) =
  mereoOrigin m == FromFunction || mereoOrigin m == FromRelation
isInternalEntity _ = False

entitiesCompatible :: Entity -> Entity -> Bool
entitiesCompatible (EntitySort s1) (EntitySort s2) =
  sortName s1 == sortName s2
entitiesCompatible (EntityFunction f1) (EntityFunction f2) =
  length (funcArgSorts f1) == length (funcArgSorts f2) &&
  sortName (funcResSort f1) == sortName (funcResSort f2) &&
  and (zipWith (\a b -> sortName a == sortName b) (funcArgSorts f1) (funcArgSorts f2))
entitiesCompatible (EntityRelation r1) (EntityRelation r2) =
  length (relArgSorts r1) == length (relArgSorts r2) &&
  and (zipWith (\a b -> sortName a == sortName b) (relArgSorts r1) (relArgSorts r2))
entitiesCompatible (EntityMereological m1) (EntityMereological m2) =
  mereoKind m1 == mereoKind m2 &&
  sortName (mereoSort m1) == sortName (mereoSort m2)
entitiesCompatible _ _ = False

addEntityToParent :: Theory -> String -> Entity -> Theory
addEntityToParent th name entity =
  th { theoryObjectsByName = Map.insertWith (++) name [entity] (theoryObjectsByName th) }

-- ---------------------------------------------------------------------------
-- Mereological translations (pass 4)
-- ---------------------------------------------------------------------------

mereoOpPrefix :: Theory -> String
mereoOpPrefix th = case theoryClosestReflectionAncestor th of
  Just anc -> theoryFullyQualifiedName anc ++ "."
  Nothing  -> ""

mereologicalTranslation :: Theory -> Fact -> [Fact]
mereologicalTranslation th fact = case factKind fact of
  FactKindFact ->
    let origExpr = fromJust (factPropExpr fact)
    in [ Fact { factKind      = factKindMereoOfFact
              , factPropExpr  = Nothing
              , factMereoExpr = Just (wrapAsFact th (factFreeVars fact) origExpr)
              , factFreeVars  = factFreeVars fact
              } ]
  FactKindAssertion ->
    let origExpr = fromJust (factPropExpr fact)
    in [ Fact { factKind      = factKindMereoOfAssertion
              , factPropExpr  = Nothing
              , factMereoExpr = Just (wrapAsAssertion th (factFreeVars fact) origExpr)
              , factFreeVars  = factFreeVars fact
              } ]
  FactKindMetafactsFact ->
    let origExpr = fromJust (factPropExpr fact)
    in [ Fact { factKind      = factKindMereoOfMetafact
              , factPropExpr  = Nothing
              , factMereoExpr = Just (wrapAsMetafact th (factFreeVars fact) origExpr)
              , factFreeVars  = factFreeVars fact
              } ]
  _ -> []

-- ---------------------------------------------------------------------------
-- Mereological wrappers
-- ---------------------------------------------------------------------------

wrapFreeVarsMereo :: [ResolvedVarDecl] -> MereoExpr -> MereoExpr
wrapFreeVarsMereo [] body = body
wrapFreeVarsMereo (vd:rest) body =
  let varN   = resolvedVarName vd
      sn     = sortName (resolvedVarSort vd)
      lo     = MVar (NC.sortMin sn)
      hi     = MVar (NC.sortMax sn)
  in MBoundedSum varN lo hi (wrapFreeVarsMereo rest body)

wrapAsFact :: Theory -> [ResolvedVarDecl] -> ResolvedPropExpr -> MereoExpr
wrapAsFact th freeVars expr =
  let body = wrapFreeVarsMereo freeVars (propExprToMereo (translatePropExpr th expr))
      pMin = MVar (NC.sortMin (sortName (theoryProp th)))
  in MAbbrevApp "WrapFact" [pMin, body]

wrapAsAssertion :: Theory -> [ResolvedVarDecl] -> ResolvedPropExpr -> MereoExpr
wrapAsAssertion th freeVars expr =
  let pMin = MVar (NC.sortMin (sortName (theoryProp th)))
      pMax = MVar (NC.sortMax (sortName (theoryProp th)))
      -- Assertions may contain '¬'; pass pMax as the negation bottom so that
      -- '¬A' translates to 'A ⇒ ℙ_Max' (propositional falsehood).
      body = wrapFreeVarsMereo freeVars (propExprToMereoNb pMax (translatePropExpr th expr))
  in MAbbrevApp "WrapAssertion" [pMin, pMax, body]

wrapAsMetafact :: Theory -> [ResolvedVarDecl] -> ResolvedPropExpr -> MereoExpr
wrapAsMetafact th freeVars expr =
  let body = wrapFreeVarsMereo freeVars (propExprToMereo (translatePropExpr th expr))
      uMin = MVar (NC.sortMin (sortName (theoryUniverse th)))
  in MAbbrevApp "WrapMetafact" [uMin, body]

-- ---------------------------------------------------------------------------
-- ResolvedPropExpr → MereoExpr conversion
--
-- Expects a ResolvedPropExpr whose operators have already been swapped to
-- their mereological equivalents by translatePropExpr (i.e. + × - ⇒ ∸).
--
-- The 'Nb' variants take an explicit "negation bottom" ('nb'): the MereoExpr
-- that stands for propositional falsehood.  'negToMereoNb' translates '¬A'
-- as 'MRevDiff A nb'.
--
-- Assertions pass 'pMax' (ℙ_Max) as 'nb' so that '¬A' correctly becomes
-- 'A ⇒ ℙ_Max' (i.e. A → ⊥).
-- Facts and metafacts — which should not contain negation — use 'MZero'
-- via the plain wrappers, preserving the old safe-default behaviour.
-- ---------------------------------------------------------------------------

propExprToMereoNb :: MereoExpr -> ResolvedPropExpr -> MereoExpr
propExprToMereoNb nb (ResolvedPropBicond left rests) =
  foldl MSymDiff (rightImplToMereoNb nb left)
                 (map (rightImplToMereoNb nb . resolvedPropRestRight) rests)

rightImplToMereoNb :: MereoExpr -> ResolvedRightImpl -> MereoExpr
rightImplToMereoNb nb (ResolvedRightImpl left Nothing) = leftImplToMereoNb nb left
rightImplToMereoNb nb (ResolvedRightImpl left (Just (_, right))) =
  MRevDiff (leftImplToMereoNb nb left) (rightImplToMereoNb nb right)

leftImplToMereoNb :: MereoExpr -> ResolvedLeftImpl -> MereoExpr
leftImplToMereoNb nb (ResolvedLeftImpl left []) = disjToMereoNb nb left
leftImplToMereoNb nb (ResolvedLeftImpl left rests) =
  foldl MDiff (disjToMereoNb nb left) (map (disjToMereoNb nb . resolvedLirRight) rests)

disjToMereoNb :: MereoExpr -> ResolvedDisj -> MereoExpr
disjToMereoNb nb (ResolvedDisj left []) = conjToMereoNb nb left
disjToMereoNb nb (ResolvedDisj left rests) =
  foldl MProd (conjToMereoNb nb left) (map (conjToMereoNb nb . resolvedDisjRestRight) rests)

conjToMereoNb :: MereoExpr -> ResolvedConj -> MereoExpr
conjToMereoNb nb (ResolvedConj left []) = negToMereoNb nb left
conjToMereoNb nb (ResolvedConj left rests) =
  foldl MSum (negToMereoNb nb left) (map (negToMereoNb nb . resolvedConjRestRight) rests)

-- | Translate a negation node.
-- 'ResolvedNegNot inner' becomes 'inner ⇒ nb' (mereological implication to
-- the negation bottom).  'ResolvedNegChild' is a non-negated quantified expr.
negToMereoNb :: MereoExpr -> ResolvedNeg -> MereoExpr
negToMereoNb nb (ResolvedNegNot inner) = MRevDiff (negToMereoNb nb inner) nb
negToMereoNb _  (ResolvedNegChild q)  = quantifiedToMereo q

-- | Backward-compat wrappers: use MZero as the negation bottom.
-- Facts and metafacts should not contain negation; MZero is the safe default.
propExprToMereo :: ResolvedPropExpr -> MereoExpr
propExprToMereo = propExprToMereoNb MZero

rightImplToMereo :: ResolvedRightImpl -> MereoExpr
rightImplToMereo = rightImplToMereoNb MZero

leftImplToMereo :: ResolvedLeftImpl -> MereoExpr
leftImplToMereo = leftImplToMereoNb MZero

disjToMereo :: ResolvedDisj -> MereoExpr
disjToMereo = disjToMereoNb MZero

conjToMereo :: ResolvedConj -> MereoExpr
conjToMereo = conjToMereoNb MZero

negToMereo :: ResolvedNeg -> MereoExpr
negToMereo = negToMereoNb MZero

quantifiedToMereo :: ResolvedQuantified -> MereoExpr
quantifiedToMereo (ResolvedQuantified [] atomic) = atomicToMereo atomic
quantifiedToMereo (ResolvedQuantified qs atomic) =
  foldr quantifierToMereo (atomicToMereo atomic) qs

quantifierToMereo :: ResolvedQuantifier -> MereoExpr -> MereoExpr
quantifierToMereo q body =
  let (vd, isExists) = case q of
        ResolvedQForall vd' -> (vd', False)
        ResolvedQExists vd' -> (vd', True)
      varN  = resolvedVarName vd
      sn    = sortName (resolvedVarSort vd)
      lo    = MVar (NC.sortMin sn)
      hi    = MVar (NC.sortMax sn)
      isInd = resolvedVarKind vd == VarKindIndividual
  in if isExists then (if isInd then MProductOfIndividuals varN lo hi body else MBoundedProduct varN lo hi body)
    else (if isInd then MSumOfIndividuals varN lo hi body else MBoundedSum varN lo hi body)

atomicToMereo :: ResolvedAtomicProp -> MereoExpr
atomicToMereo (ResolvedAtomicConstant ref) = MVar (resolvedConstRefName ref)
atomicToMereo (ResolvedAtomicTermPair tp)  = termPairToMereo tp

termPairToMereo :: ResolvedTermPair -> MereoExpr
termPairToMereo (ResolvedTermPair left rights _) =
  foldl applyRelOpToMereo (termToMereo left) rights

applyRelOpToMereo :: MereoExpr -> ResolvedRelationFollowedByTerm -> MereoExpr
applyRelOpToMereo leftExpr rfbt =
  let right = termToMereo (resolvedRFTRight rfbt)
  in case resolvedRFTOp rfbt of
       "+"  -> MSum     leftExpr right
       "×"  -> MProd    leftExpr right
       "-"  -> MDiff    leftExpr right
       "∸"  -> MSymDiff leftExpr right
       "⇒"  -> MRevDiff leftExpr right
       "="  -> MSymDiff leftExpr right      -- = in sort-limit facts translates to ∸
       "≤"  -> MRevDiff leftExpr right      -- ≤ translates to ⇒
       "∪"  -> MSum     leftExpr right
       "∩"  -> MProd    leftExpr right
       _    -> MVar ("unknown:" ++ resolvedRFTOp rfbt)

termToMereo :: ResolvedTerm -> MereoExpr
termToMereo (ResolvedTerm left rests _) =
  foldl applyArithToMereo (factorToMereo left) rests

applyArithToMereo :: MereoExpr -> ResolvedOperationFollowedByFactor -> MereoExpr
applyArithToMereo leftExpr off =
  let right = factorToMereo (resolvedOFFRight off)
  in case resolvedOFFOp off of
       "+"  -> MSum     leftExpr right
       "×"  -> MProd    leftExpr right
       "-"  -> MDiff    leftExpr right    
       "∸"  -> MSymDiff leftExpr right
       "⇒"  -> MRevDiff right leftExpr
       "∪"  -> MSum     leftExpr right
       "∩"  -> MProd    leftExpr right
       _    -> MVar ("unknown:" ++ resolvedOFFOp off)

factorToMereo :: ResolvedFactor -> MereoExpr
factorToMereo (ResolvedFactor base suffixes _) =
  foldl applySuffixToMereo (baseTermToMereo base) suffixes

applySuffixToMereo :: MereoExpr -> ResolvedTermSuffix -> MereoExpr
applySuffixToMereo expr suffix = case suffix of
  ResolvedSuffixDotAttr attr ->
    MVar (flattenMereoName expr ++ "." ++ attr)
  ResolvedSuffixCall args ->
    MAbbrevApp (flattenMereoName expr) (map termToMereo args)
  ResolvedSuffixSpecialOp _ (Just entity) ->
    MVar (entityFullyQualifiedName entity)
  ResolvedSuffixSpecialOp op Nothing ->
    MVar (flattenMereoName expr ++ "_" ++ op)

flattenMereoName :: MereoExpr -> String
flattenMereoName (MVar n) = n
flattenMereoName _        = "_"

baseTermToMereo :: ResolvedBaseTerm -> MereoExpr
baseTermToMereo bt = case bt of
  ResolvedBTAtomic ref ->
    MVar (resolvedConstRefName ref)
  ResolvedBTPropParen expr ->
    propExprToMereo expr
  ResolvedBTTermParen term ->
    termToMereo term
  ResolvedBTSingleton t ->
    termToMereo t
  ResolvedBTEvaluationInTheory eit ->
    propExprToMereo (resolvedEITOperand eit)
  ResolvedBTProjectionToSort pts ->
    MAbbrevApp "ProjectIntoInterval"
      [ termToMereo (resolvedPTOperand pts)
      , MVar (NC.sortMin (sortName (resolvedPTSort pts)))
      , MVar (NC.sortMax (sortName (resolvedPTSort pts)))
      ]
  ResolvedBTProjectionToInterval pti ->
    MAbbrevApp "ProjectIntoInterval"
      [ termToMereo (resolvedPTIOperand pti)
      , termToMereo (resolvedPTILo pti)
      , termToMereo (resolvedPTIHi pti)
      ]
  ResolvedBTGeneralizedSumOrProduct gsp ->
    let operand = termToMereo (resolvedGSPOperand gsp)
    in case resolvedGSPVar gsp of
         Left vd ->
           let varN  = resolvedVarName vd
               sn    = sortName (resolvedVarSort vd)
               lo    = MVar (NC.sortMin sn)
               hi    = MVar (NC.sortMax sn)
               isInd = resolvedVarKind vd == VarKindIndividual
           in if isInd then MSumOfIndividuals varN lo hi operand else MBoundedSum varN lo hi operand
         Right bareVar ->
           MBoundedSum bareVar MZero MZero operand
  ResolvedBTSetComprehension sc ->
    let vd   = resolvedSCVar sc
        varN = resolvedVarName vd
        sn   = sortName (resolvedVarSort vd)
        lo   = MVar (NC.sortMin sn)
        hi   = MVar (NC.sortMax sn)
        isInd = resolvedVarKind vd == VarKindIndividual
    in if isInd then MSumOfIndividuals varN lo hi (MRevDiff (propExprToMereo (resolvedSCBody sc)) (MVar varN))
      else MBoundedSum varN lo hi (MRevDiff (propExprToMereo (resolvedSCBody sc)) (MVar varN))
  ResolvedBTDescription desc ->
    let vd   = resolvedDescVar desc
        varN = resolvedVarName vd
        sn   = sortName (resolvedVarSort vd)
        lo   = MVar (NC.sortMin sn)
        hi   = MVar (NC.sortMax sn)
        isInd = resolvedVarKind vd == VarKindIndividual
    in if isInd then MSumOfIndividuals varN lo hi (MRevDiff (propExprToMereo (resolvedDescBody desc)) (MVar varN))
      else MBoundedSum varN lo hi (MRevDiff (propExprToMereo (resolvedDescBody desc)) (MVar varN))

translatePropExpr :: Theory -> ResolvedPropExpr -> ResolvedPropExpr
translatePropExpr th (ResolvedPropBicond left rests) =
  let left'  = translateRightImpl th left
      rests' = map (\(ResolvedPropRest _op r) ->
                      ResolvedPropRest (mereoOpPrefix th ++ "∸") (translateRightImpl th r))
                   rests
  in ResolvedPropBicond left' rests'

translateRightImpl :: Theory -> ResolvedRightImpl -> ResolvedRightImpl
translateRightImpl th (ResolvedRightImpl left mbRight) =
  let left' = translateLeftImpl th left
      mbRight' = fmap (\(_op, r) -> (mereoOpPrefix th ++ "⇒", translateRightImpl th r)) mbRight
  in ResolvedRightImpl left' mbRight'

translateLeftImpl :: Theory -> ResolvedLeftImpl -> ResolvedLeftImpl
translateLeftImpl th (ResolvedLeftImpl left rests) =
  let left'  = translateDisj th left
      rests' = map (\(ResolvedLeftImplRest _op d) ->
                      ResolvedLeftImplRest (mereoOpPrefix th ++ "-") (translateDisj th d))
                   rests
  in ResolvedLeftImpl left' rests'

translateDisj :: Theory -> ResolvedDisj -> ResolvedDisj
translateDisj th (ResolvedDisj left rests) =
  let left'  = translateConj th left
      rests' = map (\(ResolvedDisjRest _op c) ->
                      ResolvedDisjRest (mereoOpPrefix th ++ "×") (translateConj th c))
                   rests
  in ResolvedDisj left' rests'

translateConj :: Theory -> ResolvedConj -> ResolvedConj
translateConj th (ResolvedConj left rests) =
  let left'  = translateNeg th left
      rests' = map (\(ResolvedConjRest _op n) ->
                      ResolvedConjRest (mereoOpPrefix th ++ "+") (translateNeg th n))
                   rests
  in ResolvedConj left' rests'

translateNeg :: Theory -> ResolvedNeg -> ResolvedNeg
translateNeg th (ResolvedNegNot inner) = ResolvedNegNot (translateNeg th inner)
translateNeg th (ResolvedNegChild q)   = ResolvedNegChild (translateQuantified th q)

translateQuantified :: Theory -> ResolvedQuantified -> ResolvedQuantified
translateQuantified th (ResolvedQuantified qs atomic) =
  ResolvedQuantified qs (translateAtomicProp th atomic)

translateAtomicProp :: Theory -> ResolvedAtomicProp -> ResolvedAtomicProp
translateAtomicProp th (ResolvedAtomicTermPair tp) =
  ResolvedAtomicTermPair (translateTermPair th tp)
translateAtomicProp _th other = other

translateTermPair :: Theory -> ResolvedTermPair -> ResolvedTermPair
translateTermPair th (ResolvedTermPair left rights ty) =
  let left'   = translateTerm th left
      rights' = map (translateRFT th) rights
  in ResolvedTermPair left' rights' ty

translateRFT :: Theory -> ResolvedRelationFollowedByTerm -> ResolvedRelationFollowedByTerm
translateRFT th (ResolvedRelationFollowedByTerm path op mbSort right) =
  let newOp = case op of
        "="  -> mereoOpPrefix th ++ "∸"
        "∈"  -> mereoOpPrefix th ++ "-"
        "⊆"  -> mereoOpPrefix th ++ "-"
        "≤"  -> mereoOpPrefix th ++ "-"
        _    -> op
  in ResolvedRelationFollowedByTerm path newOp mbSort (translateTerm th right)

translateTerm :: Theory -> ResolvedTerm -> ResolvedTerm
translateTerm th (ResolvedTerm left rights ty) =
  let left'   = translateFactor th left
      rights' = map (\(ResolvedOperationFollowedByFactor p op f) ->
                       ResolvedOperationFollowedByFactor p op (translateFactor th f))
                    rights
  in ResolvedTerm left' rights' ty

translateFactor :: Theory -> ResolvedFactor -> ResolvedFactor
translateFactor th (ResolvedFactor base suffixes ty) =
  ResolvedFactor (translateBaseTerm th base) suffixes ty

translateBaseTerm :: Theory -> ResolvedBaseTerm -> ResolvedBaseTerm
translateBaseTerm th bt = case bt of
  ResolvedBTPropParen inner ->
    ResolvedBTPropParen (translatePropExpr th inner)
  ResolvedBTTermParen term ->
    ResolvedBTTermParen (translateTerm th term)
  ResolvedBTSingleton t ->
    ResolvedBTSingleton (translateTerm th t)
  ResolvedBTEvaluationInTheory (ResolvedEvaluationInTheory path subTh inner) ->
    ResolvedBTEvaluationInTheory
      (ResolvedEvaluationInTheory path subTh (translatePropExpr subTh inner))
  ResolvedBTProjectionToSort (ResolvedProjectionToSort s operand) ->
    ResolvedBTProjectionToSort (ResolvedProjectionToSort s (translateTerm th operand))
  ResolvedBTProjectionToInterval (ResolvedProjectionToInterval lo hi operand) ->
    ResolvedBTProjectionToInterval
      (ResolvedProjectionToInterval (translateTerm th lo)
                                    (translateTerm th hi)
                                    (translateTerm th operand))
  ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct sym var operand) ->
    ResolvedBTGeneralizedSumOrProduct
      (ResolvedGeneralizedSumOrProduct sym var (translateTerm th operand))
  ResolvedBTSetComprehension (ResolvedSetComprehension rvd rbody) ->
    ResolvedBTSetComprehension (ResolvedSetComprehension rvd (translatePropExpr th rbody))
  ResolvedBTDescription (ResolvedDescription rvd rbody) ->
    ResolvedBTDescription (ResolvedDescription rvd (translatePropExpr th rbody))
  ResolvedBTAtomic _ -> bt

-- ---------------------------------------------------------------------------
-- Lookup helpers
-- ---------------------------------------------------------------------------

lookupSort :: Theory -> String -> Either BuildError Sort
lookupSort th nm = case nm of
  "𝕌"    -> Right (theoryUniverse th)
  "𝔻"    -> Right (theoryDomain th)
  "ℙ"    -> Right (theoryProp th)
  "Prop" -> Right (theoryProp th)
  _ -> case Map.lookup nm (theoryObjectsByName th) of
    Just (EntitySort s : _) -> Right s
    _ ->
      case mapMaybe (\sub -> case Map.lookup nm (theoryObjectsByName sub) of
                                Just (EntitySort s : _) -> Just s
                                _                       -> Nothing)
                    (theorySubtheories th) of
        (s:_) -> Right s
        []    -> Left $ "Unknown sort: " ++ nm

lookupFunction :: Theory -> String -> Either BuildError Function
lookupFunction th nm =
  case Map.lookup nm (theoryObjectsByName th) of
    Just (EntityFunction f : _) -> Right f
    _ ->
      case mapMaybe (\sub -> case Map.lookup nm (theoryObjectsByName sub) of
                                Just (EntityFunction f : _) -> Just f
                                _                           -> Nothing)
                    (theorySubtheories th) of
        (f:_) -> Right f
        []    -> Left $ "Unknown function: '" ++ nm ++ "'"

lookupSortByExpr :: Theory -> SortExpr -> Either BuildError Sort
lookupSortByExpr th sexpr = do
  let sr = sortRef sexpr
  th' <- case sortSpecifier sr of
    []    -> Right th
    specs -> findSubtheoryByPath th (map theoryRefName specs)
  case sortHashAttr sr of
    Nothing   -> lookupSort th' (sortConstant sr)
    Just attr -> do
      fn <- lookupFunction th' (sortConstant sr)
      case attr of
        "dom" -> maybe (Left $ "Function '" ++ sortConstant sr ++ "' has no domain sort") Right
                       (funcDomain fn)
        _     -> Left $ "Unknown sort attribute '#" ++ attr ++ "' on '" ++ sortConstant sr ++ "'"

lookupEntity :: Theory -> String -> Either BuildError Entity
lookupEntity th nm =
  case Map.lookup nm (theoryObjectsByName th) of
    Just [e]   -> Right (resolveEntityAlias e)
    Just []    -> Left $ "Unknown reference: '" ++ nm ++ "'"
    Just (_:_) -> Left $ "Ambiguous name: '" ++ nm ++ "'"
    Nothing    -> Left $ "Unknown reference: '" ++ nm ++ "'"

lookupEntityInPath :: Theory -> [String] -> String -> Either BuildError Entity
lookupEntityInPath th [] nm = lookupEntity th nm
lookupEntityInPath th path nm =
  -- Always check the parent theory's map under the fully-qualified name first.
  -- This is essential for reflection subtheories: the reflected entity lives in
  -- the parent under the qualified key, while the subtheory holds the original
  -- (unreflected) entity.  Descending into the subtheory would find the wrong one.
  let qualifiedName = intercalate "." (path ++ [nm])
  in case Map.lookup qualifiedName (theoryObjectsByName th) of
    Just [e]   -> Right (resolveEntityAlias e)
    Just []    -> Left $ "Unknown reference: '" ++ qualifiedName ++ "'"
    Just (_:_) -> Left $ "Ambiguous name: '" ++ qualifiedName ++ "'"
    Nothing    -> do
      subTh <- findSubtheoryByPath th path
      lookupEntity subTh nm

lookupInPath :: Theory -> [String] -> (Theory -> a) -> a
lookupInPath th [] f    = f th
lookupInPath th (p:ps) f =
  case find (\s -> theoryName s == p) (theorySubtheories th) of
    Just sub -> lookupInPath sub ps f
    Nothing  -> f th

findSubtheoryByPath :: Theory -> [String] -> Either BuildError Theory
findSubtheoryByPath th []     = Right th
findSubtheoryByPath th (p:ps) =
  case find (\s -> theoryName s == p) (theorySubtheories th) of
    Just sub -> findSubtheoryByPath sub ps
    Nothing  -> Left $ "Subtheory not found: " ++ p

entityToExprType :: Entity -> ExprType
entityToExprType (EntitySort _) = SortClass
entityToExprType (EntityFunction f) =
  case funcKind f of
    FunctionKindFOLFunctionFromTheory -> FOLFunctionClass (length (funcArgSorts f))
    FunctionKindSOLFunctionFromTheory -> SOLFunctionClass (length (funcArgSorts f))
    FunctionKindUserAbbreviation      -> SOLFunctionClass (length (funcArgSorts f))
    _ -> OtherMereologicalClass
entityToExprType (EntityRelation r)    = RelationClass (length (relArgSorts r))
entityToExprType (EntityMereological m) =
  case mereoKind m of
    MereologicalEntityKindIndividual  ->
      if isUniverseSort (mereoSort m)
      then OtherMereologicalClass
      else IndividualClass
    MereologicalEntityKindSet         -> RelationClass 1
    MereologicalEntityKindProposition -> PropositionClass
    -- Sort-limit objects (ℙ_Min, ℙ_Max) are propositions; limits of other
    -- sorts (e.g. 𝕌_Min) are plain mereological objects.
    MereologicalEntityKindLowerLimitForSort ->
      maybe OtherMereologicalClass
            (\s -> if isPropSort s then PropositionClass else OtherMereologicalClass)
            (mereoLimitForSort m)
    MereologicalEntityKindUpperLimitForSort ->
      maybe OtherMereologicalClass
            (\s -> if isPropSort s then PropositionClass else OtherMereologicalClass)
            (mereoLimitForSort m)
    _ -> OtherMereologicalClass
entityToExprType (EntityTheory _) = TheoryClass

-- ---------------------------------------------------------------------------
-- Name resolution
-- ---------------------------------------------------------------------------

resolvePropExprInclVars
  :: Theory
  -> VarContext
  -> PropExprInclVars
  -> Either BuildError (ResolvedPropExpr, VarContext)
resolvePropExprInclVars th ctx (PropExprInclVars _ _ vars propExprAST) = do
  ctx' <- foldM resolveAndBindVar ctx vars
  resolved <- resolvePropExpr th ctx' propExprAST
  return (resolved, ctx')
  where
    resolveAndBindVar c (VarDecl vid colonOrSubset sexpr) = do
      s <- lookupSortByExpr th sexpr
      let isSet' = colonOrSubset == "⊆"
      if isSet'
        then when (not (firstLetterIsUppercase vid)) $
               Left $ "Free set variable must start with uppercase: " ++ vid
        else when (not (isPropSort s) && not (isUniverseSort s) && firstLetterIsUppercase vid) $
               Left $ "Free individual variable must start with lowercase: " ++ vid
      when ((isPropSort s || isUniverseSort s) && not isSet' && not (firstLetterIsUppercase vid)) $
        Left $ "Proposition/mereological variable must start with uppercase: " ++ vid
      let rvd = ResolvedVarDecl vid (varKindFromOpAndSort isSet' s) s
      return (extendVarContext c rvd)

resolvePropExpr :: Theory -> VarContext -> PropExpr -> Either BuildError ResolvedPropExpr
resolvePropExpr th ctx (PropExpr leftRI rests) = do
  l  <- resolveRightImpl th ctx leftRI
  rs <- mapM (resolvePropExprRest th ctx) rests
  return (ResolvedPropBicond l rs)

resolvePropExprRest :: Theory -> VarContext -> PropExprRest -> Either BuildError ResolvedPropRest
resolvePropExprRest th ctx (PropExprRest op ri) = do
  r <- resolveRightImpl th ctx ri
  return (ResolvedPropRest op r)

resolveRightImpl :: Theory -> VarContext -> RightImpl -> Either BuildError ResolvedRightImpl
resolveRightImpl th ctx (RightImpl leftI mbRight) = do
  l  <- resolveLeftImpl th ctx leftI
  mr <- case mbRight of
    Nothing       -> return Nothing
    Just (op, ri) -> Just . (op,) <$> resolveRightImpl th ctx ri
  return (ResolvedRightImpl l mr)

resolveLeftImpl :: Theory -> VarContext -> LeftImpl -> Either BuildError ResolvedLeftImpl
resolveLeftImpl th ctx (LeftImpl d rests) = do
  l  <- resolveDisj th ctx d
  rs <- mapM (\(LeftImplRest op d') -> ResolvedLeftImplRest op <$> resolveDisj th ctx d') rests
  return (ResolvedLeftImpl l rs)

resolveDisj :: Theory -> VarContext -> Disj -> Either BuildError ResolvedDisj
resolveDisj th ctx (Disj l rests) = do
  l'  <- resolveConj th ctx l
  rs' <- mapM (\(DisjRest op c) -> ResolvedDisjRest op <$> resolveConj th ctx c) rests
  return (ResolvedDisj l' rs')

resolveConj :: Theory -> VarContext -> Conj -> Either BuildError ResolvedConj
resolveConj th ctx (Conj l rests) = do
  l'  <- resolveNeg th ctx l
  rs' <- mapM (\(ConjRest op n) -> ResolvedConjRest op <$> resolveNeg th ctx n) rests
  return (ResolvedConj l' rs')

resolveNeg :: Theory -> VarContext -> Neg -> Either BuildError ResolvedNeg
resolveNeg th ctx (NegNot inner)  = ResolvedNegNot  <$> resolveNeg th ctx inner
resolveNeg th ctx (NegChild inner) = ResolvedNegChild <$> resolveQuantified th ctx inner

resolveQuantified :: Theory -> VarContext -> Quantified -> Either BuildError ResolvedQuantified
resolveQuantified th ctx (Quantified qs atomic) = do
  (ctx', rqs) <- foldM resolveQuantifier (ctx, []) qs
  rat <- resolveAtomicProp th ctx' atomic
  return (ResolvedQuantified rqs rat)
  where
    resolveQuantifier (c, acc) q = case q of
      QForall vd -> do (rvd, c') <- resolveVarDecl th c vd; return (c', acc ++ [ResolvedQForall rvd])
      QExists vd -> do (rvd, c') <- resolveVarDecl th c vd; return (c', acc ++ [ResolvedQExists rvd])

resolveVarDecl :: Theory -> VarContext -> VarDecl -> Either BuildError (ResolvedVarDecl, VarContext)
resolveVarDecl th ctx (VarDecl vid cos sexpr) = do
  s <- lookupSortByExpr th sexpr
  let isSet' = cos == "⊆"
  if isSet'
    then when (not (firstLetterIsUppercase vid)) $
           Left $ "Set/relation variable must start with uppercase: " ++ vid
    else when (not (isPropSort s) && not (isUniverseSort s) && firstLetterIsUppercase vid) $
           Left $ "Individual variable must start with lowercase: " ++ vid
  when ((isPropSort s || isUniverseSort s) && not isSet' && not (firstLetterIsUppercase vid)) $
    Left $ "Proposition/mereological variable must start with uppercase: " ++ vid
  let rvd = ResolvedVarDecl vid (varKindFromOpAndSort isSet' s) s
  return (rvd, extendVarContext ctx rvd)

resolveAtomicProp :: Theory -> VarContext -> AtomicProp -> Either BuildError ResolvedAtomicProp
resolveAtomicProp th ctx (AtomicProp tp) = ResolvedAtomicTermPair <$> resolveTermPair th ctx tp

resolveTermPair :: Theory -> VarContext -> TermPair -> Either BuildError ResolvedTermPair
resolveTermPair th ctx (TermPair leftT rights) = do
  lt  <- resolveTerm th ctx leftT
  rts <- mapM (resolveRFT th ctx) rights
  let ty = resolvedTermType lt
  return (ResolvedTermPair lt rts ty)

resolveRFT :: Theory -> VarContext -> RelationFollowedByTerm -> Either BuildError ResolvedRelationFollowedByTerm
resolveRFT th ctx (RelationFollowedByTerm specs op mbSort rightT) = do
  rt <- resolveTerm th ctx rightT
  ms <- case mbSort of
    Nothing -> return Nothing
    Just (OptionalSortExpr ind sexpr) -> do
      s <- lookupSortByExpr th sexpr
      return (Just (ResolvedOptionalSortExpr ind s))
  let path = map theoryRefName specs
  return (ResolvedRelationFollowedByTerm path op ms rt)

resolveTerm :: Theory -> VarContext -> Term -> Either BuildError ResolvedTerm
resolveTerm th ctx (Term leftF rights) = do
  lf  <- resolveFactor th ctx leftF
  rfs <- mapM (resolveOFF th ctx) rights
  let ty = resolvedFactorType lf
  return (ResolvedTerm lf rfs ty)

resolveOFF :: Theory -> VarContext -> OperationFollowedByFactor -> Either BuildError ResolvedOperationFollowedByFactor
resolveOFF th ctx (OperationFollowedByFactor specs op rightF) = do
  rf <- resolveFactor th ctx rightF
  let path = map theoryRefName specs
  return (ResolvedOperationFollowedByFactor path op rf)

resolveFactor :: Theory -> VarContext -> Factor -> Either BuildError ResolvedFactor
resolveFactor th ctx (Factor base suffixes) = do
  (rb, baseType) <- resolveBaseTerm th ctx base
  let baseEntity = case rb of
        ResolvedBTAtomic rc -> Just (resolvedConstEntity rc)
        _                   -> Nothing
  (rs, resultType, _) <- foldM (resolveSuffix th ctx) ([], baseType, baseEntity) suffixes
  return (ResolvedFactor rb rs resultType)

isSet :: ResolvedVarDecl -> Bool
isSet rvd = resolvedVarKind rvd == VarKindSet

varKindFromOpAndSort :: Bool -> Sort -> VarKind
varKindFromOpAndSort True  _  = VarKindSet
varKindFromOpAndSort False s
  | isPropSort     s = VarKindProposition
  | isUniverseSort s = VarKindMereological
  | otherwise        = VarKindIndividual

termIfPlain :: ResolvedPropExpr -> Maybe ResolvedTerm
termIfPlain (ResolvedPropBicond (ResolvedRightImpl left Nothing) []) =
  case left of
    ResolvedLeftImpl (ResolvedDisj (ResolvedConj (ResolvedNegChild (ResolvedQuantified [] atomic)) []) []) [] ->
      case atomic of
        ResolvedAtomicTermPair tp
          | null (resolvedTPRight tp) -> Just (resolvedTPLeft tp)
        ResolvedAtomicConstant cr
          | resolvedConstType cr /= PropositionClass ->
              Just (termFromConstant cr)
        _ -> Nothing
    _ -> Nothing
termIfPlain _ = Nothing

termFromConstant :: ResolvedConstantRef -> ResolvedTerm
termFromConstant cr =
  let factor = ResolvedFactor (ResolvedBTAtomic cr) [] (resolvedConstType cr)
  in ResolvedTerm factor [] (resolvedConstType cr)

resolveBaseTerm :: Theory -> VarContext -> BaseTerm -> Either BuildError (ResolvedBaseTerm, ExprType)
resolveBaseTerm th ctx bt = case bt of

  BTAtomic cref -> do
    rc <- resolveConstantRef th ctx cref
    return (ResolvedBTAtomic rc, resolvedConstType rc)

  BTEvaluationInTheory (EvaluationInTheory tnames operand) -> do
    let path = map AST.theoryName tnames
    subTh <- findSubtheoryByPath th path
    resolved <- qualifyPropExprConstants <$> resolvePropExpr subTh emptyVarContext operand
    let resolvedTy = maybe PropositionClass resolvedTermType (termIfPlain resolved)
    return (ResolvedBTEvaluationInTheory
              (ResolvedEvaluationInTheory path subTh resolved),
            resolvedTy)

  BTProjectionToSort (ProjectionToSort sexpr operand) -> do
    s  <- lookupSortByExpr th sexpr
    rt <- resolveTerm th ctx operand
    return (ResolvedBTProjectionToSort (ResolvedProjectionToSort s rt),
            RelationClass 1)

  BTProjectionToInterval (ProjectionToInterval lo hi operand) -> do
    rl <- resolveTerm th ctx lo
    rh <- resolveTerm th ctx hi
    rt <- resolveTerm th ctx operand
    return (ResolvedBTProjectionToInterval (ResolvedProjectionToInterval rl rh rt),
            OtherMereologicalClass)

  BTGeneralizedSumOrProduct (GeneralizedSumOrProduct sym var operand) -> do
    (rvar, ctx') <- case var of
      Left vd -> do
        (rvd, c) <- resolveVarDecl th ctx vd
        return (Left rvd, c)
      Right vid -> return (Right vid, ctx)
    rt <- resolveTerm th ctx' operand
    return (ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct sym rvar rt),
            OtherMereologicalClass)

  BTSingleton inner -> do
    rt <- resolveTerm th ctx inner
    let innerTy = resolvedTermType rt
    case innerTy of
      IndividualClass -> pure ()
      RelationClass 1 -> Left "Cannot take singleton of a set (singleton only for individuals)"
      _ -> Left "Singleton argument must be an individual"
    return (ResolvedBTSingleton rt, RelationClass 1)

  BTSetComprehension (SetComprehension vd body) -> do
    (rvd, ctx') <- resolveVarDecl th ctx vd
    when (isSet rvd) $
      Left "Set comprehension variable must be an individual (use ':', not '⊆')"
    rbody <- resolvePropExpr th ctx' body
    return ( ResolvedBTSetComprehension (ResolvedSetComprehension rvd rbody)
           , RelationClass 1 )

  BTDescription (Description vd body) -> do
    (rvd, ctx') <- resolveVarDecl th ctx vd
    when (isSet rvd) $
      Left "Description variable must be an individual (use ':', not '⊆')"
    rbody <- resolvePropExpr th ctx' body
    return ( ResolvedBTDescription (ResolvedDescription rvd rbody)
           , IndividualClass )

  BTParen inner -> do
    rp <- resolvePropExpr th ctx inner
    case termIfPlain rp of
      Just term | resolvedTermType term /= PropositionClass ->
        return (ResolvedBTTermParen term, resolvedTermType term)
      _ ->
        return (ResolvedBTPropParen rp, PropositionClass)

resolveSuffix
  :: Theory
  -> VarContext
  -> ([ResolvedTermSuffix], ExprType, Maybe Entity)
  -> TermSuffix
  -> Either BuildError ([ResolvedTermSuffix], ExprType, Maybe Entity)
resolveSuffix th ctx (acc, ty, curEnt) suffix = case suffix of

  SuffixCall (CallSuffix args) -> do
    rargs <- mapM (resolveTerm th ctx) args
    case ty of
      RelationClass arity -> do
        if length args /= arity
          then Left $ "Relation arity mismatch: expected " ++ show arity ++ ", got " ++ show (length args)
          else do
            forM_ rargs $ \arg -> do
              let argTy = resolvedTermType arg
              case argTy of
                IndividualClass -> return ()
                _ -> Left "Relation argument must be an individual"
            return (acc ++ [ResolvedSuffixCall rargs], PropositionClass, Nothing)
      FOLFunctionClass n ->
        if length args /= n
          then Left $ "FOL function arity mismatch: expected " ++ show n ++ ", got " ++ show (length args)
          else do
            let anySet = any (\arg -> case resolvedTermType arg of RelationClass 1 -> True; _ -> False) rargs
                resultClass = if anySet then RelationClass 1 else IndividualClass
            return (acc ++ [ResolvedSuffixCall rargs], resultClass, Nothing)
      SOLFunctionClass n ->
        if length args /= n
          then Left $ "SOL function arity mismatch: expected " ++ show n ++ ", got " ++ show (length args)
          else return (acc ++ [ResolvedSuffixCall rargs], RelationClass 1, Nothing)
      _ -> Left "Cannot apply arguments to a non‑function/non‑set"

  SuffixSpecialOp op -> do
    (resultEnt, newTy) <- applySpecialOp op ty curEnt
    return (acc ++ [ResolvedSuffixSpecialOp op resultEnt], newTy, resultEnt)

  SuffixDotAttr attr -> case attr of
    s | s `elem` ["min","max"] ->
        case ty of
          SortClass -> return (acc ++ [ResolvedSuffixDotAttr s], OtherMereologicalClass, Nothing)
          _ -> Left $ "Attempt to apply '." ++ s ++ "' to a non-sort."
    other -> return (acc ++ [ResolvedSuffixDotAttr other], ty, Nothing)

-- | Resolve a hash-attribute operation to its result entity and expression type.
-- Operations that yield a named entity return @Just entity@; type-coercion
-- operations (which do not change the underlying object) return @Nothing@.
applySpecialOp :: String -> ExprType -> Maybe Entity -> Either BuildError (Maybe Entity, ExprType)
applySpecialOp op ty curEnt = case op of

  s | s `elem` ["min", "max"] ->
    case (ty, curEnt) of
      (SortClass, Just (EntitySort s')) ->
        let m = if op == "min" then sortMin s' else sortMax s'
        in Right (Just (EntityMereological m), OtherMereologicalClass)
      (SortClass, _) -> Left $ "Cannot apply '#" ++ s ++ "': sort entity not available"
      _              -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-sort."

  "dom" ->
    case (ty, curEnt) of
      (FOLFunctionClass _, Just (EntityFunction f)) ->
        case funcDomain f of
          Just d  -> Right (Just (EntitySort d), SortClass)
          Nothing -> Left "Function has no domain sort"
      (SOLFunctionClass _, Just (EntityFunction f)) ->
        case funcDomain f of
          Just d  -> Right (Just (EntitySort d), SortClass)
          Nothing -> Left "Function has no domain sort"
      (FOLFunctionClass _, _) -> Left "Cannot apply '#dom': function entity not available"
      (SOLFunctionClass _, _) -> Left "Cannot apply '#dom': function entity not available"
      _                       -> Left "Attempt to apply '#dom' to a non-function."

  s | s `elem` ["res", "arg"] ->
    case ty of
      FOLFunctionClass _ -> resolveResArg s curEnt
      SOLFunctionClass _ -> resolveResArg s curEnt
      _                  -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-function."

  s | all (`elem` "0123456789") s && not (null s) ->
    case ty of
      FOLFunctionClass _ -> resolveArgN s curEnt
      SOLFunctionClass _ -> resolveArgN s curEnt
      _                  -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-function."

  -- Type-coercion ops: no entity change, only ExprType changes.
  s | s `elem` ["set", "individual", "mereological", "proposition"] ->
    let newClass = case s of
          "set"          -> RelationClass 1
          "individual"   -> IndividualClass
          "proposition"  -> PropositionClass
          "mereological" -> OtherMereologicalClass
          _              -> ty
    in Right (Nothing, newClass)

  other -> Right (Nothing, ty)  -- unknown op: pass through unchanged

  where
    resolveResArg s (Just (EntityFunction f)) =
      let mObj = if s == "res" then funcResObject f else funcArgument f
      in case mObj of
           Just obj -> Right (Just (EntityMereological obj), OtherMereologicalClass)
           Nothing  -> Left $ "Function has no '" ++ s ++ "' object"
    resolveResArg s _ = Left $ "Cannot apply '#" ++ s ++ "': function entity not available"

    resolveArgN s (Just (EntityFunction f)) =
      let n    = read s :: Int
          args = funcArgObjects f
      in if n >= 1 && n <= length args
         then Right (Just (EntityMereological (args !! (n - 1))), OtherMereologicalClass)
         else Left $ "Argument index #" ++ s ++ " out of range"
    resolveArgN s _ = Left $ "Cannot apply '#" ++ s ++ "': function entity not available"

resolveConstantRef :: Theory -> VarContext -> ConstantRef -> Either BuildError ResolvedConstantRef
resolveConstantRef th ctx (ConstantRef specs ref) = do
  let path = map theoryRefName specs
  let mbVar = if null path then lookupVarContext ctx ref else Nothing
  case mbVar of
    Just rvd -> do
      -- Bound variable: not a theory entity, use the source name as-is.
      let ty = case resolvedVarKind rvd of
                 VarKindSet          -> RelationClass 1
                 VarKindProposition  -> PropositionClass
                 VarKindMereological -> OtherMereologicalClass
                 VarKindIndividual   -> IndividualClass
      return (ResolvedConstantRef ref
                (EntityMereological (mkMereo th MereologicalEntityKindIndividual ref (resolvedVarSort rvd) FromSignature))
                ty)
    Nothing -> do
      -- Theory entity (including keywords ⊤ and ⊥, which carry a mereoAlias
      -- that lookupEntity dereferences automatically to the canonical
      -- sort-limit entity).
      entity <- lookupEntityInPath th path ref
      let ty   = entityToExprType entity
          -- For local lookups, use the entity's own name (after alias
          -- resolution this may differ from 'ref', e.g. "⊤" → "ℙ_Min").
          -- For cross-theory lookups, use the fully-qualified name.
          name = if null path then entityName entity
                 else entityFullyQualifiedName entity
      return (ResolvedConstantRef name entity ty)

-- ---------------------------------------------------------------------------
-- Term pair validation
-- ---------------------------------------------------------------------------

validateAllTermPairs :: ResolvedPropExpr -> Either String ()
validateAllTermPairs (ResolvedPropBicond left rests) = do
  validateRightImplTermPairs left
  mapM_ (\(ResolvedPropRest _ right) -> validateRightImplTermPairs right) rests

validateRightImplTermPairs :: ResolvedRightImpl -> Either String ()
validateRightImplTermPairs (ResolvedRightImpl left mbRight) = do
  validateLeftImplTermPairs left
  case mbRight of
    Nothing -> return ()
    Just (_, right) -> validateRightImplTermPairs right

validateLeftImplTermPairs :: ResolvedLeftImpl -> Either String ()
validateLeftImplTermPairs (ResolvedLeftImpl disj rests) = do
  validateDisjTermPairs disj
  mapM_ (\(ResolvedLeftImplRest _ d) -> validateDisjTermPairs d) rests

validateDisjTermPairs :: ResolvedDisj -> Either String ()
validateDisjTermPairs (ResolvedDisj conj rests) = do
  validateConjTermPairs conj
  mapM_ (\(ResolvedDisjRest _ c) -> validateConjTermPairs c) rests

validateConjTermPairs :: ResolvedConj -> Either String ()
validateConjTermPairs (ResolvedConj neg rests) = do
  validateNegTermPairs neg
  mapM_ (\(ResolvedConjRest _ n) -> validateNegTermPairs n) rests

validateNegTermPairs :: ResolvedNeg -> Either String ()
validateNegTermPairs (ResolvedNegNot inner) = validateNegTermPairs inner
validateNegTermPairs (ResolvedNegChild quantified) = validateQuantifiedTermPairs quantified

validateQuantifiedTermPairs :: ResolvedQuantified -> Either String ()
validateQuantifiedTermPairs (ResolvedQuantified _ atomic) = validateAtomicPropTermPairs atomic

validateAtomicPropTermPairs :: ResolvedAtomicProp -> Either String ()
validateAtomicPropTermPairs (ResolvedAtomicTermPair tp) = validateTermPairSemantics tp
validateAtomicPropTermPairs (ResolvedAtomicConstant _) = Right ()

validateTermPairSemantics :: ResolvedTermPair -> Either String ()
validateTermPairSemantics (ResolvedTermPair left rights _) = do
  let leftClass = resolvedTermType left
  forM_ rights $ \(ResolvedRelationFollowedByTerm _ op _ right) -> do
    let rightClass = resolvedTermType right
        eitherIsWildcard = leftClass  == OtherMereologicalClass
                        || rightClass == OtherMereologicalClass
    if eitherIsWildcard
      then Right ()
      else case op of
        "∈" -> do
          let leftOk  = leftClass  == IndividualClass
              rightOk = rightClass == RelationClass 1
          if not leftOk
            then Left $ "Left operand of ∈ must be an individual or mereological, got " ++ show leftClass
            else if not rightOk
              then Left $ "Right operand of ∈ must be a set or mereological, got " ++ show rightClass
              else Right ()
        "⊆" -> do
          let leftOk  = leftClass  == RelationClass 1
              rightOk = rightClass == RelationClass 1
          if not leftOk
            then Left $ "Left operand of ⊆ must be a set or mereological, got " ++ show leftClass
            else if not rightOk
              then Left $ "Right operand of ⊆ must be a set or mereological, got " ++ show rightClass
              else Right ()
        "≤" -> Right ()
        "=" ->
          if leftClass == rightClass
            then Right ()
            else Left $ "Cannot equate " ++ show leftClass ++ " with " ++ show rightClass
        _ -> Left $ "Unknown operator: " ++ op

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

firstLetterIsUppercase :: String -> Bool
firstLetterIsUppercase []    = False
firstLetterIsUppercase (c:_) = isUpper c

-- ---------------------------------------------------------------------------
-- Fact body validation (negation/absurdity check)
-- ---------------------------------------------------------------------------

validateFactBody :: FactKind -> ResolvedPropExpr -> Either String ()
validateFactBody FactKindFact expr
  | containsNegationOrAbsurdity expr =
      Left "Facts cannot contain negation (¬) or absurdity (⊥)"
  | otherwise = Right ()
validateFactBody _ _ = Right ()

containsNegationOrAbsurdity :: ResolvedPropExpr -> Bool
containsNegationOrAbsurdity (ResolvedPropBicond left rests) =
  containsNegationInRight left ||
  any (containsNegationInRight . resolvedPropRestRight) rests

containsNegationInRight :: ResolvedRightImpl -> Bool
containsNegationInRight (ResolvedRightImpl left mbRight) =
  containsNegationInLeft left ||
  maybe False (\(_, rhs) -> containsNegationInRight rhs) mbRight

containsNegationInLeft :: ResolvedLeftImpl -> Bool
containsNegationInLeft (ResolvedLeftImpl left rests) =
  containsNegationInDisj left ||
  any (containsNegationInDisj . resolvedLirRight) rests

containsNegationInDisj :: ResolvedDisj -> Bool
containsNegationInDisj (ResolvedDisj left rests) =
  containsNegationInConj left ||
  any (containsNegationInConj . resolvedDisjRestRight) rests

containsNegationInConj :: ResolvedConj -> Bool
containsNegationInConj (ResolvedConj left rests) =
  containsNegationInNeg left ||
  any (containsNegationInNeg . resolvedConjRestRight) rests

containsNegationInNeg :: ResolvedNeg -> Bool
containsNegationInNeg (ResolvedNegNot _) = True
containsNegationInNeg (ResolvedNegChild q) = containsNegationInQuantified q

containsNegationInQuantified :: ResolvedQuantified -> Bool
containsNegationInQuantified (ResolvedQuantified _ atom) =
  containsNegationOrAbsurdityInAtomic atom

-- | True when a 'ResolvedConstantRef' refers to the propositional falsity (⊥).
-- Uses entity inspection rather than the stored name so that it is robust to
-- name rewriting that happens during resolution (e.g. cross-theory qualified
-- names or the replacement of the "⊥" keyword by the real entity name).
isFalsityRef :: ResolvedConstantRef -> Bool
isFalsityRef ref = case resolvedConstEntity ref of
  EntityMereological mo ->
    mereoKind mo == MereologicalEntityKindUpperLimitForSort
    && maybe False isPropSort (mereoLimitForSort mo)
  _ -> False

containsNegationOrAbsurdityInAtomic :: ResolvedAtomicProp -> Bool
containsNegationOrAbsurdityInAtomic (ResolvedAtomicConstant ref) =
  isFalsityRef ref
containsNegationOrAbsurdityInAtomic (ResolvedAtomicTermPair tp) =
  containsNegationInTermPair tp

containsNegationInTermPair :: ResolvedTermPair -> Bool
containsNegationInTermPair (ResolvedTermPair left rights _) =
  containsNegationInTerm left ||
  any containsNegationInRelation rights

containsNegationInRelation :: ResolvedRelationFollowedByTerm -> Bool
containsNegationInRelation (ResolvedRelationFollowedByTerm _ _ _ right) =
  containsNegationInTerm right

containsNegationInTerm :: ResolvedTerm -> Bool
containsNegationInTerm (ResolvedTerm left rights _) =
  containsNegationInFactor left ||
  any containsNegationInOperation rights

containsNegationInOperation :: ResolvedOperationFollowedByFactor -> Bool
containsNegationInOperation (ResolvedOperationFollowedByFactor _ _ right) =
  containsNegationInFactor right

containsNegationInFactor :: ResolvedFactor -> Bool
containsNegationInFactor (ResolvedFactor base _ _) =
  containsNegationInBase base

containsNegationInBase :: ResolvedBaseTerm -> Bool
containsNegationInBase (ResolvedBTAtomic ref) =
  isFalsityRef ref
containsNegationInBase (ResolvedBTPropParen expr) =
  containsNegationOrAbsurdity expr
containsNegationInBase (ResolvedBTTermParen term) =
  containsNegationInTerm term
containsNegationInBase (ResolvedBTSingleton t) =
  containsNegationInTerm t
containsNegationInBase (ResolvedBTEvaluationInTheory eit) =
  containsNegationOrAbsurdity (resolvedEITOperand eit)
containsNegationInBase (ResolvedBTProjectionToSort pts) =
  containsNegationInTerm (resolvedPTOperand pts)
containsNegationInBase (ResolvedBTProjectionToInterval pti) =
  containsNegationInTerm (resolvedPTIOperand pti)
containsNegationInBase (ResolvedBTGeneralizedSumOrProduct gsp) =
  containsNegationInTerm (resolvedGSPOperand gsp)

-- | Rewrites resolved constant references to use their fully-qualified entity names.
-- This is used for <<theory>>(...) so that references are explicitly anchored to
-- the chosen subtheory in generated backend output.
qualifyPropExprConstants :: ResolvedPropExpr -> ResolvedPropExpr
qualifyPropExprConstants (ResolvedPropBicond l rs) =
  ResolvedPropBicond (goRightImpl l) (map goPropRest rs)
  where
    goPropRest (ResolvedPropRest op r) = ResolvedPropRest op (goRightImpl r)
    goRightImpl (ResolvedRightImpl li mr) =
      ResolvedRightImpl (goLeftImpl li) (fmap (\(op, r) -> (op, goRightImpl r)) mr)
    goLeftImpl (ResolvedLeftImpl d rs') =
      ResolvedLeftImpl (goDisj d) (map (\(ResolvedLeftImplRest op d') -> ResolvedLeftImplRest op (goDisj d')) rs')
    goDisj (ResolvedDisj c rs') =
      ResolvedDisj (goConj c) (map (\(ResolvedDisjRest op c') -> ResolvedDisjRest op (goConj c')) rs')
    goConj (ResolvedConj n rs') =
      ResolvedConj (goNeg n) (map (\(ResolvedConjRest op n') -> ResolvedConjRest op (goNeg n')) rs')
    goNeg (ResolvedNegNot n) = ResolvedNegNot (goNeg n)
    goNeg (ResolvedNegChild q) = ResolvedNegChild (goQuantified q)
    goQuantified (ResolvedQuantified qs a) = ResolvedQuantified qs (goAtomic a)
    goAtomic (ResolvedAtomicTermPair tp) = ResolvedAtomicTermPair (goTermPair tp)
    goAtomic (ResolvedAtomicConstant ref) = ResolvedAtomicConstant (qualifyConst ref)
    goTermPair (ResolvedTermPair lt rs' ty) = ResolvedTermPair (goTerm lt) (map goRFT rs') ty
    goRFT (ResolvedRelationFollowedByTerm p op ms rt) =
      ResolvedRelationFollowedByTerm p op ms (goTerm rt)
    goTerm (ResolvedTerm f rs' ty) = ResolvedTerm (goFactor f) (map goOFF rs') ty
    goOFF (ResolvedOperationFollowedByFactor p op rf) =
      ResolvedOperationFollowedByFactor p op (goFactor rf)
    goFactor (ResolvedFactor bt sfx ty) = ResolvedFactor (goBase bt) sfx ty
    goBase (ResolvedBTAtomic cr) = ResolvedBTAtomic (qualifyConst cr)
    goBase (ResolvedBTPropParen p) = ResolvedBTPropParen (qualifyPropExprConstants p)
    goBase (ResolvedBTTermParen t) = ResolvedBTTermParen (goTerm t)
    goBase (ResolvedBTSingleton t) = ResolvedBTSingleton (goTerm t)
    goBase (ResolvedBTEvaluationInTheory (ResolvedEvaluationInTheory p sub inner)) =
      ResolvedBTEvaluationInTheory (ResolvedEvaluationInTheory p sub (qualifyPropExprConstants inner))
    goBase (ResolvedBTProjectionToSort (ResolvedProjectionToSort s t)) =
      ResolvedBTProjectionToSort (ResolvedProjectionToSort s (goTerm t))
    goBase (ResolvedBTProjectionToInterval (ResolvedProjectionToInterval lo hi t)) =
      ResolvedBTProjectionToInterval (ResolvedProjectionToInterval (goTerm lo) (goTerm hi) (goTerm t))
    goBase (ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct sym v t)) =
      ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct sym v (goTerm t))
    goBase (ResolvedBTSetComprehension (ResolvedSetComprehension v p)) =
      ResolvedBTSetComprehension (ResolvedSetComprehension v (qualifyPropExprConstants p))
    goBase (ResolvedBTDescription (ResolvedDescription v p)) =
      ResolvedBTDescription (ResolvedDescription v (qualifyPropExprConstants p))

    qualifyConst cr = cr { resolvedConstRefName = entityFullyQualifiedName (resolvedConstEntity cr) }
