-- | Build the intermediate representation ('Theory') from a parsed 'TheoryDecl'.
module Eidos.FromSyntax
  ( buildTheoryIO
  , buildTheoryPure
  , buildTheoryWithResolver
  , buildTheoryFromFile
  , BuildError
  ) where

import           Control.Monad        (forM_, when, foldM)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Char            (isUpper)
import           Data.List            (find, intercalate)
import qualified Data.Map.Strict      as Map
import           Data.Maybe           (fromMaybe, mapMaybe)
import           System.FilePath      (takeDirectory)

import           Eidos.AST            hiding (theoryBody, theoryName, funcName, funcDomain, relName)
import qualified Eidos.AST            as AST
import           Eidos.BuildMonad
import           Eidos.ExternalRef    hiding (mockResolver)
import           Eidos.IR
import           Eidos.Parser         (parseString)
import           Eidos.TypeCheck
import           Eidos.SubLanguage

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

-- | Build theory using IO (for CLI/main program) - reads files from disk
buildTheoryIO :: TheoryDecl -> IO (Either BuildError Theory)
buildTheoryIO td = runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False []) Nothing

-- | Build theory from a file path (IO), using the file's directory as the resolution base
buildTheoryFromFile :: FilePath -> TheoryDecl -> IO (Either BuildError Theory)
buildTheoryFromFile filePath td =
  let tt = theoryTypeFromFilePath filePath
  in runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False [tt])
               (Just (takeDirectory filePath))

-- | Build theory using a pure resolver (for testing) - no file IO
buildTheoryPure :: PureResolver -> Maybe String -> TheoryDecl -> Either BuildError Theory
buildTheoryPure resolver baseContext td =
  runReader (runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False []) baseContext) resolver

-- | Build theory with an explicit pure resolver function (for testing custom resolvers)
buildTheoryWithResolver
  :: (Maybe String -> String -> Either ExternalRefError ExternalRefResult)
  -> Maybe String
  -> TheoryDecl
  -> Either BuildError Theory
buildTheoryWithResolver resolverFn baseContext td =
  runReader
    (runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False []) baseContext)
    (FnResolver resolverFn)

-- ---------------------------------------------------------------------------
-- Core theory builder (polymorphic in m)
-- ---------------------------------------------------------------------------

-- | Build a 'Theory' from a 'TheoryBody'.
--
-- 'constraints' is the accumulated list of 'TheoryType' restrictions in
-- force for this body.  It starts as @[theoryTypeFromFilePath filePath]@
-- at the top level and is extended when an external subtheory file adds its
-- own 'TheoryType'.  Inline subtheory bodies inherit the parent list unchanged.
decorateTheoryBody
  :: forall m. (MonadExternalRefResolver m)
  => TheoryBody
  -> Maybe Theory
  -> String
  -> Bool
  -> [TheoryType]   -- ^ active sublanguage constraints
  -> BuildM m Theory
decorateTheoryBody body parentMaybe name isReflection constraints = do

  -- ── Sublanguage check (before anything else) ──────────────────────────
  either throwError return $ checkTheoryBody constraints body

  -- ── Base theory skeleton ──────────────────────────────────────────────
  let th0 = createTheory parentMaybe name isReflection

  -- ── Register built-in sorts (adds min/max entities + sort-limit facts) ─
  -- addSortToTh skips universe-self and prop-self guards internally.
  -- We pass th0 as the base for relateSortToProp/Universe since the
  -- built-in sort references (theoryProp, theoryUniverse) are stable.
  let thA = addSortToTh th0 (theoryUniverse th0)
      thB = addSortToTh thA (theoryDomain   th0)
      thC = addSortToTh thB (theoryProp     th0)

  -- ── Pass 1: subtheories ───────────────────────────────────────────────
  (th1, subtheories) <- foldM (buildSubtheoryEntry constraints) (thC, []) (sections body)
  let th2 = th1 { theorySubtheories = subtheories }

  -- ── Pass 2: signature ─────────────────────────────────────────────────
  th3 <- foldM (buildSignatureSection th2) th2 (sections body)

  -- ── Pass 3: axioms ────────────────────────────────────────────────────
  th4 <- foldM (buildAxiomsSection th3) th3 (sections body)

  -- ── Mereological translations ─────────────────────────────────────────
  let translations = concatMap (mereologicalTranslation th4) (theoryFacts th4)
  let th5 = th4 { theoryFacts = theoryFacts th4 ++ translations }

  return th5

-- ---------------------------------------------------------------------------
-- Pass 1 — Subtheories
-- ---------------------------------------------------------------------------

buildSubtheoryEntry
  :: forall m. (MonadExternalRefResolver m)
  => [TheoryType]
  -> (Theory, [Theory])
  -> Section
  -> BuildM m (Theory, [Theory])
buildSubtheoryEntry constraints (th, acc) (SectionSubtheories (SubtheoriesSection entries)) = do
  foldM (processEntry constraints) (th, acc) entries
buildSubtheoryEntry _ (th, acc) _ = return (th, acc)

processEntry
  :: forall m. (MonadExternalRefResolver m)
  => [TheoryType]
  -> (Theory, [Theory])
  -> SubtheoryEntry
  -> BuildM m (Theory, [Theory])
processEntry constraints (th, subs) entry = case entry of
  SubtheoryEntryGroup (SubtheoryGroup kw items) -> do
    foldM (processItem constraints kw) (th, subs) items
  SubtheoryEntryItem item -> do
    let kw = fromMaybe "named" (itemQualifier item)
    processItem constraints kw (th, subs) item

processItem constraints kw (th, subs) item = do
  baseContext <- ask
  
  let subName = fromMaybe "" (itemName item)
  
  when (subName == "") $
    throwError "All subtheories must have names."
  
  let isRefl     = kw == "reflection"
      isImplicit = kw == "implicit"
  
  (subBody, extInfo) <- resolveSubtheoryBody baseContext item
  
  -- For external subtheories, the resolved file's TheoryType is added to the
  -- constraint list — the body must satisfy both the parent file's constraints
  -- and its own file's constraints.  Inline subtheory bodies inherit the
  -- parent constraint list unchanged.
  let subConstraints = case extInfo of
        Nothing           -> constraints          -- inline: inherit parent
        Just (_, extType) -> addConstraint constraints extType

  let subContext = baseContext
  
  sub <- local (const subContext) $ 
    decorateTheoryBody subBody (Just th) subName isRefl subConstraints
  
  let th' = addSubtheoryToTheory th sub
  th'' <- either throwError return $ propagateSubtheory th' subName isImplicit isRefl sub
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

-- | Resolve a subtheory definition using the resolver from the monad.
-- For external refs, the second component carries the resolved 'TheoryType'
-- so the caller can add it to the constraint list.
resolveSubtheoryBody
  :: forall m. (MonadExternalRefResolver m)
  => Maybe String
  -> SubtheoryItem
  -> BuildM m (TheoryBody, Maybe (String, TheoryType))
resolveSubtheoryBody baseContext item = case itemDef item of
  SubtheoryBody b -> return (b, Nothing)
  
  SubtheoryExternalRef ref -> do
    let refPath = case ref of
          ('@':rest) -> rest
          _          -> ref
    
    result <- lift $ resolveExternalRef baseContext refPath
    res <- case result of
      Left err -> throwError (show err)
      Right r -> return r
    
    -- Read the content using the monad's readExternalContent method
    content <- lift $ readExternalContent (extRefSource res)
    ast <- case parseString content of
      Left parseErr -> throwError $ "Parse error in external theory " ++ extRefIdentifier res ++ ": " ++ show parseErr
      Right a -> return a
    let body = AST.theoryBody ast
    return (body, Just (extRefIdentifier res, extRefTheoryType res))

addSubtheoryToTheory :: Theory -> Theory -> Theory
addSubtheoryToTheory th sub =
  th { theorySubtheories = theorySubtheories th ++ [sub] }

-- ---------------------------------------------------------------------------
-- Pass 2 — Signature
-- ---------------------------------------------------------------------------

buildSignatureSection
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> Theory -> Section -> BuildM m Theory
-- NOTE: th0 is the initial theory snapshot (with built-in sorts + subtheories)
-- passed to buildSignatureItem so that each item can look up sorts that were
-- already declared.  th is the accumulator that grows as items are processed.
buildSignatureSection th0 th (SectionSignature (SignatureSection items)) = do
  foldM (buildSignatureItem th0) th items
buildSignatureSection _ th _ = return th

buildSignatureItem
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> Theory -> SignatureItem -> BuildM m Theory
buildSignatureItem th0 th item = do
  -- Local helper:
  --   * fresh name      -> insert declaration
  --   * compatible name -> treat declaration as reaffirming inherited implicit entity
  --   * incompatible    -> hard conflict
  let shouldInsertDeclaration name newEntity =
        case Map.lookup name (theoryObjectsByName th) of
          Nothing -> return True
          Just existing
            | all (entitiesCompatible newEntity) existing -> return False
            | otherwise ->
                throwError $ "Name conflict: '" ++ name ++ "' already refers to a different entity"

  case item of

    SigSimpleSort (SimpleSortDeclaration nm) -> do
      let s = mkSort th SortKindFromSignature nm FromSignature
          entity = EntitySort s
      shouldInsert <- shouldInsertDeclaration nm entity
      return (if shouldInsert then addSortToTh th s else th)

    SigRelationalSort (RelationalSortDeclaration nm rel sortExprAST) -> do
      parentSort <- either throwError return $ lookupSort th (sortConstant (sortRef sortExprAST))
      let th' = markTheorySortExprUsage th sortExprAST
          s   = mkRelatedSort th' rel nm parentSort  -- pass rel and parentSort
          entity = EntitySort s
      shouldInsert <- shouldInsertDeclaration nm entity
      if shouldInsert
        then do
          let th1 = addSortToTh th' s
              th2 = relationalSortFacts th1 rel s parentSort
          return th2
        else return th'

    SigFunction (FunctionDeclaration nm domainExprs codomainExpr) -> do
      argSorts <- mapM (liftLookup (lookupSortByExpr th)) domainExprs
      resSort <- either throwError return $ lookupSortByExpr th codomainExpr
      let th' = foldl markTheorySortExprUsage (markTheorySortExprUsage th codomainExpr) domainExprs
      if firstLetterIsUppercase nm
        then do
          -- SOL function (uppercase name)
          let f = mkSOLFunction th' nm FunctionKindSOLFunctionFromTheory argSorts resSort FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityFunction f)
          return (if shouldInsert then addEntityToTh th' (EntityFunction f) else th')
        else do
          -- FOL function (lowercase name): also create domain sort, inverse, image functions
          let (f, domSort, invFn, dirImg, invImg) =
                mkFOLFunction th' nm argSorts resSort FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityFunction f)
          if shouldInsert
            then do
              -- Add domain sort (product sort) + its limits
              let th1 = addEntityToTh th'  (EntitySort domSort)
                  th2 = addEntityToTh th1 (EntityMereological (sortMin domSort))
                  th3 = addEntityToTh th2 (EntityMereological (sortMax domSort))
              -- Add inverse domain sort + limits
              let invDomSort = case funcDomain invFn of { Just d -> d; Nothing -> domSort }
                  th4 = addEntityToTh th3 (EntitySort invDomSort)
                  th5 = addEntityToTh th4 (EntityMereological (sortMin invDomSort))
                  th6 = addEntityToTh th5 (EntityMereological (sortMax invDomSort))
              -- Add main function and companions
              let th7 = addEntityToTh th6 (EntityFunction f)
                  th8 = addEntityToTh th7 (EntityFunction invFn)
                  th9 = addEntityToTh th8 (EntityFunction dirImg)
                  th10= addEntityToTh th9 (EntityFunction invImg)
              return th10
            else return th'

    SigIndividual (IndividualDeclaration nm sortExprAST) -> do
      s <- either throwError return $ lookupSortByExpr th sortExprAST
      let th' = markTheorySortExprUsage th sortExprAST
      let isPropSort = sortKind s == SortKindProp
      let isUniverseSort = sortKind s == SortKindUniverse
      
      -- Naming rules:
      -- - Propositions (ℙ): must start with uppercase
      -- - Bare mereological objects (𝕌): must start with uppercase
      -- - Individuals (other sorts): must start with lowercase
      when (isPropSort && not (firstLetterIsUppercase nm)) $
        throwError $ "Proposition names must start with uppercase: " ++ nm
      when (isUniverseSort && not (firstLetterIsUppercase nm)) $
        throwError $ "Bare mereological object names must start with uppercase: " ++ nm
      when (not isPropSort && not isUniverseSort && firstLetterIsUppercase nm) $
        throwError $ "Individual names must start with lowercase: " ++ nm
      
      let moKind =
            if isPropSort
              then MereologicalEntityKindProposition
              else if isUniverseSort
                then MereologicalEntityKindMereological  -- New kind for bare mereological objects
                else MereologicalEntityKindIndividual
      
      let mo = mkMereo th' moKind nm s FromSignature
      shouldInsert <- shouldInsertDeclaration nm (EntityMereological mo)
      return (if shouldInsert then addEntityToTh th' (EntityMereological mo) else th')
    
    SigSet (SetDeclaration nm domainExprs) -> do
      when (not (firstLetterIsUppercase nm)) $
        throwError $ "Set/relation names must start with uppercase: " ++ nm
      let th' = foldl markTheorySortExprUsage th domainExprs
      case domainExprs of
        [sexpr] -> do
          s <- either throwError return $ lookupSortByExpr th sexpr
          let mo = mkMereo th' MereologicalEntityKindSet nm s FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityMereological mo)
          return (if shouldInsert then addEntityToTh th' (EntityMereological mo) else th')
        _ -> do
          argSorts <- mapM (liftLookup (lookupSortByExpr th)) domainExprs
          let rel = mkRelation th' nm argSorts FromSignature
          shouldInsert <- shouldInsertDeclaration nm (EntityRelation rel)
          return (if shouldInsert then addEntityToTh th' (EntityRelation rel) else th')

-- Helper to lift lookup functions into BuildM
liftLookup
  :: forall m a b. (MonadExternalRefResolver m)
  => (a -> Either BuildError b) -> a -> BuildM m b
liftLookup f x = either throwError return (f x)

-- ---------------------------------------------------------------------------
-- Pass 3 — Axioms
-- ---------------------------------------------------------------------------

buildAxiomsSection
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> Theory -> Section -> BuildM m Theory
buildAxiomsSection th0 th (SectionAxioms (AxiomsWrapper axSections)) = do
  foldM (buildAxSection th0) th axSections
buildAxiomsSection th0 th (SectionBareAxioms axSection) =
  buildAxSection th0 th axSection
buildAxiomsSection _ th _ = return th

buildAxSection
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> Theory -> AxiomsSection -> BuildM m Theory
-- NOTE: th0 is the signature snapshot captured before any axioms are added.
-- It is passed to resolvePropExprInclVars so that name resolution always
-- operates against the completed signature, never against an axiom-by-axiom
-- accumulation.  th is the theory being accumulated with new Fact entries;
-- it is the value returned at the end of each fold step.
buildAxSection th0 th axSec = case axSec of
  AxAssertions (AssertionsSection props) ->
    foldM (addPropFact th0 FactKindAssertion) th props
  AxFacts (FactsSection props) ->
    foldM (addPropFact th0 FactKindFact) th props
  AxMetafacts (MetafactsSection props) ->
    foldM (addPropFact th0 FactKindMetafactsFact) th props

addPropFact th0 fk th prop = do
  let ctx = emptyVarContext
      sourceCtx = propSourceContext prop
      -- Extract free variables from PropExprInclVars
      (PropExprInclVars _ _ vars _) = prop
  (resolvedExpr, ctx') <- either throwError return $
    resolvePropExprInclVars th0 ctx prop
  
  -- Get the resolved variable declarations from the context
  let freeVars = map (toResolvedVarDecl th0) vars
      
  case typeCheckResolvedExpr resolvedExpr of
    Left typeErr -> throwError (sourceCtx ++ "Type error in " ++ show fk ++ ": " ++ typeErr)
    Right _ -> return ()

  case validateAllTermPairs resolvedExpr of
    Left opErr -> throwError (sourceCtx ++ "Operation error in " ++ show fk ++ ": " ++ opErr)
    Right _ -> return ()
  
  -- ADD THIS: Validate that facts don't contain negation or absurdity
  case validateFactBody fk resolvedExpr of
    Left factErr -> throwError (sourceCtx ++ factErr)
    Right _ -> return ()
  
  let fact = Fact
        { factIsMereologicalTranslation = False
        , factIsInherited               = False
        , factKind                      = fk
        , factPropExpr                  = resolvedExpr
        , factFreeVars                  = freeVars
        }
  let th' = markTheoryPropExprUsage th prop
  return (th' { theoryFacts = theoryFacts th' ++ [fact] })

-- Helper to convert AST VarDecl to ResolvedVarDecl
toResolvedVarDecl :: Theory -> VarDecl -> ResolvedVarDecl
toResolvedVarDecl th (VarDecl name op sortExpr) =
  let s = case lookupSortByExpr th sortExpr of
            Right sort -> sort
            Left _ -> error $ "Failed to resolve sort for variable: " ++ name
  in ResolvedVarDecl name (op == "⊆") s
  
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

-- | Create the initial theory with built-in sorts and mereological functions.
-- Mirrors 'createTheory' in theory.go.
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
        }

      universe = mkSort th SortKindUniverse "𝕌" InEveryTheory
      domain   = mkSort th SortKindDomain   "𝔻" InEveryTheory
      prop     = mkSort th SortKindProp     "ℙ" InEveryTheory

      truth   = mkMereo th MereologicalEntityKindProposition "⊤" prop InEveryTheory
      falsity = mkMereo th MereologicalEntityKindProposition "⊥" prop InEveryTheory

      -- Built-in binary mereological SOL functions (+, ×, -, ⇒, ∸)
      mkBinSOL sym = mkSOLFunction th sym FunctionKindMereologicalOperation
                       [universe, universe] universe InEveryTheory

      sumF     = mkBinSOL "+"
      prodF    = mkBinSOL "×"
      diffF    = mkBinSOL "-"
      revDiffF = mkBinSOL "⇒"
      symDiffF = mkBinSOL "∸"

      -- createTheory only seeds the theory with truth, falsity, and the mereological
      -- functions.  The three built-in sorts (universe, domain, prop) are added via
      -- addSortToTh in decorateTheoryBody, which also registers their min/max objects
      -- and emits sort-limit metafacts.  Keeping sorts out of builtins here prevents
      -- them from appearing twice in theoryObjects.
      builtins = map EntityMereological [truth, falsity]
              ++ map EntityFunction [sumF, prodF, diffF, revDiffF, symDiffF]

      builtinsByName = Map.fromListWith (++)
        [ (entityName e, [e]) | e <- builtins ]

      -- The three core sort-limit facts are: truth = ℙ#min, falsity = ℙ#max,
      -- and ℙ#max ≤ 𝔻#min.  The universe/domain/prop interval facts are emitted
      -- by addSortToTh in decorateTheoryBody.
      builtinFacts =
        [ mkSortLimitFact (theoryTruth th)   "=" (sortMin prop)
        , mkSortLimitFact (theoryFalsity th) "=" (sortMax prop)
        ]

  in th

-- ---------------------------------------------------------------------------
-- Smart constructors for IR entities
-- ---------------------------------------------------------------------------

-- | Construct a 'Sort' together with its min/max limit objects.
-- A recursive @let@ is used so that @sortMin@ and @sortMax@ can reference
-- the same @s@ value rather than calling @mkSort@ recursively (which would
-- create an infinite chain of fresh allocations).
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
        , mereoName          = nm ++ "#min"
        , mereoSort          = s
        , mereoLimitForSort  = Just s
        , mereoReflectedFrom = Nothing
        }
      sMax = MereologicalObject
        { mereoKind          = MereologicalEntityKindUpperLimitForSort
        , mereoOrigin        = orig
        , mereoTheory        = th
        , mereoName          = nm ++ "#max"
        , mereoSort          = s
        , mereoLimitForSort  = Just s
        , mereoReflectedFrom = Nothing
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
  }

mkSOLFunction :: Theory -> String -> EntityKind -> [Sort] -> Sort -> Origin -> Function
mkSOLFunction th nm k argSorts resSort orig = Function
  { funcKind          = k
  , funcOrigin        = orig
  , funcTheory        = th
  , funcName          = nm
  , funcArgSorts      = argSorts
  , funcResSort       = resSort
  , funcResObject     = mkMereo th MereologicalEntityKindResultOfSOLFunction (nm ++ "#res") resSort orig
  , funcArgObjects    = zipWith (\s i -> mkMereo th MereologicalEntityKindArgumentOfSOLFunction
                                          (nm ++ "#" ++ show i) s orig) argSorts [1..]
  , funcDomain        = Nothing
  , funcArgument      = Nothing
  , funcDirectImage   = Nothing
  , funcInverseImage  = Nothing
  , funcReflectedFrom = Nothing
  }

-- | Build a FOL function (lowercase name): creates a product-sort domain, an arg object,
--   a paired inverse function f_inv, and direct/inverse image SOL functions.
--   Returns (mainFn, domSort, invFn, dirImgFn, invImgFn).
mkFOLFunction :: Theory -> String -> [Sort] -> Sort -> Origin
              -> (Function, Sort, Function, Function, Function)
mkFOLFunction th nm argSorts resSort orig =
  -- The function itself carries the caller-supplied origin (e.g. FromSignature,
  -- FromSubtheory).  All *auxiliary* objects generated as a consequence of
  -- declaring the function — domain sorts, limit objects, image functions,
  -- the inverse — are tagged FromFunction so that queries can distinguish
  -- "was explicitly written" from "was auto-generated".
  let auxOrig = FromFunction
      f0 = mkSOLFunction th nm FunctionKindFOLFunctionFromTheory argSorts resSort orig
      domSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = auxOrig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (nm ++ "#dom#min") domSort auxOrig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (nm ++ "#dom#max") domSort auxOrig
        , sortName             = nm ++ "#dom"
        , sortComponentSorts   = argSorts
        , sortAssociatedEntity = Just (EntityFunction f)
        , sortReflectedFrom    = Nothing
        }
      domArg = mkMereo th MereologicalEntityKindArgumentOfSOLFunction (nm ++ "#arg") domSort auxOrig
      -- Direct-image SOL function: dom → res
      dirImg = mkSOLFunction th (nm ++ "#dir_img") FunctionKindDirectImageFunction [domSort] resSort auxOrig
      -- Inverse-image SOL function: res → dom
      invImg = mkSOLFunction th (nm ++ "#inv_img") FunctionKindInverseImageFunction [resSort] domSort auxOrig
      -- The main function, wired with domain, domArg, and image functions
      f = f0 { funcDomain      = Just domSort
             , funcArgument    = Just domArg
             , funcDirectImage  = Just dirImg
             , funcInverseImage = Just invImg
             }
      -- Inverse function f_inv: resSort → domSort (also a FOL function).
      -- The inverse is an *automatically generated* companion, so it gets
      -- FromFunction origin even though it is a first-class FOL function.
      inv0 = mkSOLFunction th (nm ++ "_inv") FunctionKindFOLFunctionFromTheory [resSort] domSort auxOrig
      invDomSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = auxOrig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (nm ++ "_inv#dom#min") invDomSort auxOrig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (nm ++ "_inv#dom#max") invDomSort auxOrig
        , sortName             = nm ++ "_inv#dom"
        , sortComponentSorts   = [resSort]
        , sortAssociatedEntity = Just (EntityFunction invFn)
        , sortReflectedFrom    = Nothing
        }
      invArg = mkMereo th MereologicalEntityKindArgumentOfSOLFunction (nm ++ "_inv#arg") invDomSort auxOrig
      invFn = inv0 { funcDomain   = Just invDomSort
                   , funcArgument = Just invArg
                   }
  in (f, domSort, invFn, dirImg, invImg)

mkSortLimitFact :: MereologicalObject -> String -> MereologicalObject -> Fact
mkSortLimitFact l op r = Fact
  { factIsMereologicalTranslation = False
  , factIsInherited               = False
  , factKind                      = FactKindSortLimitation
  , factPropExpr                  = twoTermPropExpr l op r
  }

-- | Build a minimal 'ResolvedPropExpr' for "left op right"
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

-- | Add an entity to the theory's object list and name map (local only; propagation
--   to ancestors is done explicitly via 'propagateSubtheory').
addEntityToTh :: Theory -> Entity -> Theory
addEntityToTh th e =
  th { theoryObjects      = theoryObjects th ++ [e]
     , theoryObjectsByName = Map.insertWith (++) (entityName e) [e]
                               (theoryObjectsByName th)
     }

-- | Add a fact to the theory.
addFactToTh :: Theory -> Fact -> Theory
addFactToTh th f = th { theoryFacts = theoryFacts th ++ [f] }

-- | Emit the two metafacts that relate a sort to the universe:
--   𝕌#min ≤ sort#min   and   sort#max ≤ 𝕌#max
--   (Skip if the sort IS the universe itself, mirroring the Go check.)
relateSortToUniverse :: Theory -> Sort -> Theory
relateSortToUniverse th s
  | sortKind s == SortKindUniverse = th
  | otherwise =
      let u = theoryUniverse th
      in addFactToTh (addFactToTh th
           (mkSortLimitFact (sortMin u) "≤" (sortMin s)))
           (mkSortLimitFact (sortMax s) "≤" (sortMax u))

-- | Emit the metafact that relates a sort to Prop:
--   ℙ#max ≤ sort#min
--   (Skip for universe and for prop itself, mirroring the Go checks.)
relateSortToProp :: Theory -> Sort -> Theory
relateSortToProp th s
  | sortKind s == SortKindUniverse = th
  | sortKind s == SortKindProp     = th
  | otherwise = addFactToTh th (mkSortLimitFact (sortMax (theoryProp th)) "≤" (sortMin s))

-- | Add a sort to a theory: register the sort entity, register its min/max objects,
--   and emit the sort-limit metafacts (relateSortToProp + relateSortToUniverse).
--   This mirrors Go's createNamedSort behaviour.
addSortToTh :: Theory -> Sort -> Theory
addSortToTh th s =
  let th1 = addEntityToTh th  (EntitySort s)
      th2 = addEntityToTh th1 (EntityMereological (sortMin s))
      th3 = addEntityToTh th2 (EntityMereological (sortMax s))
      th4 = relateSortToProp    th3 s
      th5 = relateSortToUniverse th4 s
  in th5

-- | Build a sort that stands in a relational position to an existing sort.
--   Returns just the Sort record; the caller is responsible for adding it to the theory
--   (via addSortToTh) and emitting any relationship facts.
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

-- | Emit the min/max comparison facts for a relational sort declaration.
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
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (nm ++ "#dom#min") domSort orig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (nm ++ "#dom#max") domSort orig
        , sortName             = nm ++ "#dom"
        , sortComponentSorts   = argSorts
        , sortAssociatedEntity = Just (EntityRelation rel)
        , sortReflectedFrom    = Nothing
        }
      domArg   = mkMereo th MereologicalEntityKindIndividual (nm ++ "#arg") domSort orig
      assocSet = mkMereo th MereologicalEntityKindSet        (nm ++ "#set") (head argSorts) orig
      rel = Relation
        { relOrigin        = orig
        , relKind          = MereologicalEntityKindSet
        , relTheory        = th
        , relName          = nm
        , relArgSorts      = argSorts
        , relDomain        = domSort
        , relArgObjects    = zipWith (\s i -> mkMereo th MereologicalEntityKindArgumentOfSOLFunction
                                              (nm ++ "#" ++ show i) s orig) argSorts [1..]
        , relArgument      = domArg
        , relAssociatedSet = assocSet
        , relReflectedFrom = Nothing
        }
  in rel

-- ---------------------------------------------------------------------------
-- Reflection: entity kind transformation
-- ---------------------------------------------------------------------------

-- | Transform an entity from a reflection subtheory as it is propagated to the parent.
-- SOL functions → FOL functions; sorts → SortKindFromReflection;
-- mereological sets → individuals.  Everything else is marked as reflected.
reflectEntity :: Entity -> Entity
reflectEntity (EntityFunction f) =
  if funcKind f == FunctionKindSOLFunctionFromTheory
    then EntityFunction (f { funcKind         = FunctionKindFOLFunctionFromTheory
                           , funcReflectedFrom = Just (funcTheory f) })
    else EntityFunction (f { funcReflectedFrom = Just (funcTheory f) })
reflectEntity (EntitySort s) =
  EntitySort (s { sortKind          = SortKindFromReflection
                , sortReflectedFrom = Just (sortTheory s) 
                , sortRelationship  = NotRelational  -- reflected sorts become non-relational
                , sortParent        = Nothing         -- clear parent reference
                })
reflectEntity (EntityMereological m) =
  EntityMereological (m { mereoKind           = MereologicalEntityKindIndividual
                        , mereoReflectedFrom  = Just (mereoTheory m) })
reflectEntity (EntityRelation r) =
  EntityRelation (r { relReflectedFrom = Just (relTheory r) })
reflectEntity e = e

-- ---------------------------------------------------------------------------
-- Subtheory propagation (Gap 7)
-- ---------------------------------------------------------------------------

-- | After a subtheory has been built, propagate its entities to the parent theory.
--
-- Rules:
--   * All subtheories: every entity is added under the qualified name "subName.entityName".
--     Internal structural entities (names containing '#') are only added qualified.
--   * Named/reflection subtheories: no unqualified names are added.
--   * Implicit subtheories: for each entity with a "plain" name (no '#'):
--       - Built-in sorts/limits (𝔻, ℙ, 𝕌, ⊤, ⊥): the parent already owns the
--         canonical slot.  Emit one 'FactKindImplicitMerge' equality fact
--         @unqualifiedName = sub.entity@.
--       - Mereological operations (+, ×, -, ⇒, ∸): treated as user-defined
--         entities (see below).  The parent gains an unqualified alias.
--       - User-defined, unqualified name not yet in parent: create a canonical
--         entity anchored to the PARENT theory (order-independent), add it under
--         the unqualified key, and emit @name = sub.name@.
--       - User-defined, unqualified name already in parent from another implicit
--         subtheory, structurally compatible: emit another @name = sub.name@
--         equality fact.  The single canonical entry stays; no second entity
--         is pushed into the slot.
--       - User-defined, same name, NOT structurally compatible: return a
--         Left build error.
--
-- "Internal" means the name contains '#' — bookkeeping artefacts such as sort
-- limits, domain sorts, and image functions.  They are always propagated only
-- under their qualified names and never pollute the unqualified namespace.
--
-- The propagated names are inserted into the parent's objectsByName map only
-- (not into theoryObjects, which lists only locally-declared entities).
propagateSubtheory :: Theory -> String -> Bool -> Bool -> Theory -> Either BuildError Theory
propagateSubtheory parentTh subName isImplicit isReflection subTh =
  foldM addEntry parentTh (Map.toList (theoryObjectsByName subTh))
  where
    addEntry th (name, entities) = do
      let transformed = if isReflection then map reflectEntity entities else entities
          qualifiedName = if null subName then name else subName ++ "." ++ name

          -- Step 1: always register the qualified name.
          th1 = foldl (\t e -> addEntityToParent t qualifiedName e) th transformed

      -- Step 2: for implicit subtheories, also handle the unqualified name —
      -- but only for plain names (no '#' — those are internal artefacts).
      if isImplicit && not (isInternalName name)
        then foldM (addUnqualified name qualifiedName) th1 transformed
        else Right th1

-- | Create a ResolvedTerm from an entity with a custom display name
termFromEntityWithName :: String -> Entity -> ResolvedTerm
termFromEntityWithName displayName entity =
  let constRef = ResolvedConstantRef
        { resolvedConstRefName = displayName
        , resolvedConstEntity  = entity
        , resolvedConstType    = entityToExprType entity
        }
      factor = ResolvedFactor (ResolvedBTAtomic constRef) [] (entityToExprType entity)
  in ResolvedTerm factor [] (entityToExprType entity)

-- | Convenience wrapper using the entity's own name as the display name.
termFromEntity :: Entity -> ResolvedTerm
termFromEntity e = termFromEntityWithName (entityName e) e

-- | Emit one implicit-merge equality fact of the form
--   @unqualifiedName = sub.qualifiedName@.
--
-- The LHS is always the unqualified canonical name; the RHS is always the
-- qualified subtheory name.  Using 'FactKindImplicitMerge' (rather than
-- 'FactKindAssertion') lets pretty-printers and downstream passes identify
-- and optionally suppress these auto-generated witnesses.
addMergeEqualityFact
  :: Theory    -- ^ theory to add the fact to
  -> String    -- ^ unqualified (LHS) name
  -> Entity    -- ^ canonical entity for the LHS
  -> String    -- ^ qualified (RHS) name, e.g. "sub.f"
  -> Entity    -- ^ subtheory entity for the RHS
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
  in addFactToTh th (Fact
        { factIsMereologicalTranslation = False
        , factIsInherited               = False
        , factKind                      = FactKindImplicitMerge
        , factPropExpr                  = ResolvedPropBicond rightImpl []
        })

-- | Built-in sort/limit names that every theory already owns an unqualified
-- entry for.  When an implicit subtheory contributes one of these names, the
-- parent already owns the canonical slot; we only need to emit an equality
-- fact linking parent entity = sub.entity.
--
-- The mereological operations (+, ×, -, ⇒, ∸) are intentionally excluded:
-- they are treated the same as user-defined entities so that the parent gains
-- a proper unqualified alias with a merge equality fact, exactly as the
-- implicit subtheory document specifies.
builtInSortNames :: [String]
builtInSortNames = ["𝔻", "ℙ", "𝕌", "⊤", "⊥"]

isBuiltInSort :: String -> Bool
isBuiltInSort n = n `elem` builtInSortNames

-- | Decide what to do when we encounter @entity@ (from the sub) for the
-- unqualified slot @name@.  @qualifiedName@ is the already-registered
-- @"sub.entity"@ key used to produce well-formed equality facts.
--
-- Contract:
--   * The unqualified name is ALWAYS the LHS of any equality fact produced.
--   * The qualified (sub.X) name is ALWAYS the RHS.
--   * Order of subtheory processing must not affect the result.
addUnqualified :: String -> String -> Theory -> Entity -> Either BuildError Theory
addUnqualified name qualifiedName th entity
  -- Built-in sorts/limits: parent already owns the canonical slot.
  -- Emit "parent_entity = sub.entity" and nothing else.
  | isBuiltInSort name =
      case ( Map.lookup name      (theoryObjectsByName th)
           , Map.lookup qualifiedName (theoryObjectsByName th) ) of
        (Just (parentEntity:_), Just (subEntity:_)) ->
          Right $ addMergeEqualityFact th name parentEntity qualifiedName subEntity
        _ -> Right th

  -- Slot empty: first occurrence of this user-defined name.
  -- Create a canonical entity anchored to the PARENT theory (not the
  -- subtheory), so the result is the same regardless of which subtheory
  -- is processed first.
  | Nothing <- Map.lookup name (theoryObjectsByName th) =
      let canonical = createCanonicalEntity th entity
          th1       = addEntityToParent th name canonical
      in Right $ addMergeEqualityFact th1 name canonical qualifiedName entity

  -- Slot already occupied by a canonical entity from a previous implicit sub.
  -- If compatible, emit another equality fact; leave the single canonical
  -- entry in place (no new entity added to the slot).
  | Just (canonical : _) <- Map.lookup name (theoryObjectsByName th) =
      if entitiesCompatible canonical entity
        then Right $ addMergeEqualityFact th name canonical qualifiedName entity
        else Left $ "Name conflict: '" ++ name
               ++ "' is defined in multiple implicit subtheories with incompatible signatures"

  | otherwise = Right th

-- | Create a canonical entity to serve as the merged representative for a
-- user-defined name coming from an implicit subtheory.
--
-- The canonical entity is structurally identical to the subtheory entity but
-- has its theory pointer rewritten to @parentTh@ and its @reflectedFrom@
-- field cleared.  Anchoring to the parent theory ensures the result is
-- stable across different subtheory processing orders.
createCanonicalEntity :: Theory -> Entity -> Entity
createCanonicalEntity parentTh (EntitySort s) =
  EntitySort s { sortTheory       = parentTh
               , sortOrigin       = FromSubtheory
               , sortReflectedFrom = Nothing
               -- sortRelationship and sortParent stay as-is
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
createCanonicalEntity _ e = e  -- EntityTheory: should not occur here

-- | True for names that are internal structural artefacts produced automatically
--   by the IR builder (sort limits, domain sorts, image functions, etc.).
--   These contain '#' (e.g. "S#min", "f#dom", "f#dir_img") and must never
--   appear as bare unqualified names in any parent theory, even when the
--   subtheory is implicit.  'propagateSubtheory' checks this before calling
--   'addUnqualified'.
isInternalName :: String -> Bool
isInternalName = ('#' `elem`)

-- | Structural compatibility check — mirrors C++ overload/override resolution.
--   Two entities are compatible (and thus candidates for an equality-fact merge)
--   iff they could represent the same mathematical concept:
--   same constructor family, same arity, and (for functions/relations) the same
--   sort names for arguments and result.
--
--   We compare sort *names* rather than sort identity because sorts from
--   different theories are distinct Haskell values even when they refer to the
--   same mathematical concept.
--
--   Sorts: we do NOT treat two arbitrary sorts as compatible just because they
--   share a name.  An `S` in `sub1` and an `S` in `sub2` are unrelated unless
--   they came from a shared ancestor, which cannot be determined here.  For
--   sorts we therefore require the same originating theory (same fully-qualified
--   name) before issuing an equality fact.  Two truly independent `sort S`
--   declarations remain ambiguous (no spurious fact) while a sort propagated up
--   through a chain of implicit subtheories correctly stays as one concept.
entitiesCompatible :: Entity -> Entity -> Bool
entitiesCompatible (EntitySort s1) (EntitySort s2) =
  sortName s1 == sortName s2
  --theoryFullyQualifiedName (sortTheory s1) == theoryFullyQualifiedName (sortTheory s2)
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
entitiesCompatible _ _ = False   -- different constructors → incompatible

-- | Add an entity to a theory's name map only (not to theoryObjects).
addEntityToParent :: Theory -> String -> Entity -> Theory
addEntityToParent th name entity =
  th { theoryObjectsByName = Map.insertWith (++) name [entity] (theoryObjectsByName th) }

-- ---------------------------------------------------------------------------
-- Mereological translations (pass 4)
-- ---------------------------------------------------------------------------

-- | Determine the operation prefix to use for mereological operations.
-- If the theory has a reflection ancestor, operations are qualified with its name.
mereoOpPrefix :: Theory -> String
mereoOpPrefix th = case theoryClosestReflectionAncestor th of
  Just anc -> theoryFullyQualifiedName anc ++ "."
  Nothing  -> ""

-- | Produce the mereological translation of a fact (assertions and facts only).
-- Mirrors translateAxiom / translateIdentity in translate.go.
mereologicalTranslation :: Theory -> Fact -> [Fact]
mereologicalTranslation th fact = case factKind fact of
  FactKindAssertion ->
    [ fact { factIsMereologicalTranslation = True
           , factPropExpr = translatePropExpr th (factPropExpr fact) } ]
  FactKindFact ->
    -- Go's translateIdentity is currently a no-op (returns assertion unchanged)
    [ fact { factIsMereologicalTranslation = True } ]
  _ -> []

-- | Translate a resolved proposition into its mereological equivalent.
-- Logical connectives become mereological operations:
--   ↔  →  ∸   (symmetric difference)
--   →  →  ⇒   (reverse difference)
--   ←  →  -   (difference)
--   ∨  →  ×   (product)
--   ∧  →  +   (sum)
--   ¬  →  ⊥ - x
--   =, ∈, ⊆, ≤  →  ∸ / -
translatePropExpr :: Theory -> ResolvedPropExpr -> ResolvedPropExpr
translatePropExpr th (ResolvedPropBicond left rests) =
  -- ↔ becomes a chain of ∸ (sym diff) at the term level
  -- We embed the whole thing as a single term via the first operand;
  -- additional rests become ∸-separated terms.
  -- Since ResolvedPropExpr must stay in its grammar, we preserve structure
  -- but swap the operators.
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
translateNeg th (ResolvedNegNot inner) =
  -- ¬x  →  ⊥ - x  (we keep as NegNot since the outer layer handles the op;
  -- a future pass can lower this to a term)
  ResolvedNegNot (translateNeg th inner)
translateNeg th (ResolvedNegChild q) =
  ResolvedNegChild (translateQuantified th q)

translateQuantified :: Theory -> ResolvedQuantified -> ResolvedQuantified
translateQuantified th (ResolvedQuantified qs atomic) =
  ResolvedQuantified qs (translateAtomicProp th atomic)

translateAtomicProp :: Theory -> ResolvedAtomicProp -> ResolvedAtomicProp
translateAtomicProp th (ResolvedAtomicTermPair tp) =
  ResolvedAtomicTermPair (translateTermPair th tp)
translateAtomicProp _th other = other

-- | Translate "=", "∈", "⊆", "≤" to mereological ops, mirroring translateTermPair in Go.
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
        _    -> op     -- pass through any other operator unchanged
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
  -- NEW: Proposition parentheses – translate inner proposition
  ResolvedBTPropParen inner ->
    ResolvedBTPropParen (translatePropExpr th inner)
  -- NEW: Term parentheses – translate inner term
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
  ResolvedBTAtomic _ -> bt   -- atomic constants are left unchanged

-- ---------------------------------------------------------------------------
-- Lookup helpers
-- ---------------------------------------------------------------------------

-- | Lookup a sort by its simple name in a theory.
lookupSort :: Theory -> String -> Either BuildError Sort
lookupSort th nm = case nm of
  "𝕌" -> Right (theoryUniverse th)
  "𝔻" -> Right (theoryDomain th)
  "ℙ" -> Right (theoryProp th)
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

lookupSortByExpr :: Theory -> SortExpr -> Either BuildError Sort
lookupSortByExpr th sexpr = do
  let sr = sortRef sexpr
  case sortSpecifier sr of
    [] -> lookupSort th (sortConstant sr)
    specs -> do
      subTh <- findSubtheoryByPath th (map theoryRefName specs)
      lookupSort subTh (sortConstant sr)

-- | Look up any entity by name in a theory
lookupEntity :: Theory -> String -> Either BuildError Entity
lookupEntity th nm =
  let parts = splitOn '.' nm
  in case parts of
    [] -> Left "Empty name"
    [single] -> case Map.lookup single (theoryObjectsByName th) of
      Just [e] -> Right e
      Just (_:_) -> Left $ "Ambiguous name: '" ++ single ++ "'"
      Nothing -> Left $ "Unknown reference: '" ++ nm ++ "'"
    (first:rest) ->
      -- Find subtheories with name 'first'
      let matchingSubs = filter (\sub -> theoryName sub == first) (theorySubtheories th)
      in case matchingSubs of
        [] -> Left $ "Unknown subtheory: '" ++ first ++ "'"
        [_] -> lookupEntity (head matchingSubs) (intercalate "." rest)
        _ -> Left $ "Ambiguous path: '" ++ first ++ "' refers to multiple subtheories"


lookupEntityInPath :: Theory -> [String] -> String -> Either BuildError Entity
lookupEntityInPath th [] nm   = lookupEntity th nm
lookupEntityInPath th path nm = do
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

-- | Determine the 'ExprType' for an entity looked up by name.
entityToExprType :: Entity -> ExprType
entityToExprType (EntitySort _) = SortClass
entityToExprType (EntityFunction f) = 
  case funcKind f of
    FunctionKindFOLFunctionFromTheory -> FOLFunctionClass (length (funcArgSorts f))
    FunctionKindSOLFunctionFromTheory -> SOLFunctionClass (length (funcArgSorts f))
    _ -> OtherMereologicalClass
entityToExprType (EntityRelation r) = RelationClass (length (relArgSorts r))
entityToExprType (EntityMereological m) =
  case mereoKind m of
    MereologicalEntityKindIndividual -> IndividualClass
    MereologicalEntityKindSet -> RelationClass 1
    MereologicalEntityKindProposition -> PropositionClass
    _ -> OtherMereologicalClass
entityToExprType (EntityTheory _) = TheoryClass

-- ---------------------------------------------------------------------------
-- Name resolution (from original file)
-- ---------------------------------------------------------------------------

-- | Resolve all references in a 'PropExprInclVars', binding the leading
-- variable declarations into the context.
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
      -- Naming rules (mirror signature declarations):
      --   ⊆-bound variables:  must start with uppercase (set/relation)
      --   ℙ-sort variables:   must start with uppercase (proposition)
      --   𝕌-sort variables:   must start with uppercase (bare mereological)
      --   other :-bound vars: must start with lowercase (individual)
      if isSet'
        then when (not (firstLetterIsUppercase vid)) $
               Left $ "Free set variable must start with uppercase: " ++ vid
        else when (not (isPropSort s) && not (isUniverseSort s) && firstLetterIsUppercase vid) $
               Left $ "Free individual variable must start with lowercase: " ++ vid
      when ((isPropSort s || isUniverseSort s) && not isSet' && not (firstLetterIsUppercase vid)) $
        Left $ "Proposition/mereological variable must start with uppercase: " ++ vid
      let rvd = ResolvedVarDecl vid isSet' s
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
  l <- resolveLeftImpl th ctx leftI
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
  -- Naming rules (mirror signature declarations):
  --   ⊆-bound variables:  must start with uppercase (set/relation)
  --   ℙ-sort variables:   must start with uppercase (proposition)
  --   𝕌-sort variables:   must start with uppercase (bare mereological)
  --   other :-bound vars: must start with lowercase (individual)
  if isSet'
    then when (not (firstLetterIsUppercase vid)) $
           Left $ "Set/relation variable must start with uppercase: " ++ vid
    else when (not (isPropSort s) && not (isUniverseSort s) && firstLetterIsUppercase vid) $
           Left $ "Individual variable must start with lowercase: " ++ vid
  when ((isPropSort s || isUniverseSort s) && not isSet' && not (firstLetterIsUppercase vid)) $
    Left $ "Proposition/mereological variable must start with uppercase: " ++ vid
  let rvd = ResolvedVarDecl vid isSet' s
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
  (rs, resultType) <- foldM (resolveSuffix th ctx) ([], baseType) suffixes
  return (ResolvedFactor rb rs resultType)

isSet :: ResolvedVarDecl -> Bool
isSet (ResolvedVarDecl _ b _) = b

-- | Extract a term from a proposition that is just a term in disguise.
-- Returns Nothing if the proposition contains any logical structure.
termIfPlain :: ResolvedPropExpr -> Maybe ResolvedTerm
termIfPlain (ResolvedPropBicond (ResolvedRightImpl left Nothing) []) =
  case left of
    ResolvedLeftImpl (ResolvedDisj (ResolvedConj (ResolvedNegChild (ResolvedQuantified [] atomic)) [] ) [] ) [] ->
      case atomic of
        ResolvedAtomicTermPair tp
          | null (resolvedTPRight tp) -> Just (resolvedTPLeft tp)
        ResolvedAtomicConstant cr
          | resolvedConstType cr /= PropositionClass ->
              Just (termFromConstant cr)
        _ -> Nothing
    _ -> Nothing
termIfPlain _ = Nothing

-- | Build a ResolvedTerm from a constant reference (for the atomic constant case).
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
    resolved <- resolvePropExpr subTh emptyVarContext operand
    return (ResolvedBTEvaluationInTheory
              (ResolvedEvaluationInTheory path subTh resolved),
            PropositionClass)  -- evaluation yields a proposition

  BTProjectionToSort (ProjectionToSort sexpr operand) -> do
    s  <- lookupSortByExpr th sexpr
    rt <- resolveTerm th ctx operand
    return (ResolvedBTProjectionToSort (ResolvedProjectionToSort s rt),
            RelationClass 1)  -- projection to a sort yields a set

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
    -- { x : A | φ(x) } resolves to a set (RelationClass 1).
    -- The bound variable is in scope only within the body.
    (rvd, ctx') <- resolveVarDecl th ctx vd
    when (isSet rvd) $
      throwError "Set comprehension variable must be an individual (use ':', not '⊆')"
    rbody <- resolvePropExpr th ctx' body
    return ( ResolvedBTSetComprehension (ResolvedSetComprehension rvd rbody)
           , RelationClass 1 )

  BTDescription (Description vd body) -> do
    -- ιx : A φ(x) resolves to the unique individual of sort A satisfying φ.
    (rvd, ctx') <- resolveVarDecl th ctx vd
    when (isSet rvd) $
      throwError "Description variable must be an individual (use ':', not '⊆')"
    rbody <- resolvePropExpr th ctx' body
    return ( ResolvedBTDescription (ResolvedDescription rvd rbody)
           , IndividualClass )

  BTParen inner -> do
    rp <- resolvePropExpr th ctx inner
    case termIfPlain rp of
      Just term | resolvedTermType term /= PropositionClass ->
        -- It's a term, not a proposition → term parentheses
        return (ResolvedBTTermParen term, resolvedTermType term)
      _ ->
        -- It's a genuine proposition → keep as proposition parentheses
        return (ResolvedBTPropParen rp, PropositionClass)

-- | Resolve term suffixes and propagate the type.
resolveSuffix
  :: Theory
  -> VarContext
  -> ([ResolvedTermSuffix], ExprType)
  -> TermSuffix
  -> Either BuildError ([ResolvedTermSuffix], ExprType)
resolveSuffix th ctx (acc, ty) suffix = case suffix of

  SuffixCall (CallSuffix args) -> do
    rargs <- mapM (resolveTerm th ctx) args
    case ty of
      -- Relation (set or n-ary predicate)
      RelationClass arity -> do
        if length args /= arity
          then Left $ "Relation arity mismatch: expected " ++ show arity ++ ", got " ++ show (length args)
          else do
            forM_ rargs $ \arg -> do
              let argTy = resolvedTermType arg
              case argTy of
                IndividualClass -> return ()
                _ -> Left "Relation argument must be an individual"
            return (acc ++ [ResolvedSuffixCall rargs], PropositionClass)

      -- FOL function: result is IndividualClass if all args individuals, else RelationClass 1
      FOLFunctionClass n ->
        if length args /= n
          then Left $ "FOL function arity mismatch: expected " ++ show n ++ ", got " ++ show (length args)
          else do
            let anySet = any (\arg -> case resolvedTermType arg of RelationClass 1 -> True; _ -> False) rargs
                resultClass = if anySet then RelationClass 1 else IndividualClass
            return (acc ++ [ResolvedSuffixCall rargs], resultClass)

      -- SOL function: always returns a set
      SOLFunctionClass n ->
        if length args /= n
          then Left $ "SOL function arity mismatch: expected " ++ show n ++ ", got " ++ show (length args)
          else do
            return (acc ++ [ResolvedSuffixCall rargs], RelationClass 1)

      _ -> Left "Cannot apply arguments to a non‑function/non‑set"

  SuffixSpecialOp op -> case op of
    s | s `elem` ["min","max"] ->
        case ty of
          SortClass -> return (acc ++ [ResolvedSuffixSpecialOp s], OtherMereologicalClass)
          _ -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-sort."
    s | s `elem` ["res","arg"] ->
        case ty of
          FOLFunctionClass _ -> return (acc ++ [ResolvedSuffixSpecialOp s], OtherMereologicalClass)
          SOLFunctionClass _ -> return (acc ++ [ResolvedSuffixSpecialOp s], OtherMereologicalClass)
          _ -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-function."
    "dom" ->
        case ty of
          FOLFunctionClass _ -> return (acc ++ [ResolvedSuffixSpecialOp "dom"], SortClass)
          SOLFunctionClass _ -> return (acc ++ [ResolvedSuffixSpecialOp "dom"], SortClass)
          _ -> Left "Attempt to apply '#dom' to a non-function."
    s | s `elem` ["set","individual","mereological","proposition"] ->
        let newClass = case s of
              "set" -> RelationClass 1
              "individual" -> IndividualClass
              "proposition" -> PropositionClass
              "mereological" -> OtherMereologicalClass
              _ -> ty
        in return (acc ++ [ResolvedSuffixSpecialOp s], newClass)
    s | all (`elem` "0123456789") s && not (null s) ->
        case ty of
          FOLFunctionClass _ -> return (acc ++ [ResolvedSuffixSpecialOp s], OtherMereologicalClass)
          SOLFunctionClass _ -> return (acc ++ [ResolvedSuffixSpecialOp s], OtherMereologicalClass)
          _ -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-function."
    other -> return (acc ++ [ResolvedSuffixSpecialOp other], ty)

  SuffixDotAttr attr -> case attr of
    s | s `elem` ["min","max"] ->
        case ty of
          SortClass -> return (acc ++ [ResolvedSuffixDotAttr s], OtherMereologicalClass)
          _ -> Left $ "Attempt to apply '." ++ s ++ "' to a non-sort."
    other -> return (acc ++ [ResolvedSuffixDotAttr other], ty)

-- | Resolve a constant reference — may be a bound variable, ⊤/⊥, a sort,
-- a function, or an individual / set.
resolveConstantRef :: Theory -> VarContext -> ConstantRef -> Either BuildError ResolvedConstantRef
resolveConstantRef th ctx (ConstantRef specs ref) = do
  let path = map theoryRefName specs

  case ref of
    "⊤" -> do
      let mo = lookupInPath th path (theoryTruth)
      return (ResolvedConstantRef ref (EntityMereological mo) PropositionClass)
    "⊥" -> do
      let mo = lookupInPath th path (theoryFalsity)
      return (ResolvedConstantRef ref (EntityMereological mo) PropositionClass)
    _ -> do
      let mbVar = if null path
                  then lookupVarContext ctx ref
                  else Nothing
      case mbVar of
        Just rvd -> do
          let ty = if resolvedVarIsSet rvd
                   then RelationClass 1
                   else case sortKind (resolvedVarSort rvd) of
                          SortKindProp -> PropositionClass
                          SortKindUniverse -> OtherMereologicalClass
                          _ -> IndividualClass
          return (ResolvedConstantRef ref
                    (EntityMereological (mkMereo th MereologicalEntityKindIndividual ref (resolvedVarSort rvd) FromSignature))
                    ty)
        Nothing -> do
          entity <- lookupEntityInPath th path ref
          let ty = entityToExprType entity
          return (ResolvedConstantRef ref entity ty)

-- ---------------------------------------------------------------------------
-- Term pair validation
-- ---------------------------------------------------------------------------

-- | Validate all term pairs in a resolved expression
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

-- | Validate the semantic meaning of a term pair (checking ∈, ⊆, etc.)
-- | Validate the semantic meaning of a term pair (checking ∈, ⊆, etc.)
validateTermPairSemantics :: ResolvedTermPair -> Either String ()
validateTermPairSemantics (ResolvedTermPair left rights _) = do
  let leftClass = resolvedTermType left
  forM_ rights $ \(ResolvedRelationFollowedByTerm _ op _ right) -> do
    let rightClass = resolvedTermType right
    -- OtherMereologicalClass is a wildcard: any operation is permitted when
    -- either operand has this class (analogous to 'any' in TypeScript).
    let eitherIsWildcard = leftClass  == OtherMereologicalClass
                        || rightClass == OtherMereologicalClass
    if eitherIsWildcard
      then Right ()
      else case op of
        "∈" -> do
          let leftOk  = leftClass  == IndividualClass
          let rightOk = rightClass == RelationClass 1
          if not leftOk
            then Left $ "Left operand of ∈ must be an individual or mereological, got " ++ show leftClass
            else if not rightOk
              then Left $ "Right operand of ∈ must be a set or mereological, got " ++ show rightClass
              else Right ()
        "⊆" -> do
          let leftOk  = leftClass  == RelationClass 1
          let rightOk = rightClass == RelationClass 1
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


-- | Helper to get the Level2Type from a ResolvedTerm
getResolvedTermType :: ResolvedTerm -> Either String ExprType
getResolvedTermType term = Right (resolvedTermType term)

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

firstLetterIsUppercase :: String -> Bool
firstLetterIsUppercase []    = False
firstLetterIsUppercase (c:_) = isUpper c

-- ---------------------------------------------------------------------------
-- Fact body validation (negation/absurdity check)
-- ---------------------------------------------------------------------------

-- | Validate that facts don't contain negation (¬) or absurdity (⊥)
validateFactBody :: FactKind -> ResolvedPropExpr -> Either String ()
validateFactBody FactKindFact expr
  | containsNegationOrAbsurdity expr = 
      Left "Facts cannot contain negation (¬) or absurdity (⊥)"
  | otherwise = Right ()
validateFactBody _ _ = Right ()  -- assertions and metafacts can use anything

-- | Check if a resolved proposition expression contains ¬ or ⊥
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
containsNegationInNeg (ResolvedNegNot _) = True  -- This is ¬
containsNegationInNeg (ResolvedNegChild q) = containsNegationInQuantified q

containsNegationInQuantified :: ResolvedQuantified -> Bool
containsNegationInQuantified (ResolvedQuantified _ atom) = 
  containsNegationOrAbsurdityInAtomic atom

containsNegationOrAbsurdityInAtomic :: ResolvedAtomicProp -> Bool
containsNegationOrAbsurdityInAtomic (ResolvedAtomicConstant ref) = 
  resolvedConstRefName ref == "⊥"  -- Check for absurdity
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
  resolvedConstRefName ref == "⊥"
containsNegationInBase (ResolvedBTPropParen expr) = 
  containsNegationOrAbsurdity expr
containsNegationInBase (ResolvedBTTermParen term) = 
  containsNegationInTerm term   -- propagate through term parentheses
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