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
import           Data.List            (find, isPrefixOf)
import qualified Data.Map.Strict      as Map
import           Data.Maybe           (fromMaybe, isJust, isNothing, mapMaybe)
import           System.FilePath      (takeDirectory)

import           Eidos.AST            hiding (theoryBody, theoryName, funcName, funcDomain, relName)
import qualified Eidos.AST            as AST
import           Eidos.BuildMonad
import           Eidos.ExternalRef
import           Eidos.IR
import           Eidos.Parser         (parseString)
import           Eidos.TypeCheck

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

-- | Build theory using IO (for CLI/main program) - reads files from disk
buildTheoryIO :: TheoryDecl -> IO (Either BuildError Theory)
buildTheoryIO td = runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False) Nothing

-- | Build theory from a file path (IO), using the file's directory as the resolution base
buildTheoryFromFile :: FilePath -> TheoryDecl -> IO (Either BuildError Theory)
buildTheoryFromFile filePath td =
  runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False)
            (Just (takeDirectory filePath))

-- | Build theory using a pure resolver (for testing) - no file IO
buildTheoryPure :: PureResolver -> Maybe String -> TheoryDecl -> Either BuildError Theory
buildTheoryPure resolver baseContext td =
  runReader (runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False) baseContext) resolver

-- | Build theory with an explicit pure resolver function (for testing custom resolvers)
buildTheoryWithResolver
  :: (Maybe String -> String -> Either ExternalRefError ExternalRefResult)
  -> Maybe String
  -> TheoryDecl
  -> Either BuildError Theory
buildTheoryWithResolver resolverFn baseContext td =
  runReader
    (runBuildM (decorateTheoryBody (AST.theoryBody td) Nothing "" False) baseContext)
    (FnResolver resolverFn)

-- ---------------------------------------------------------------------------
-- Core theory builder (polymorphic in m)
-- ---------------------------------------------------------------------------

-- | Build a 'Theory' from a 'TheoryBody'.
decorateTheoryBody
  :: forall m. (MonadExternalRefResolver m)
  => TheoryBody
  -> Maybe Theory
  -> String
  -> Bool
  -> BuildM m Theory
decorateTheoryBody body parentMaybe name isReflection = do

  -- ── Base theory skeleton ──────────────────────────────────────────────
  let th0 = createTheory parentMaybe name isReflection

  -- ── Pass 1: subtheories ───────────────────────────────────────────────
  (th1, subtheories) <- foldM (buildSubtheoryEntry) (th0, []) (sections body)
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
  => (Theory, [Theory])
  -> Section
  -> BuildM m (Theory, [Theory])
buildSubtheoryEntry (th, acc) (SectionSubtheories (SubtheoriesSection entries)) = do
  foldM processEntry (th, acc) entries
buildSubtheoryEntry (th, acc) _ = return (th, acc)

processEntry
  :: forall m. (MonadExternalRefResolver m)
  => (Theory, [Theory])
  -> SubtheoryEntry
  -> BuildM m (Theory, [Theory])
processEntry (th, subs) entry = case entry of
  SubtheoryEntryGroup (SubtheoryGroup kw items) -> do
    foldM (processItem kw) (th, subs) items
  SubtheoryEntryItem item -> do
    let kw = fromMaybe "named" (itemQualifier item)
    processItem kw (th, subs) item

processItem
  :: forall m. (MonadExternalRefResolver m)
  => String
  -> (Theory, [Theory])
  -> SubtheoryItem
  -> BuildM m (Theory, [Theory])
processItem kw (th, subs) item = do
  baseContext <- ask
  
  let subName = case kw of
        "implicit" -> ""
        _ -> fromMaybe "" (itemName item)
  
  when (kw == "implicit" && subName /= "") $
    throwError "Implicit subtheories cannot have names."
  when (kw /= "implicit" && subName == "") $
    throwError "Non-implicit subtheories must have names."
  
  let isRefl = kw == "reflection"
  
  (subBody, extInfo) <- resolveSubtheoryBody baseContext item
  
  let finalName = case extInfo of
        Just (extId, _) -> subName -- never use extId here; always use the alias given in the theory
        Nothing -> subName
  
  let subContext = case extInfo of
        Just (_, FileSystemSource _) -> baseContext  -- Keep same context, content will be read via resolver
        Just (_, MemorySource _) -> baseContext
        Nothing -> baseContext
  
  sub <- local (const subContext) $ 
    decorateTheoryBody subBody (Just th) finalName isRefl
  let th' = addSubtheoryToTheory th sub
  return (th', subs ++ [sub])

-- | Resolve a subtheory definition using the resolver from the monad
resolveSubtheoryBody
  :: forall m. (MonadExternalRefResolver m)
  => Maybe String
  -> SubtheoryItem
  -> BuildM m (TheoryBody, Maybe (String, ExternalRefSource))
resolveSubtheoryBody baseContext item = case itemDef item of
  SubtheoryBody b -> return (b, Nothing)
  
  SubtheoryExternalRef ref -> do
    let refPath = case ref of
          '@':rest -> rest
          _        -> ref
    
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
    return (body, Just (extRefIdentifier res, extRefSource res))

addSubtheoryToTheory :: Theory -> Theory -> Theory
addSubtheoryToTheory th sub =
  th { theorySubtheories = theorySubtheories th ++ [sub] }

-- ---------------------------------------------------------------------------
-- Pass 2 — Signature
-- ---------------------------------------------------------------------------

buildSignatureSection
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> Theory -> Section -> BuildM m Theory
buildSignatureSection th0 th (SectionSignature (SignatureSection items)) = do
  foldM (buildSignatureItem th0) th items
buildSignatureSection _ th _ = return th

buildSignatureItem
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> Theory -> SignatureItem -> BuildM m Theory
buildSignatureItem th0 th item = case item of

  SigSimpleSort (SimpleSortDeclaration nm) ->
    case Map.lookup nm (theoryObjectsByName th) of
      Just _  -> throwError ("duplicate sort declaration: " ++ nm)
      Nothing -> do
        let s = mkSort th SortKindFromSignature nm FromSignature
        return (addEntityToTh th (EntitySort s))

  SigRelationalSort (RelationalSortDeclaration nm rel sortExprAST) -> do
    parentSort <- either throwError return $ 
      lookupSort th (sortConstant (sortRef sortExprAST))
    let s = mkRelatedSort th nm rel parentSort
    return (addEntityToTh th (EntitySort s))

  SigFunction (FunctionDeclaration nm domainExprs codomainExpr) -> do
    argSorts <- mapM (liftLookup (lookupSortByExpr th)) domainExprs
    resSort <- either throwError return $ lookupSortByExpr th codomainExpr
    if firstLetterIsUppercase nm
      then do
        let f = mkSOLFunction th nm FunctionKindSOLFunctionFromTheory argSorts resSort FromSignature
        return (addEntityToTh th (EntityFunction f))
      else do
        let f = mkFOLFunction th nm FunctionKindFOLFunctionFromTheory argSorts resSort FromSignature
        return (addEntityToTh th (EntityFunction f))

  SigIndividual (IndividualDeclaration nm sortExprAST) -> do
    s <- either throwError return $ lookupSortByExpr th sortExprAST
    let mo = mkMereo th MereologicalEntityKindIndividual nm s FromSignature
    return (addEntityToTh th (EntityMereological mo))

  SigSet (SetDeclaration nm domainExprs) -> case domainExprs of
    [sexpr] -> do
      s <- either throwError return $ lookupSortByExpr th sexpr
      let mo = mkMereo th MereologicalEntityKindSet nm s FromSignature
      return (addEntityToTh th (EntityMereological mo))
    _ -> do
      argSorts <- mapM (liftLookup (lookupSortByExpr th)) domainExprs
      let rel = mkRelation th nm argSorts FromSignature
      return (addEntityToTh th (EntityRelation rel))

  SigRelation (RelationDeclaration nm first rest) -> do
    argSorts <- mapM (liftLookup (lookupSortByExpr th)) (first : rest)
    let rel = mkRelation th nm argSorts FromSignature
    return (addEntityToTh th (EntityRelation rel))

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
buildAxSection th0 th axSec = case axSec of
  AxAssertions (AssertionsSection props) ->
    foldM (addPropFact th0 FactKindAssertion) th props
  AxFacts (FactsSection props) ->
    foldM (addPropFact th0 FactKindFact) th props
  AxMetafacts (MetafactsSection props) ->
    foldM (addPropFact th0 FactKindMetafactsFact) th props

addPropFact
  :: forall m. (MonadExternalRefResolver m)
  => Theory -> FactKind -> Theory -> PropExprInclVars -> BuildM m Theory
addPropFact th0 fk th prop = do
  let ctx = emptyVarContext
  (resolvedExpr, _ctx') <- either throwError return $ 
    resolvePropExprInclVars th0 ctx prop
  
  case typeCheckResolvedExpr resolvedExpr of
    Left typeErr -> throwError ("Type error in " ++ show fk ++ ": " ++ typeErr)
    Right _ -> return ()
  
  case validateAllTermPairs resolvedExpr of
    Left opErr -> throwError ("Operation error in " ++ show fk ++ ": " ++ opErr)
    Right _ -> return ()
  
  let fact = Fact
        { factIsMereologicalTranslation = False
        , factIsInherited               = False
        , factKind                      = fk
        , factPropExpr                  = resolvedExpr
        }
  return (th { theoryFacts = theoryFacts th ++ [fact] })

-- ---------------------------------------------------------------------------
-- Theory skeleton construction (pure, no monad needed)
-- ---------------------------------------------------------------------------

-- ... (keep all the existing pure functions: createTheory, mkSort, mkMereo, 
--     mkSOLFunction, mkFOLFunction, mkSortLimitFact, twoTermPropExpr,
--     addEntityToTh, mkRelatedSort, mkRelation, lookupSort, lookupSortByExpr,
--     lookupEntity, lookupEntityInPath, lookupInPath, findSubtheoryByPath,
--     entityToExprType, firstLetterIsUppercase, and all the name resolution
--     functions from the original file) ...

-- The following functions from your original file remain unchanged:
-- createTheory, mkSort, mkMereo, mkSOLFunction, mkFOLFunction, mkSortLimitFact,
-- twoTermPropExpr, addEntityToTh, mkRelatedSort, mkRelation, lookupSort,
-- lookupSortByExpr, lookupEntity, lookupEntityInPath, lookupInPath,
-- findSubtheoryByPath, entityToExprType, firstLetterIsUppercase,
-- resolvePropExprInclVars, resolvePropExpr, resolvePropExprRest,
-- resolveRightImpl, resolveLeftImpl, resolveDisj, resolveConj, resolveNeg,
-- resolveQuantified, resolveVarDecl, resolveAtomicProp, resolveTermPair,
-- resolveRFT, resolveTerm, resolveOFF, resolveFactor, resolveBaseTerm,
-- resolveSuffix, resolveConstantRef, validateAllTermPairs,
-- validateRightImplTermPairs, validateLeftImplTermPairs, validateDisjTermPairs,
-- validateConjTermPairs, validateNegTermPairs, validateQuantifiedTermPairs,
-- validateAtomicPropTermPairs, validateTermPairSemantics, getResolvedTermType


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

      builtins = map EntitySort [universe, domain, prop]
             ++ map EntityMereological [truth, falsity]
             ++ map EntityFunction [sumF, prodF, diffF, revDiffF, symDiffF]

      builtinsByName = Map.fromListWith (++)
        [ (entityName e, [e]) | e <- builtins ]

      builtinFacts =
        [ mkSortLimitFact (sortMax prop)   "≤" (sortMin domain)
        , mkSortLimitFact (theoryTruth th) "=" (sortMin prop)
        , mkSortLimitFact (theoryFalsity th) "=" (sortMax prop)
        ]

  in th

-- ---------------------------------------------------------------------------
-- Smart constructors for IR entities
-- ---------------------------------------------------------------------------

mkSort :: Theory -> EntityKind -> String -> Origin -> Sort
mkSort th k nm orig = Sort
  { sortKind              = k
  , sortTheory            = th
  , sortOrigin            = orig
  , sortMin               = mkSortMin
  , sortMax               = mkSortMax
  , sortName              = nm
  , sortComponentSorts    = []
  , sortAssociatedEntity  = Nothing
  }
  where
    mkSortMin = MereologicalObject
      { mereoKind         = MereologicalEntityKindLowerLimitForSort
      , mereoOrigin       = orig
      , mereoTheory       = th
      , mereoName         = nm ++ "#min"
      , mereoSort         = mkSort th k nm orig
      , mereoLimitForSort = Just (mkSort th k nm orig)
      }
    mkSortMax = MereologicalObject
      { mereoKind         = MereologicalEntityKindUpperLimitForSort
      , mereoOrigin       = orig
      , mereoTheory       = th
      , mereoName         = nm ++ "#max"
      , mereoSort         = mkSort th k nm orig
      , mereoLimitForSort = Just (mkSort th k nm orig)
      }

mkMereo :: Theory -> EntityKind -> String -> Sort -> Origin -> MereologicalObject
mkMereo th k nm s orig = MereologicalObject
  { mereoKind         = k
  , mereoOrigin       = orig
  , mereoTheory       = th
  , mereoName         = nm
  , mereoSort         = s
  , mereoLimitForSort = Nothing
  }

mkSOLFunction :: Theory -> String -> EntityKind -> [Sort] -> Sort -> Origin -> Function
mkSOLFunction th nm k argSorts resSort orig = Function
  { funcKind        = k
  , funcOrigin      = orig
  , funcTheory      = th
  , funcName        = nm
  , funcArgSorts    = argSorts
  , funcResSort     = resSort
  , funcResObject   = mkMereo th MereologicalEntityKindResultOfSOLFunction (nm ++ "#res") resSort orig
  , funcArgObjects  = zipWith (\s i -> mkMereo th MereologicalEntityKindArgumentOfSOLFunction
                                        (nm ++ "#" ++ show i) s orig) argSorts [1..]
  , funcDomain      = Nothing
  , funcArgument    = Nothing
  , funcDirectImage = Nothing
  , funcInverseImage = Nothing
  }

mkFOLFunction :: Theory -> String -> EntityKind -> [Sort] -> Sort -> Origin -> Function
mkFOLFunction th nm k argSorts resSort orig =
  let f = mkSOLFunction th nm k argSorts resSort orig
      domSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = orig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (nm ++ "#dom#min") domSort orig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (nm ++ "#dom#max") domSort orig
        , sortName             = ""
        , sortComponentSorts   = argSorts
        , sortAssociatedEntity = Just (EntityFunction f)
        }
      domArg = mkMereo th MereologicalEntityKindArgumentOfSOLFunction (nm ++ "#arg") domSort orig
  in f { funcDomain   = Just domSort
       , funcArgument = Just domArg
       }

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
    mereoExprType mo = termTypeMereological (Just (kindToSubtype (mereoKind mo))) (Just (mereoSort mo))
    kindToSubtype MereologicalEntityKindIndividual   = MereologicalSubtypeIndividual
    kindToSubtype MereologicalEntityKindSet          = MereologicalSubtypeSet
    kindToSubtype MereologicalEntityKindProposition  = MereologicalSubtypeProposition
    kindToSubtype _                                  = MereologicalSubtypeMereological

-- | Add an entity to the theory's object lists and name map
addEntityToTh :: Theory -> Entity -> Theory
addEntityToTh th e =
  th { theoryObjects     = theoryObjects th ++ [e]
     , theoryObjectsByName = Map.insertWith (++) (entityName e) [e]
                               (theoryObjectsByName th)
     }

-- | Build a sort that stands in a relational position to an existing sort
mkRelatedSort :: Theory -> String -> String -> Sort -> Sort
mkRelatedSort th nm _rel _parentSort =
  mkSort th SortKindFromSignature nm FromSignature

mkRelation :: Theory -> String -> [Sort] -> Origin -> Relation
mkRelation th nm argSorts orig =
  let domSort = Sort
        { sortKind             = SortKindProduct
        , sortTheory           = th
        , sortOrigin           = orig
        , sortMin              = mkMereo th MereologicalEntityKindLowerLimitForSort (nm ++ "#dom#min") domSort orig
        , sortMax              = mkMereo th MereologicalEntityKindUpperLimitForSort (nm ++ "#dom#max") domSort orig
        , sortName             = ""
        , sortComponentSorts   = argSorts
        , sortAssociatedEntity = Just (EntityRelation rel)
        }
      domArg = mkMereo th MereologicalEntityKindIndividual (nm ++ "#arg") domSort orig
      assocSet = mkMereo th MereologicalEntityKindSet nm (head argSorts) orig
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
        }
  in rel

-- ---------------------------------------------------------------------------
-- Mereological translations (pass 4)
-- ---------------------------------------------------------------------------

-- | Produce the mereological translation of a fact (assertions and facts only).
mereologicalTranslation :: Theory -> Fact -> [Fact]
mereologicalTranslation _th fact = case factKind fact of
  FactKindAssertion ->
    [ fact { factIsMereologicalTranslation = True } ]
  FactKindFact ->
    [ fact { factIsMereologicalTranslation = True } ]
  _ -> []

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
lookupEntity th nm = case Map.lookup nm (theoryObjectsByName th) of
  Just (e:_) -> Right e
  _          -> Left $ "Unknown reference: '" ++ nm ++ "' in theory '" ++ theoryName th ++ "'"

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
entityToExprType (EntitySort _)         = termTypeSort
entityToExprType (EntityFunction f)     = termTypeFunction (length (funcArgSorts f))
entityToExprType (EntityMereological m) =
  let sub = case mereoKind m of
              MereologicalEntityKindIndividual  -> Just MereologicalSubtypeIndividual
              MereologicalEntityKindSet         -> Just MereologicalSubtypeSet
              MereologicalEntityKindProposition -> Just MereologicalSubtypeProposition
              _                                 -> Just MereologicalSubtypeMereological
  in termTypeMereological sub (Just (mereoSort m))
entityToExprType (EntityRelation r)     = termTypeMereological (Just MereologicalSubtypeSet) (Just (relDomain r))
entityToExprType (EntityTheory _)       = termTypeMereological Nothing Nothing

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
resolvePropExprInclVars th ctx (PropExprInclVars vars propExprAST) = do
  ctx' <- foldM resolveAndBindVar ctx vars
  resolved <- resolvePropExpr th ctx' propExprAST
  return (resolved, ctx')
  where
    resolveAndBindVar c (VarDecl vid colonOrSubset sexpr) = do
      s <- lookupSortByExpr th sexpr
      let isSet' = colonOrSubset == "⊆"
          rvd    = ResolvedVarDecl vid isSet' s
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
  let rvd = ResolvedVarDecl vid (cos == "⊆") s
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
            termTypeMereological (Just MereologicalSubtypeProposition) Nothing)

  BTProjectionToSort (ProjectionToSort sexpr operand) -> do
    s  <- lookupSortByExpr th sexpr
    rt <- resolveTerm th ctx operand
    return (ResolvedBTProjectionToSort (ResolvedProjectionToSort s rt),
            termTypeMereological (Just MereologicalSubtypeSet) (Just s))

  BTProjectionToInterval (ProjectionToInterval lo hi operand) -> do
    rl <- resolveTerm th ctx lo
    rh <- resolveTerm th ctx hi
    rt <- resolveTerm th ctx operand
    return (ResolvedBTProjectionToInterval (ResolvedProjectionToInterval rl rh rt),
            termTypeMereological Nothing Nothing)

  BTGeneralizedSumOrProduct (GeneralizedSumOrProduct sym var operand) -> do
    (rvar, ctx') <- case var of
      Left vd -> do
        (rvd, c) <- resolveVarDecl th ctx vd
        return (Left rvd, c)
      Right vid -> return (Right vid, ctx)
    rt <- resolveTerm th ctx' operand
    return (ResolvedBTGeneralizedSumOrProduct (ResolvedGeneralizedSumOrProduct sym rvar rt),
            termTypeMereological Nothing Nothing)

  BTSingleton inner -> do
    rt <- resolveTerm th ctx inner
    return (ResolvedBTSingleton rt,
            termTypeMereological (Just MereologicalSubtypeSet) Nothing)

  BTParen inner -> do
    rp <- resolvePropExpr th ctx inner
    return (ResolvedBTParen rp,
            termTypeMereological (Just MereologicalSubtypeProposition) Nothing)

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
    case exprMajorType ty of
      MajorTypeFunction ->
        let numArgs = fromMaybe 0 (exprNumArgs ty)
        in if length args /= numArgs
           then Left $ "Argument count mismatch: expected " ++ show numArgs
                    ++ ", got " ++ show (length args)
           else return (acc ++ [ResolvedSuffixCall rargs],
                        termTypeMereological Nothing Nothing)
      _ -> Left "Attempt to call a non-function."

  SuffixSpecialOp op -> case op of
    s | s `elem` ["min","max"] ->
        case exprMajorType ty of
          MajorTypeSort -> return (acc ++ [ResolvedSuffixSpecialOp s],
                                   termTypeMereological Nothing Nothing)
          _ -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-sort."
    s | s `elem` ["res","arg"] ->
        case exprMajorType ty of
          MajorTypeFunction -> return (acc ++ [ResolvedSuffixSpecialOp s],
                                       termTypeMereological Nothing Nothing)
          _ -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-function."
    "dom" ->
        case exprMajorType ty of
          MajorTypeFunction -> return (acc ++ [ResolvedSuffixSpecialOp "dom"],
                                       termTypeSort)
          _ -> Left "Attempt to apply '#dom' to a non-function."
    s | s `elem` ["set","individual","mereological","proposition"] ->
        return (acc ++ [ResolvedSuffixSpecialOp s],
                termTypeMereological (Just (viewSubtype s)) Nothing)
    s | all (`elem` "0123456789") s && not (null s) ->
        case exprMajorType ty of
          MajorTypeFunction -> return (acc ++ [ResolvedSuffixSpecialOp s],
                                       termTypeMereological Nothing Nothing)
          _ -> Left $ "Attempt to apply '#" ++ s ++ "' to a non-function."
    other -> return (acc ++ [ResolvedSuffixSpecialOp other], ty)

  SuffixDotAttr attr -> case attr of
    s | s `elem` ["min","max"] ->
        case exprMajorType ty of
          MajorTypeSort -> return (acc ++ [ResolvedSuffixDotAttr s],
                                   termTypeMereological Nothing Nothing)
          _ -> Left $ "Attempt to apply '." ++ s ++ "' to a non-sort."
    other -> return (acc ++ [ResolvedSuffixDotAttr other], ty)

  where
    viewSubtype "set"          = MereologicalSubtypeSet
    viewSubtype "individual"   = MereologicalSubtypeIndividual
    viewSubtype "proposition"  = MereologicalSubtypeProposition
    viewSubtype _              = MereologicalSubtypeMereological

-- | Resolve a constant reference — may be a bound variable, ⊤/⊥, a sort,
-- a function, or an individual / set.
resolveConstantRef :: Theory -> VarContext -> ConstantRef -> Either BuildError ResolvedConstantRef
resolveConstantRef th ctx (ConstantRef specs ref) = do
  let path = map theoryRefName specs

  case ref of
    "⊤" -> do
      let mo = lookupInPath th path (theoryTruth)
      return (ResolvedConstantRef ref (EntityMereological mo)
                (termTypeMereological (Just MereologicalSubtypeProposition) Nothing))
    "⊥" -> do
      let mo = lookupInPath th path (theoryFalsity)
      return (ResolvedConstantRef ref (EntityMereological mo)
                (termTypeMereological (Just MereologicalSubtypeProposition) Nothing))
    _ -> do
      let mbVar = if null path
                  then lookupVarContext ctx ref
                  else Nothing
      case mbVar of
        Just rvd -> do
          let ty = if resolvedVarIsSet rvd
                   then termTypeMereological (Just MereologicalSubtypeSet) (Just (resolvedVarSort rvd))
                   else case sortKind (resolvedVarSort rvd) of
                          SortKindProp     -> termTypeMereological (Just MereologicalSubtypeProposition) Nothing
                          SortKindUniverse -> termTypeMereological Nothing Nothing
                          _                -> termTypeMereological (Just MereologicalSubtypeIndividual)
                                               (Just (resolvedVarSort rvd))
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
validateTermPairSemantics :: ResolvedTermPair -> Either String ()
validateTermPairSemantics (ResolvedTermPair left rights _) = do
  leftType <- getResolvedTermType left
  forM_ rights $ \(ResolvedRelationFollowedByTerm _ op _ right) -> do
    rightType <- getResolvedTermType right
    let leftWithAny = (leftType, False)
    let rightWithAny = (rightType, False)
    case op of
      "∈" -> do
        if not (acceptIndividualOperand leftWithAny)
          then Left $ "Left operand of ∈ must be an individual, got " ++ show leftType
          else if not (acceptSetOperand rightWithAny)
            then Left $ "Right operand of ∈ must be a set, got " ++ show rightType
            else Right ()
      "⊆" -> do
        if not (acceptSetOperand leftWithAny)
          then Left $ "Left operand of ⊆ must be a set, got " ++ show leftType
          else if not (acceptSetOperand rightWithAny)
            then Left $ "Right operand of ⊆ must be a set, got " ++ show rightType
            else Right ()
      "≤" -> Right ()
      "=" -> Right ()
      _ -> Left $ "Unknown operator: " ++ op

-- | Helper to get the Level2Type from a ResolvedTerm
getResolvedTermType :: ResolvedTerm -> Either String Level2Type
getResolvedTermType term = do
  let ty = resolvedTermType term
  case exprMajorType ty of
    MajorTypeMereologicalObject ->
      case exprMereoSubtype ty of
        Just MereologicalSubtypeIndividual -> Right L2Individual
        Just MereologicalSubtypeSet -> Right L2Set
        Just MereologicalSubtypeProposition -> Right L2Proposition
        Just MereologicalSubtypeMereological -> Right L2BareMereological
        Nothing -> Right L2BareMereological
    MajorTypeFunction -> Right (L2Function (fromMaybe 0 (exprNumArgs ty)))
    MajorTypeSort -> Right L2Sort

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

firstLetterIsUppercase :: String -> Bool
firstLetterIsUppercase []    = False
firstLetterIsUppercase (c:_) = isUpper c