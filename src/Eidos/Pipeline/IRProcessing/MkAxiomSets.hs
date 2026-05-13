-- | Generation of 'AxiomSet' values from an Eidos 'IR.Theory'.
--
-- This is the backend-agnostic stage of the pipeline:
--
-- @
-- IR.Theory  →  [AxiomSet]  →  (backend-specific rendering)
-- @
--
-- Every axiom that any backend emits has a corresponding 'AxiomSet' here,
-- with the same logical content expressed via 'AxiomBody' rather than any
-- backend-specific expression type.  A backend calls 'theoryBlocks' and
-- converts each 'AxiomBody' to its target syntax.
module Eidos.Pipeline.IRProcessing.MkAxiomSets
  ( mkAxiomSets
  , theoryBlocks
  ) where

import           Data.Maybe (fromJust)
import qualified Eidos.Pipeline.FromSyntax.IR as IR
import qualified Eidos.Pipeline.PipelineCore as PL
import qualified Eidos.Pipeline.IRProcessing.SortBounds as SB
import qualified Eidos.Pipeline.IRProcessing.FunctionFacts as FF
import           Eidos.Pipeline.IRProcessing.AxiomSet
import qualified Eidos.Pipeline.IRProcessing.MereologicalOpDefs as MOD

-- ---------------------------------------------------------------------------
-- Naming helpers
-- ---------------------------------------------------------------------------

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

sortMinName, sortMaxName :: String -> String
sortMinName s = s ++ minSuffix
sortMaxName s = s ++ maxSuffix

uSortName, pSortName, dSortName :: String
uSortName = "𝕌"
pSortName = "ℙ"
dSortName = "𝔻"

uMinName, uMaxName, pMinName, pMaxName, dMinName, dMaxName :: String
uMinName = sortMinName uSortName   -- "𝕌_Min"
uMaxName = sortMaxName uSortName   -- "𝕌_Max"
pMinName = sortMinName pSortName   -- "ℙ_Min"
pMaxName = sortMaxName pSortName   -- "ℙ_Max"
dMinName = sortMinName dSortName   -- "𝔻_Min"
dMaxName = sortMaxName dSortName   -- "𝔻_Max"

sanitizeName :: String -> String
sanitizeName = map (\c -> if c == '#' then '_' else c)

domMinName, domMaxName :: IR.Function -> String
domMinName f = sanitizeName (IR.sortName dom) ++ minSuffix
  where dom = maybe (error "no domain sort") id (IR.funcDomain f)
domMaxName f = sanitizeName (IR.sortName dom) ++ maxSuffix
  where dom = maybe (error "no domain sort") id (IR.funcDomain f)

dirImgName, invImgName :: IR.Function -> String
dirImgName f = IR.funcName f ++ "#dir_img"
invImgName f = IR.funcName f ++ "#inv_img"

piName :: IR.Function -> Int -> String
piName f k = IR.funcName f ++ "_pi_" ++ show k

piInvName :: IR.Function -> Int -> String
piInvName f k = IR.funcName f ++ "_pi_" ++ show k ++ "_inv"

tupleName :: IR.Function -> String
tupleName f = IR.funcName f ++ "_tuple"

irPredicateName :: IR.Function -> String
irPredicateName f = "IR_" ++ IR.funcName f

invName :: IR.Function -> String
invName f = IR.funcName f ++ "_inv"

minSuffixForAxiomNames, maxSuffixForAxiomNames :: String
minSuffixForAxiomNames = "_min"
maxSuffixForAxiomNames = "_max"

-- ---------------------------------------------------------------------------
-- Tag-set helpers
-- ---------------------------------------------------------------------------

tSort, tSet, tIndividual, tFun, tFOL, tSOL :: [Tag]
tSort       = [TagSort, TagDecl]
tSet        = [TagSet,  TagDecl]
tIndividual = [TagIndividual, TagDecl]
tFun        = [TagFunction, TagDecl]
tFOL        = [TagFunction, TagFOLFunction, TagDecl]
tSOL        = [TagFunction, TagSOLFunction, TagDecl]

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Build the complete list of 'AxiomSet' values for one theory.
mkAxiomSets :: PL.PreparedTheory -> [AxiomSet]
mkAxiomSets pt = concat
  [ mereologicalOpDefAxiomSets
  , userAbbrevDefAxiomSets
  , headerAxiomSets
  , userSortLimitAxiomSets
  , productSortLimitAxiomSets
  , relProductSortLimitAxiomSets
  , functionDeclAxiomSets
  , relDeclAxiomSets
  , imageFunctionDeclAxiomSets
  , projectionFunctionDeclAxiomSets
  , projectionInverseDeclAxiomSets
  , tupleFunctionDeclAxiomSets
  , folInverseDeclAxiomSets
  , irPredicateDeclAxiomSets
  , functionArgResultDeclAxiomSets
  , relArgObjectDeclAxiomSets
  , folInverseArgResDeclAxiomSets
  , productArgDeclAxiomSets
  , relArgumentDeclAxiomSets
  , projectionWitnessDeclAxiomSets
  , invImgWitnessDeclAxiomSets
  , mereoDeclAxiomSets
  , propDeclAxiomSets
  , setDeclAxiomSets
  , functionFactAxiomSets
  , individualDeclAxiomSets
  , sortBoundAxiomSets
  , sortOrderAxiomSets
  , userFactAxiomSets
  , implicitMergeAxiomSets
  ]
  where
  theory = PL.ptTheory pt

  usesDomain = IR.theoryUsesDomain theory

  userSorts =
    [ s | IR.EntitySort s <- IR.theoryObjects theory
        , IR.sortKind s == IR.SortKindFromSignature ]

  solFunctions = IR.theorySOLFunctions theory
  folFunctions = IR.theoryFOLFunctions theory

  folSingleArgFunctions =
    filter (\f -> length (IR.funcArgSorts f) == 1
               && IR.funcOrigin f == IR.FromSignature)
           folFunctions

  multiArgFolFunctions =
    filter (\f -> length (IR.funcArgSorts f) > 1
               && IR.funcOrigin f == IR.FromSignature)
           folFunctions

  userDeclaredFolFunctions =
    filter (\f -> IR.funcOrigin f == IR.FromSignature) folFunctions

  individualObjects =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindIndividual
        , IR.mereoOrigin m == IR.FromSignature
        , IR.mereoName   m `notElem` [uMinName, uMaxName]
        ]

  mereoObjects =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindMereological
        , IR.mereoOrigin m == IR.FromSignature
        , IR.mereoName   m `notElem` [uMinName, uMaxName]
        ]

  propObjects =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindProposition
        , IR.mereoOrigin m == IR.FromSignature
        , IR.mereoName   m `notElem` [pMinName, pMaxName, "⊤", "⊥"]
        ]

  setObjects =
    if usesDomain
    then [ m | IR.EntityMereological m <- IR.theoryObjects theory
             , IR.mereoKind   m == IR.MereologicalEntityKindSet
             , IR.mereoOrigin m == IR.FromSignature
             , IR.sortKind  (IR.mereoSort m) == IR.SortKindDomain
             , IR.sortName  (IR.mereoSort m) == dSortName
             ]
    else []

  userSortSets =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindSet
        , IR.mereoOrigin m == IR.FromSignature
        , IR.sortKind  (IR.mereoSort m) == IR.SortKindFromSignature
        ]

  userRelations =
    [ r | IR.EntityRelation r <- IR.theoryObjects theory
        , IR.relOrigin r == IR.FromSignature
        ]

  relDomMinName r = sanitizeName (IR.sortName (IR.relDomain r)) ++ minSuffix
  relDomMaxName r = sanitizeName (IR.sortName (IR.relDomain r)) ++ maxSuffix

  translationOfFacts =
    [ f | f <- IR.theoryFacts theory
        , IR.factCategory (IR.factKind f) == IR.FCMereologicalTranslation
        , IR.factSubkind  (IR.factKind f) == IR.FSTranslationOfFact
        ]

  translationOfAssertions =
    [ f | f <- IR.theoryFacts theory
        , IR.factCategory (IR.factKind f) == IR.FCMereologicalTranslation
        , IR.factSubkind  (IR.factKind f) == IR.FSTranslationOfAssertion
        ]

  translationOfMetafacts =
    [ f | f <- IR.theoryFacts theory
        , IR.factCategory (IR.factKind f) == IR.FCMereologicalTranslation
        , IR.factSubkind  (IR.factKind f) == IR.FSTranslationOfMetafact
        ]

  implicitMergeFacts =
    [ f | f <- IR.theoryFacts theory
        , IR.factCategory (IR.factKind f) == IR.FCImplicitMerge
        ]

  -- -------------------------------------------------------------------------
  -- 0. Per-theory definitions of the five built-in mereological operations.
  --    These are emitted as def/Definition (not axiom/Axiom) by backends.
  -- -------------------------------------------------------------------------
  mereologicalOpDefAxiomSets :: [AxiomSet]
  mereologicalOpDefAxiomSets = map mkOpDef (PL.ptMereologicalOpDefs pt)
    where
      mkOpDef entry =
        axiomSet [SGlobal] (tags [TagMereologicalOpDef])
          [(MOD.modDefName entry, ABDef (MOD.modParams entry) (MOD.modBody entry))]

  -- -------------------------------------------------------------------------
  -- 0b. User-defined abbreviations from abbreviations { } sections.
  --     Emitted as def/Definition (not axiom/Axiom) by backends.
  -- -------------------------------------------------------------------------
  userAbbrevDefAxiomSets :: [AxiomSet]
  userAbbrevDefAxiomSets = map mkAbbrevDef (PL.ptUserAbbrevDefs pt)
    where
      mkAbbrevDef ad =
        axiomSet [SGlobal] (tags [TagUserAbbrevDef])
          [(IR.abbrevName ad, ABDef (IR.abbrevParams ad) (IR.abbrevBody ad))]

  -- -------------------------------------------------------------------------
  -- 1. Header: U/P (and optionally D) limit objects
  -- -------------------------------------------------------------------------
  headerAxiomSets :: [AxiomSet]
  headerAxiomSets =
    [ axiomSet [SSort uSortName] (tags tSort)
        [ (uMinName, ABDeclProp)
        , (uMaxName, ABDeclProp)
        ]
    , axiomSet [SSort pSortName] (tags tSort)
        [ (pMinName, ABDeclProp)
        , (pMaxName, ABDeclProp)
        ]
    ] ++
    [ axiomSet [SSort dSortName] (tags tSort)
        [ (dMinName, ABDeclProp)
        , (dMaxName, ABDeclProp)
        ]
    | usesDomain
    ]

  -- -------------------------------------------------------------------------
  -- 2. User sort limit objects: S_Min, S_Max
  -- -------------------------------------------------------------------------
  userSortLimitAxiomSets :: [AxiomSet]
  userSortLimitAxiomSets = map mkSortLimits userSorts
    where
      mkSortLimits s =
        axiomSet [SSort (IR.sortName s)] (tags tSort)
          [ (sortMinName (IR.sortName s), ABDeclProp)
          , (sortMaxName (IR.sortName s), ABDeclProp)
          ]

  -- -------------------------------------------------------------------------
  -- 3. Product sort limit objects: f_dom_Min, f_dom_Max
  -- -------------------------------------------------------------------------
  productSortLimitAxiomSets :: [AxiomSet]
  productSortLimitAxiomSets = map mkLimits multiArgFolFunctions
    where
      mkLimits f =
        axiomSet [SFunction (IR.funcName f), STuple]
                 (tags [TagFunction, TagFOLFunction, TagTuple, TagDecl])
          [ (domMinName f, ABDeclProp)
          , (domMaxName f, ABDeclProp)
          ]

  -- -------------------------------------------------------------------------
  -- 4. Function declarations (SOL + user FOL)
  -- -------------------------------------------------------------------------
  functionDeclAxiomSets :: [AxiomSet]
  functionDeclAxiomSets =
       map mkSOLDecl solFunctions
    ++ map mkFOLDecl userDeclaredFolFunctions
    where
      mkSOLDecl f =
        axiomSet [SFunction (IR.funcName f)] (tags tSOL)
          [(IR.funcName f, funcArity f)]
      mkFOLDecl f =
        axiomSet [SFunction (IR.funcName f)] (tags tFOL)
          [(IR.funcName f, funcArity f)]
      funcArity f =
        let n = length (IR.funcArgObjects f)
        in if n == 0 then ABDeclProp else ABDeclFunc n

  -- -------------------------------------------------------------------------
  -- 5. Image function declarations: f#dir_img, f#inv_img
  -- -------------------------------------------------------------------------
  imageFunctionDeclAxiomSets :: [AxiomSet]
  imageFunctionDeclAxiomSets = concatMap mkImgDecls multiArgFolFunctions
    where
      mkImgDecls f =
        [ axiomSet [SFunction (IR.funcName f), SImage]
                   (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
            [(dirImgName f, ABDeclFunc 1)]
        , axiomSet [SFunction (IR.funcName f), SImage]
                   (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
            [(invImgName f, ABDeclFunc 1)]
        ]

  -- -------------------------------------------------------------------------
  -- 6. Projection function declarations: f_pi_1, f_pi_2, ...
  -- -------------------------------------------------------------------------
  projectionFunctionDeclAxiomSets :: [AxiomSet]
  projectionFunctionDeclAxiomSets = concatMap mkProjDecls multiArgFolFunctions
    where
      mkProjDecls f =
        [ axiomSet [SFunction (IR.funcName f), SProjection k]
                   (tags [TagFunction, TagFOLFunction, TagProjection, TagDecl])
            [(piName f k, ABDeclFunc 1)]
        | k <- [1 .. length (IR.funcArgSorts f)]
        ]

  -- -------------------------------------------------------------------------
  -- 7. Inverse projection declarations: f_pi_1_inv, f_pi_2_inv, ...
  -- -------------------------------------------------------------------------
  projectionInverseDeclAxiomSets :: [AxiomSet]
  projectionInverseDeclAxiomSets = concatMap mkProjInvDecls multiArgFolFunctions
    where
      mkProjInvDecls f =
        [ axiomSet [SFunction (IR.funcName f), SProjection k, SInverse]
                   (tags [TagFunction, TagFOLFunction, TagProjection, TagInverse, TagDecl])
            [(piInvName f k, ABDeclFunc 1)]
        | k <- [1 .. length (IR.funcArgSorts f)]
        ]

  -- -------------------------------------------------------------------------
  -- 8. Tuple function declarations: f_tuple
  -- -------------------------------------------------------------------------
  tupleFunctionDeclAxiomSets :: [AxiomSet]
  tupleFunctionDeclAxiomSets = map mkTupleDecl multiArgFolFunctions
    where
      mkTupleDecl f =
        let arity = length (IR.funcArgSorts f)
        in axiomSet [SFunction (IR.funcName f), STuple]
                    (tags [TagFunction, TagFOLFunction, TagTuple, TagDecl])
             [(tupleName f, ABDeclFunc arity)]

  -- -------------------------------------------------------------------------
  -- 9. FOL inverse declarations: g_inv, h_inv, ...
  -- -------------------------------------------------------------------------
  folInverseDeclAxiomSets :: [AxiomSet]
  folInverseDeclAxiomSets = map mkInvDecl folSingleArgFunctions
    where
      mkInvDecl f =
        axiomSet [SFunction (IR.funcName f), SInverse]
                 (tags [TagFunction, TagFOLFunction, TagInverse, TagDecl])
          [(invName f, ABDeclFunc 1)]

  -- -------------------------------------------------------------------------
  -- 10. IR predicate declarations: IR_f
  -- -------------------------------------------------------------------------
  irPredicateDeclAxiomSets :: [AxiomSet]
  irPredicateDeclAxiomSets = map mkIRDecl multiArgFolFunctions
    where
      mkIRDecl f =
        axiomSet [SFunction (IR.funcName f), SIR]
                 (tags [TagFunction, TagFOLFunction, TagIR, TagDecl])
          [(irPredicateName f, ABDeclFunc 1)]

  -- -------------------------------------------------------------------------
  -- 11. Function argument/result object declarations
  -- -------------------------------------------------------------------------
  functionArgResultDeclAxiomSets :: [AxiomSet]
  functionArgResultDeclAxiomSets = concatMap mkObjDecls
      (solFunctions ++ userDeclaredFolFunctions)
    where
      mkObjDecls f =
           [ axiomSet [SFunction (IR.funcName f), SArgObject k]
                      (tags tFun)
               [(sanitizeName (IR.mereoName obj), ABDeclProp)]
           | (k, obj) <- zip [1..] (IR.funcArgObjects f)
           ]
        ++ [ axiomSet [SFunction (IR.funcName f), SResObject]
                      (tags tFun)
               [(sanitizeName (IR.mereoName (IR.funcResObject f)), ABDeclProp)]
           ]

  -- -------------------------------------------------------------------------
  -- 12. FOL inverse arg/res object declarations
  -- -------------------------------------------------------------------------
  folInverseArgResDeclAxiomSets :: [AxiomSet]
  folInverseArgResDeclAxiomSets = concatMap mkInvObjDecls folSingleArgFunctions
    where
      mkInvObjDecls f =
        let fInv = invName f
        in [ axiomSet [SFunction (IR.funcName f), SInverse, SArgObject 1]
                      (tags [TagFunction, TagFOLFunction, TagInverse, TagDecl])
               [(fInv ++ "_1", ABDeclProp)]
           , axiomSet [SFunction (IR.funcName f), SInverse, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagInverse, TagDecl])
               [(fInv ++ "_res", ABDeclProp)]
           ]

  -- -------------------------------------------------------------------------
  -- 13. Product arg object declarations: f_arg
  -- -------------------------------------------------------------------------
  productArgDeclAxiomSets :: [AxiomSet]
  productArgDeclAxiomSets = concatMap mkArgDecl multiArgFolFunctions
    where
      mkArgDecl f =
        case IR.funcArgument f of
          Nothing  -> []
          Just arg ->
            let argN = sanitizeName (IR.mereoName arg)
            in [ axiomSet [SFunction (IR.funcName f), STuple, SArgObject 0]
                          (tags [TagFunction, TagFOLFunction, TagTuple, TagDecl])
                   [(argN, ABDeclProp)]
               ]

  -- -------------------------------------------------------------------------
  -- 14. Projection witness declarations: f_pi_k_1, f_pi_k_res
  -- -------------------------------------------------------------------------
  projectionWitnessDeclAxiomSets :: [AxiomSet]
  projectionWitnessDeclAxiomSets = concatMap mkProjWitnesses multiArgFolFunctions
    where
      mkProjWitnesses f = concatMap (mkOne f) [1 .. length (IR.funcArgSorts f)]
        where
          mkOne f k =
            [ axiomSet [SFunction (IR.funcName f), SProjection k, SArgObject 1]
                       (tags [TagFunction, TagFOLFunction, TagProjection, TagDecl])
                [(piName f k ++ "_1", ABDeclProp)]
            , axiomSet [SFunction (IR.funcName f), SProjection k, SResObject]
                       (tags [TagFunction, TagFOLFunction, TagProjection, TagDecl])
                [(piName f k ++ "_res", ABDeclProp)]
            ]

  -- -------------------------------------------------------------------------
  -- 15. Inverse image witness declarations: f#inv_img_arg, f#inv_img_res
  -- -------------------------------------------------------------------------
  invImgWitnessDeclAxiomSets :: [AxiomSet]
  invImgWitnessDeclAxiomSets = concatMap mkWitnesses multiArgFolFunctions
    where
      mkWitnesses f =
        let fN   = invImgName f
            argN = fN ++ "_arg"
            resN = fN ++ "_res"
        in [ axiomSet [SFunction (IR.funcName f), SImage, SArgObject 1]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
               [(argN, ABDeclProp)]
           , axiomSet [SFunction (IR.funcName f), SImage, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
               [(resN, ABDeclProp)]
           ]

  -- -------------------------------------------------------------------------
  -- 16. Mereological (𝕌-sorted) object declarations
  -- -------------------------------------------------------------------------
  mereoDeclAxiomSets :: [AxiomSet]
  mereoDeclAxiomSets = map mkMereoDecl mereoObjects
    where
      mkMereoDecl m =
        axiomSet [SGlobal] (tags [TagDecl])
          [(IR.mereoName m, ABDeclProp)]

  -- -------------------------------------------------------------------------
  -- 17. Propositional (ℙ-sorted) object declarations
  -- -------------------------------------------------------------------------
  propDeclAxiomSets :: [AxiomSet]
  propDeclAxiomSets = map mkPropDecl propObjects
    where
      mkPropDecl m =
        axiomSet [SGlobal] (tags [TagDecl])
          [(IR.mereoName m, ABDeclProp)]

  -- -------------------------------------------------------------------------
  -- 18. 𝔻-sorted set declarations
  -- -------------------------------------------------------------------------
  setDeclAxiomSets :: [AxiomSet]
  setDeclAxiomSets = map mkSetDecl (setObjects ++ userSortSets)
    where
      mkSetDecl m =
        axiomSet [SSet (IR.mereoName m)] (tags tSet)
          [(IR.mereoName m, ABDeclProp)]

  -- -------------------------------------------------------------------------
  -- 19-21 + 36-39. Sort bounds.  Delegates to Pipeline.SortBounds.
  -- -------------------------------------------------------------------------
  sortBoundAxiomSets :: [AxiomSet]
  sortBoundAxiomSets = map sortBoundToAxiomSet (PL.ptSortBounds pt)

  sortBoundToAxiomSet :: SB.SortBoundEntry -> AxiomSet
  sortBoundToAxiomSet entry =
    let (path, tgs) = contextToPathAndTags (SB.sbeContext entry)
    in axiomSet path (tags tgs)
         (map (\(nm, expr) -> (nm, ABMereo expr)) (SB.sbeAxioms entry))

  contextToPathAndTags :: SB.SortBoundContext -> ([SubjectNode], [Tag])
  contextToPathAndTags ctx = case ctx of
    SB.SBCGlobal                      -> ([SGlobal], [TagSorting])
    SB.SBCIndividual n                 -> ([SIndividual n], [TagIndividual, TagSorting])
    SB.SBCSet n                        -> ([SSet n], [TagSet, TagSorting])
    SB.SBCFunctionObj fn               -> ([SFunction fn], [TagFunction, TagSorting])
    SB.SBCFunctionTupleArg fn          -> ([SFunction fn, STuple, SArgObject 0], [TagFunction, TagFOLFunction, TagTuple, TagSorting])
    SB.SBCFunctionImageArg fn          -> ([SFunction fn, SImage, SArgObject 1], [TagFunction, TagFOLFunction, TagImage, TagSorting])
    SB.SBCFunctionImageRes fn          -> ([SFunction fn, SImage, SResObject], [TagFunction, TagFOLFunction, TagImage, TagSorting])
    SB.SBCFunctionInverseArg fn        -> ([SFunction fn, SInverse, SArgObject 1], [TagFunction, TagFOLFunction, TagInverse, TagSorting])
    SB.SBCFunctionInverseRes fn        -> ([SFunction fn, SInverse, SResObject], [TagFunction, TagFOLFunction, TagInverse, TagSorting])
    SB.SBCFunctionProjectionArg fn k   -> ([SFunction fn, SProjection k, SArgObject 1], [TagFunction, TagFOLFunction, TagProjection, TagSorting])
    SB.SBCFunctionProjectionRes fn k   -> ([SFunction fn, SProjection k, SResObject], [TagFunction, TagFOLFunction, TagProjection, TagSorting])
    SB.SBCRelationObj rn               -> ([SSet rn], [TagSet, TagSorting])

  -- -------------------------------------------------------------------------
  -- 22-35 + R6. Function facts.  Delegates to Pipeline.FunctionFacts.
  -- -------------------------------------------------------------------------
  functionFactAxiomSets :: [AxiomSet]
  functionFactAxiomSets = map functionFactToAxiomSet (PL.ptFunctionFacts pt)

  functionFactToAxiomSet :: FF.FunctionFactEntry -> AxiomSet
  functionFactToAxiomSet entry =
    let (path, tgs) = factContextToPathAndTags (FF.ffeContext entry)
    in axiomSet path (tags tgs)
         (map (\(nm, expr) -> (nm, ABMereo expr)) (FF.ffeAxioms entry))

  factContextToPathAndTags :: FF.FunctionFactContext -> ([SubjectNode], [Tag])
  factContextToPathAndTags ctx = case ctx of
    FF.FFCFunctionConnection fn        -> ([SFunction fn],                      [TagFunction, TagConnection])
    FF.FFCInverseConnection  fn        -> ([SFunction fn, SInverse],            [TagFunction, TagFOLFunction, TagInverse, TagConnection])
    FF.FFCDirImageConnection fn        -> ([SFunction fn, SImage],              [TagFunction, TagFOLFunction, TagImage,   TagConnection])
    FF.FFCInvImageConnection fn        -> ([SFunction fn, SImage],              [TagFunction, TagFOLFunction, TagImage,   TagConnection])
    FF.FFCInverseAdjunction  fn        -> ([SFunction fn, SInverse],            [TagFunction, TagFOLFunction, TagInverse, TagAdjunction])
    FF.FFCImageAdjunction    fn        -> ([SFunction fn, SImage],              [TagFunction, TagFOLFunction, TagImage,   TagAdjunction])
    FF.FFCDecomposition      fn        -> ([SFunction fn],                      [TagFunction, TagFOLFunction, TagDecomposition])
    FF.FFCTupleConnection    fn        -> ([SFunction fn, STuple],              [TagFunction, TagFOLFunction, TagTuple,   TagConnection])
    FF.FFCProjectionConnection  fn k   -> ([SFunction fn, SProjection k],       [TagFunction, TagFOLFunction, TagProjection, TagConnection])
    FF.FFCProjectionAdjunction  fn k   -> ([SFunction fn, SProjection k, SInverse], [TagFunction, TagFOLFunction, TagProjection, TagInverse, TagAdjunction])
    FF.FFCTupleInvDecomposition fn     -> ([SFunction fn, STuple],              [TagFunction, TagFOLFunction, TagTuple,   TagInvDecomposition])
    FF.FFCIRTupleWithProjections fn    -> ([SFunction fn, SIR],                 [TagFunction, TagFOLFunction, TagIR, TagIRTupleProj])
    FF.FFCIRProjectionsFromTuple fn    -> ([SFunction fn, SIR],                 [TagFunction, TagFOLFunction, TagIR, TagIRProjFromTuple])
    FF.FFCIRSeparates           fn     -> ([SFunction fn, SIR],                 [TagFunction, TagFOLFunction, TagIR, TagIRSeparates])
    FF.FFCRelBounds             rn     -> ([SSet rn],                           [TagSet, TagSorting])

  -- -------------------------------------------------------------------------
  -- 35b. Individual declarations
  -- -------------------------------------------------------------------------
  individualDeclAxiomSets :: [AxiomSet]
  individualDeclAxiomSets = map mkIndividualDecl individualObjects
    where
      mkIndividualDecl m =
        axiomSet [SIndividual (IR.mereoName m)] (tags tIndividual)
          [(IR.mereoName m, ABDeclProp)]

  -- -------------------------------------------------------------------------
  -- 40-41 + R7. Sort ordering axioms.  Delegates to Pipeline.SortBounds.
  -- -------------------------------------------------------------------------
  sortOrderAxiomSets :: [AxiomSet]
  sortOrderAxiomSets = map sortOrderToAxiomSet (PL.ptSortOrder pt)

  sortOrderToAxiomSet :: SB.SortOrderEntry -> AxiomSet
  sortOrderToAxiomSet entry =
    let (path, tgs) = orderContextToPathAndTags (SB.soeContext entry)
    in axiomSet path (tags tgs)
         (map (\(nm, expr) -> (nm, ABMereo expr)) (SB.soeAxioms entry))

  orderContextToPathAndTags :: SB.SortOrderContext -> ([SubjectNode], [Tag])
  orderContextToPathAndTags ctx = case ctx of
    SB.SOCBuiltinSort n           -> ([SSort n],              [TagSort, TagOrdering])
    SB.SOCUserSort    n           -> ([SSort n],              [TagSort, TagOrdering])
    SB.SOCProductSort fn          -> ([SFunction fn, STuple], [TagSort, TagFunction, TagFOLFunction, TagTuple, TagOrdering])
    SB.SOCRelationProductSort rn  -> ([SSet rn],              [TagSort, TagSet, TagOrdering])

  -- -------------------------------------------------------------------------
  -- R1. Relation product-sort limit declarations
  -- -------------------------------------------------------------------------
  relProductSortLimitAxiomSets :: [AxiomSet]
  relProductSortLimitAxiomSets = map mkLimits userRelations
    where
      mkLimits r =
        axiomSet [SSet (IR.relName r)] (tags tSet)
          [ (relDomMinName r, ABDeclProp)
          , (relDomMaxName r, ABDeclProp)
          ]

  -- -------------------------------------------------------------------------
  -- R2. Relation declarations
  -- -------------------------------------------------------------------------
  relDeclAxiomSets :: [AxiomSet]
  relDeclAxiomSets = map mkRelDecl userRelations
    where
      mkRelDecl r =
        let arity = length (IR.relArgSorts r)
        in axiomSet [SSet (IR.relName r)] (tags tSet)
             [(IR.relName r, ABDeclFunc arity)]

  -- -------------------------------------------------------------------------
  -- R3. Relation arg-object declarations
  -- -------------------------------------------------------------------------
  relArgObjectDeclAxiomSets :: [AxiomSet]
  relArgObjectDeclAxiomSets = concatMap mkArgDecls userRelations
    where
      mkArgDecls r =
        [ axiomSet [SSet (IR.relName r)] (tags tSet)
            [(sanitizeName (IR.mereoName obj), ABDeclProp)]
        | (_, obj) <- zip [1..] (IR.relArgObjects r)
        ]

  -- -------------------------------------------------------------------------
  -- R4. Relation argument-object declaration + bounds
  --
  -- The bounds axioms @argN_min@ and @argN_max@ express
  --   @ℙ_Min → argN → R_dom_Min@  and  @ℙ_Min → R_dom_Max → argN@
  -- which in mereological form is
  --   @MRevDiff MZero (MRevDiff (MVar argN) (MVar dMn))@  and
  --   @MRevDiff MZero (MRevDiff (MVar dMx) (MVar argN))@.
  -- -------------------------------------------------------------------------
  relArgumentDeclAxiomSets :: [AxiomSet]
  relArgumentDeclAxiomSets = map mkArgDecl userRelations
    where
      mkArgDecl r =
        let argN = sanitizeName (IR.mereoName (IR.relArgument r))
            dMn  = relDomMinName r
            dMx  = relDomMaxName r
            pMin = IR.MVar pMinName
        in axiomSet [SSet (IR.relName r)] (tags tSet)
             [ (argN, ABDeclProp)
             , (argN ++ minSuffixForAxiomNames,
                  ABMereo (IR.MRevDiff pMin (IR.MRevDiff (IR.MVar argN) (IR.MVar dMn))))
             , (argN ++ maxSuffixForAxiomNames,
                  ABMereo (IR.MRevDiff pMin (IR.MRevDiff (IR.MVar dMx) (IR.MVar argN))))
             ]

  -- -------------------------------------------------------------------------
  -- 42. User fact axioms
  -- -------------------------------------------------------------------------
  userFactAxiomSets :: [AxiomSet]
  userFactAxiomSets =
    zipWith mkTranslationAS [1..] allTranslationFacts
    where
      allTranslationFacts = translationOfFacts ++ translationOfAssertions ++ translationOfMetafacts
      totalFacts = length allTranslationFacts
      mkLabel idx = "ax" ++ show idx

      mkTranslationAS idx fact =
        axiomSet [SGlobal] (tags [TagUserFact])
          [(mkLabel idx, ABMereo (fromJust (IR.factMereoExpr fact)))]

  -- -------------------------------------------------------------------------
  -- 43. Implicit merge axioms
  -- -------------------------------------------------------------------------
  implicitMergeAxiomSets :: [AxiomSet]
  implicitMergeAxiomSets = concatMap mkMergeAS implicitMergeFacts
    where
      mkMergeAS :: IR.Fact -> [AxiomSet]
      mkMergeAS fact = extractMergeAxioms (fromJust (IR.factPropExpr fact))
        where
          extractMergeAxioms :: IR.ResolvedPropExpr -> [AxiomSet]
          extractMergeAxioms (IR.ResolvedPropBicond left []) = extractFromRightImpl left
          extractMergeAxioms _ = []

          extractFromRightImpl :: IR.ResolvedRightImpl -> [AxiomSet]
          extractFromRightImpl (IR.ResolvedRightImpl leftImpl Nothing) = extractFromLeftImpl leftImpl
          extractFromRightImpl _ = []

          extractFromLeftImpl :: IR.ResolvedLeftImpl -> [AxiomSet]
          extractFromLeftImpl (IR.ResolvedLeftImpl disj []) = extractFromDisj disj
          extractFromLeftImpl _ = []

          extractFromDisj :: IR.ResolvedDisj -> [AxiomSet]
          extractFromDisj (IR.ResolvedDisj conj []) = extractFromConj conj
          extractFromDisj _ = []

          extractFromConj :: IR.ResolvedConj -> [AxiomSet]
          extractFromConj (IR.ResolvedConj neg []) = extractFromNeg neg
          extractFromConj _ = []

          extractFromNeg :: IR.ResolvedNeg -> [AxiomSet]
          extractFromNeg (IR.ResolvedNegChild quant) = extractFromQuantified quant
          extractFromNeg _ = []

          extractFromQuantified :: IR.ResolvedQuantified -> [AxiomSet]
          extractFromQuantified (IR.ResolvedQuantified [] atomic) = extractFromAtomic atomic
          extractFromQuantified _ = []

          extractFromAtomic :: IR.ResolvedAtomicProp -> [AxiomSet]
          extractFromAtomic (IR.ResolvedAtomicTermPair tp) = extractFromTermPair tp
          extractFromAtomic _ = []

          extractFromTermPair :: IR.ResolvedTermPair -> [AxiomSet]
          extractFromTermPair (IR.ResolvedTermPair lhs rights _) =
            case rights of
              [rfbt] | IR.resolvedRFTOp rfbt == "=" ->
                case (getTermName lhs, getTermName (IR.resolvedRFTRight rfbt)) of
                  (Just lName, Just rName) -> emitMergeAxiom lName rName
                  _ -> []
              _ -> []

          getTermName :: IR.ResolvedTerm -> Maybe String
          getTermName (IR.ResolvedTerm (IR.ResolvedFactor (IR.ResolvedBTAtomic ref) [] _) [] _) =
            Just (resolveConstRef ref)
          getTermName _ = Nothing

          emitMergeAxiom :: String -> String -> [AxiomSet]
          emitMergeAxiom lhsName rhsName =
            let axName = mergeAxiomName lhsName rhsName
            in case IR.factSubkind (IR.factKind fact) of
              IR.FSImplicitMergeFunction ->
                [ axiomSet [SGlobal] (tags [TagImplicitMerge])
                    [(axName, ABFuncEq lhsName rhsName)]
                ]
              _ ->
                [ axiomSet [SGlobal] (tags [TagImplicitMerge])
                    [(axName, ABMereo (fromJust (IR.factMereoExpr fact)))]
                ]

      mergeAxiomName :: String -> String -> String
      mergeAxiomName lhsName rhsName =
        concatMap safeMergeChar lhsName ++ "_from_" ++ subtheoryFromRhs rhsName

      subtheoryFromRhs :: String -> String
      subtheoryFromRhs rhsName =
        case reverse (splitOnDot rhsName) of
          (_entity : revPath) -> map dotToUnderscore
                                    (concatMap (\(i,s) -> if i==0 then s else '.':s)
                                               (zip [0..] (reverse revPath)))
          []                  -> "unknown"

      splitOnDot :: String -> [String]
      splitOnDot "" = []
      splitOnDot s  = let (h, t) = break (== '.') s
                      in h : case t of { [] -> []; (_:rest) -> splitOnDot rest }

      dotToUnderscore :: Char -> Char
      dotToUnderscore '.' = '_'
      dotToUnderscore c   = c

      safeMergeChar :: Char -> String
      safeMergeChar c = case c of
        '+' -> "plus"; '-' -> "minus"; '×' -> "times"
        '⇒' -> "impl"; '∸' -> "sub";  '/' -> "div"
        '#' -> "_";    '.' -> "_";    _   -> [c]

      resolveConstRef :: IR.ResolvedConstantRef -> String
      resolveConstRef = resolveName . IR.resolvedConstRefName

      resolveName :: String -> String
      resolveName n = case n of
        "⊤" -> pMinName
        "⊥" -> pMaxName
        _   -> sanitizeName n

-- ---------------------------------------------------------------------------
-- Flat post-order block list
-- ---------------------------------------------------------------------------

-- | Collect all theories in the tree rooted at the given 'PreparedTheory'
-- into a flat, post-ordered list of @(namespace, axiomSets)@ pairs.
--
-- Post-order (children before parents) ensures that cross-namespace
-- references from a parent to a child are always forward-declared.
--
-- Every theory — including the root — is assigned its
-- 'IR.theoryFullyQualifiedName' as its namespace identifier, so all output
-- is wrapped in a @namespace@\/@end@ (or @Module@\/@End@) block.
-- Reflection subtheories are skipped.
theoryBlocks :: PL.PreparedTheory -> [(String, [AxiomSet])]
theoryBlocks pt =
  childBlocks ++ [rootBlock]
  where
    theory      = PL.ptTheory pt
    rootFqn     = IR.theoryFullyQualifiedName theory
    rootBlock   = (if null rootFqn then "__main__" else rootFqn, mkAxiomSets pt)
    childBlocks = concatMap subBlocks (IR.theorySubtheories theory)

    subBlocks :: IR.Theory -> [(String, [AxiomSet])]
    subBlocks sub
      | IR.theoryReflection sub = []
      | otherwise =
          concatMap subBlocks (IR.theorySubtheories sub)
          ++ [(IR.theoryFullyQualifiedName sub, mkAxiomSets (PL.prepareTheory (PL.ptOptions pt) sub))]
