-- | Generation of 'AxiomSet' values from an Eidos 'IR.Theory'.
--
-- This module implements the first stage of the refactored pipeline:
--
-- @
-- IR.Theory  →  [AxiomSet]  →  LeanDoc  →  String
-- @
--
-- Every axiom that 'Eidos.Backend.LeanProps.LeanProps.theoryToLeanDoc' currently emits
-- has a corresponding 'AxiomSet' here, with the same logical content but
-- enriched with a 'SubjectPath' and a 'TagSet' that make it introspectable
-- without parsing 'LeanExpr' trees.
module Eidos.Backend.LeanProps.MkAxiomSets
  ( mkAxiomSets
  , theoryBlocks
  ) where

import           Data.Maybe (fromJust)
import qualified Eidos.IR as IR
import qualified Eidos.Pipeline as PL
import qualified Eidos.Pipeline.SortBounds as SB
import qualified Eidos.Pipeline.FunctionFacts as FF
import Eidos.Backend.LeanProps.LeanExpr
import Eidos.Backend.LeanProps.LeanAxiomSet

-- ---------------------------------------------------------------------------
-- Naming helpers (kept in sync with LeanProps)
-- ---------------------------------------------------------------------------

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

sortMinName, sortMaxName :: String -> String
sortMinName s = s ++ minSuffix
sortMaxName s = s ++ maxSuffix

-- | Canonical names for the three built-in sorts.
-- These are the single source of truth; change here to rename a sort globally.
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

pMin :: LeanExpr
pMin = LVar pMinName

sanitizeName :: String -> String
sanitizeName = map (\c -> if c == '#' then '_' else c)

domMinName, domMaxName :: IR.Function -> String
domMinName f = sanitizeName (IR.sortName dom) ++ minSuffix
  where dom = maybe (error "no domain sort") id (IR.funcDomain f)
domMaxName f = sanitizeName (IR.sortName dom) ++ maxSuffix
  where dom = maybe (error "no domain sort") id (IR.funcDomain f)

dirImgName, invImgName :: IR.Function -> String
dirImgName f = IR.funcName f ++ "_dir_img"
invImgName f = IR.funcName f ++ "_inv_img"

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

sortBounds :: String -> (String, String)
sortBounds sortN
  | sortN == pSortName = (pMinName, pMaxName)
  | sortN == uSortName = (uMinName, uMaxName)
  | sortN == dSortName = (dMinName, dMaxName)
  | otherwise          = let n = sanitizeName sortN in (n ++ minSuffix, n ++ maxSuffix)

bForall :: String -> String -> String -> LeanExpr -> LeanExpr
bForall = LBoundedForall

-- ---------------------------------------------------------------------------
-- Tag-set helpers
-- ---------------------------------------------------------------------------

tSort, tSet, tIndividual, tFun, tFOL, tSOL :: [Tag]
tSort = [TagSort, TagDecl]
tSet  = [TagSet,  TagDecl]
tIndividual = [TagIndividual, TagDecl]
tFun  = [TagFunction, TagDecl]
tFOL  = [TagFunction, TagFOLFunction, TagDecl]
tSOL  = [TagFunction, TagSOLFunction, TagDecl]

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Build the complete list of 'AxiomSet' values for a theory.
-- The order matches the current 'theoryToLeanDoc' output exactly, so that
-- 'axiomSetsToLeanDoc' can reproduce the same Lean 4 text.
mkAxiomSets :: PL.PreparedTheory -> [AxiomSet]
mkAxiomSets pt = concat
  [ headerAxiomSets
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
  -- -------------------------------------------------------------------------
  -- Derived function lists (mirrors LeanProps)
  -- -------------------------------------------------------------------------
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
        , IR.mereoName   m `notElem` [uMinName, uMaxName, "𝕌#min", "𝕌#max"]
        ]

  mereoObjects =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindMereological
        , IR.mereoOrigin m == IR.FromSignature
        , IR.mereoName   m `notElem` [uMinName, uMaxName, "𝕌#min", "𝕌#max"]
        ]

  propObjects =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindProposition
        , IR.mereoOrigin m == IR.FromSignature
        , IR.mereoName   m `notElem` [pMinName, pMaxName, "⊤", "⊥", "ℙ#min", "ℙ#max"]
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
  -- 1. Header: U/P (and optionally D) limit objects
  -- -------------------------------------------------------------------------
  headerAxiomSets :: [AxiomSet]
  headerAxiomSets =
    [ axiomSet [SSort uSortName] (tags [TagSort, TagDecl])
        [ LeanAxiom uMinName LProp
        , LeanAxiom uMaxName LProp
        ]
    , axiomSet [SSort pSortName] (tags [TagSort, TagDecl])
        [ LeanAxiom pMinName LProp
        , LeanAxiom pMaxName LProp
        ]
    ] ++
    [ axiomSet [SSort dSortName] (tags [TagSort, TagDecl])
        [ LeanAxiom dMinName LProp
        , LeanAxiom dMaxName LProp
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
        axiomSet [SSort (IR.sortName s)] (tags [TagSort, TagDecl])
          [ LeanAxiom (sortMinName (IR.sortName s)) LProp
          , LeanAxiom (sortMaxName (IR.sortName s)) LProp
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
          [ LeanAxiom (domMinName f) LProp
          , LeanAxiom (domMaxName f) LProp
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
          [LeanAxiom (IR.funcName f) (functionType f)]
      mkFOLDecl f =
        axiomSet [SFunction (IR.funcName f)] (tags tFOL)
          [LeanAxiom (IR.funcName f) (functionType f)]
      functionType f =
        let arity = length (IR.funcArgObjects f)
        in foldr (\_ acc -> LImpl LProp acc) LProp [1..arity]

  -- -------------------------------------------------------------------------
  -- 5. Image function declarations: f_dir_img, f_inv_img
  -- -------------------------------------------------------------------------
  imageFunctionDeclAxiomSets :: [AxiomSet]
  imageFunctionDeclAxiomSets = concatMap mkImgDecls multiArgFolFunctions
    where
      mkImgDecls f =
        [ axiomSet [SFunction (IR.funcName f), SImage]
                   (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
            [LeanAxiom (dirImgName f) (LImpl LProp LProp)]
        , axiomSet [SFunction (IR.funcName f), SImage]
                   (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
            [LeanAxiom (invImgName f) (LImpl LProp LProp)]
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
            [LeanAxiom (piName f k) (LImpl LProp LProp)]
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
            [LeanAxiom (piInvName f k) (LImpl LProp LProp)]
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
            ty    = foldr (\_ acc -> LImpl LProp acc) LProp [1..arity]
        in axiomSet [SFunction (IR.funcName f), STuple]
                    (tags [TagFunction, TagFOLFunction, TagTuple, TagDecl])
             [LeanAxiom (tupleName f) ty]

  -- -------------------------------------------------------------------------
  -- 9. FOL inverse declarations: g_inv, h_inv, ...
  -- -------------------------------------------------------------------------
  folInverseDeclAxiomSets :: [AxiomSet]
  folInverseDeclAxiomSets = map mkInvDecl folSingleArgFunctions
    where
      mkInvDecl f =
        axiomSet [SFunction (IR.funcName f), SInverse]
                 (tags [TagFunction, TagFOLFunction, TagInverse, TagDecl])
          [LeanAxiom (invName f) (LImpl LProp LProp)]

  -- -------------------------------------------------------------------------
  -- 10. IR predicate declarations: IR_f
  -- -------------------------------------------------------------------------
  irPredicateDeclAxiomSets :: [AxiomSet]
  irPredicateDeclAxiomSets = map mkIRDecl multiArgFolFunctions
    where
      mkIRDecl f =
        axiomSet [SFunction (IR.funcName f), SIR]
                 (tags [TagFunction, TagFOLFunction, TagIR, TagDecl])
          [LeanAxiom (irPredicateName f) (LImpl LProp LProp)]

  -- -------------------------------------------------------------------------
  -- 11. Function argument/result object declarations
  -- -------------------------------------------------------------------------
  functionArgResultDeclAxiomSets :: [AxiomSet]
  functionArgResultDeclAxiomSets = concatMap mkObjDecls
      (solFunctions ++ userDeclaredFolFunctions)
    where
      mkObjDecls f =
           [ axiomSet [SFunction (IR.funcName f), SArgObject k]
                      (tags [TagFunction, TagDecl])
               [LeanAxiom (sanitizeName (IR.mereoName obj)) LProp]
           | (k, obj) <- zip [1..] (IR.funcArgObjects f)
           ]
        ++ [ axiomSet [SFunction (IR.funcName f), SResObject]
                      (tags [TagFunction, TagDecl])
               [LeanAxiom (sanitizeName (IR.mereoName (IR.funcResObject f))) LProp]
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
               [LeanAxiom (fInv ++ "_1") LProp]
           , axiomSet [SFunction (IR.funcName f), SInverse, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagInverse, TagDecl])
               [LeanAxiom (fInv ++ "_res") LProp]
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
                   [LeanAxiom argN LProp]
               ]

  -- -------------------------------------------------------------------------
  -- 14. Projection witness declarations: f_pi_k_1, f_pi_k_res
  -- -------------------------------------------------------------------------
  projectionWitnessDeclAxiomSets :: [AxiomSet]
  projectionWitnessDeclAxiomSets = concatMap mkProjWitnesses multiArgFolFunctions
    where
      mkProjWitnesses f =
        concatMap (mkOne f) [1 .. length (IR.funcArgSorts f)]
        where
          mkOne f k =
            [ axiomSet [SFunction (IR.funcName f), SProjection k, SArgObject 1]
                       (tags [TagFunction, TagFOLFunction, TagProjection, TagDecl])
                [LeanAxiom (piName f k ++ "_1") LProp]
            , axiomSet [SFunction (IR.funcName f), SProjection k, SResObject]
                       (tags [TagFunction, TagFOLFunction, TagProjection, TagDecl])
                [LeanAxiom (piName f k ++ "_res") LProp]
            ]

  -- -------------------------------------------------------------------------
  -- 15. Inverse image witness declarations: f_inv_img_arg, f_inv_img_res
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
               [LeanAxiom argN LProp]
           , axiomSet [SFunction (IR.funcName f), SImage, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
               [LeanAxiom resN LProp]
           ]

  -- -------------------------------------------------------------------------
  -- 16. Mereological (𝕌-sorted) object declarations
  -- -------------------------------------------------------------------------
  mereoDeclAxiomSets :: [AxiomSet]
  mereoDeclAxiomSets = map mkMereoDecl mereoObjects
    where
      mkMereoDecl m =
        axiomSet [SGlobal] (tags [TagDecl])
          [LeanAxiom (IR.mereoName m) LProp]

  -- -------------------------------------------------------------------------
  -- 17. Propositional (ℙ-sorted) object declarations
  -- -------------------------------------------------------------------------
  propDeclAxiomSets :: [AxiomSet]
  propDeclAxiomSets = map mkPropDecl propObjects
    where
      mkPropDecl m =
        axiomSet [SGlobal] (tags [TagDecl])
          [LeanAxiom (IR.mereoName m) LProp]

  -- -------------------------------------------------------------------------
  -- 18. 𝔻-sorted set declarations
  -- -------------------------------------------------------------------------
  setDeclAxiomSets :: [AxiomSet]
  setDeclAxiomSets = map mkSetDecl (setObjects ++ userSortSets)
    where
      mkSetDecl m =
        axiomSet [SSet (IR.mereoName m)] (tags [TagSet, TagDecl])
          [LeanAxiom (IR.mereoName m) LProp]

  -- -------------------------------------------------------------------------
  -- 19-21 + 36-39. Sort bounds (all entity kinds).
  -- Delegates entirely to Eidos.SortBounds which owns all the semantic logic:
  -- which entities need bounds, what lo/hi values they have, and whether to
  -- collapse to a single IsWithinBounds axiom (--sorting-axioms) or expand to
  -- separate _min/_max axioms.
  -- -------------------------------------------------------------------------
  sortBoundAxiomSets :: [AxiomSet]
  sortBoundAxiomSets = map sortBoundToAxiomSet (PL.ptSortBounds pt)

  sortBoundToAxiomSet :: SB.SortBoundEntry -> AxiomSet
  sortBoundToAxiomSet entry =
    let (path, tgs) = contextToPathAndTags (SB.sbeContext entry)
    in axiomSet path (tags tgs)
         (map (\(nm, expr) -> LeanAxiom nm (mereoExprToLean expr)) (SB.sbeAxioms entry))

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
  -- 22-35 + R6. Function connection, adjunction, decomposition, IR, and
  -- relation-bound axioms.
  -- Delegates entirely to Eidos.FunctionFacts which owns all the semantic
  -- logic.  MAbbrevApp covers function application; MBoundedSum provides
  -- bounded quantification (renders as IsWithinBounds-guarded ∀).
  -- -------------------------------------------------------------------------
  functionFactAxiomSets :: [AxiomSet]
  functionFactAxiomSets = map functionFactToAxiomSet (PL.ptFunctionFacts pt)

  functionFactToAxiomSet :: FF.FunctionFactEntry -> AxiomSet
  functionFactToAxiomSet entry =
    let (path, tgs) = factContextToPathAndTags (FF.ffeContext entry)
    in axiomSet path (tags tgs)
         (map (\(nm, expr) -> LeanAxiom nm (mereoExprToLean expr)) (FF.ffeAxioms entry))

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

  -- Sections 22-35 and R6 are now handled by functionFactAxiomSets above.

  -- -------------------------------------------------------------------------
  -- -------------------------------------------------------------------------
  -- 35b. Individual declarations
  -- -------------------------------------------------------------------------
  individualDeclAxiomSets :: [AxiomSet]
  individualDeclAxiomSets = map mkIndividualDecl individualObjects
    where
      mkIndividualDecl m =
        axiomSet [SIndividual (IR.mereoName m)] (tags tIndividual)
          [LeanAxiom (IR.mereoName m) LProp]

  -- Sections 36-39 (mereological, individual, propositional, set bounds) are
  -- now handled by sortBoundAxiomSets above via Eidos.SortBounds.

  -- -------------------------------------------------------------------------
  -- 40-41 + R7. Sort ordering axioms.
  -- Delegates entirely to Eidos.SortBounds which owns all the semantic logic:
  -- builtin sort orderings (𝕌, ℙ, 𝔻), user sort orderings (subsort /
  -- quotient / subquotient / regular), product sort orderings, and relation
  -- product sort orderings.  MSymDiff renders as ↔, substituting for LEq.
  -- -------------------------------------------------------------------------
  sortOrderAxiomSets :: [AxiomSet]
  sortOrderAxiomSets = map sortOrderToAxiomSet (PL.ptSortOrder pt)

  sortOrderToAxiomSet :: SB.SortOrderEntry -> AxiomSet
  sortOrderToAxiomSet entry =
    let (path, tgs) = orderContextToPathAndTags (SB.soeContext entry)
    in axiomSet path (tags tgs)
         (map (\(nm, expr) -> LeanAxiom nm (mereoExprToLean expr)) (SB.soeAxioms entry))

  orderContextToPathAndTags :: SB.SortOrderContext -> ([SubjectNode], [Tag])
  orderContextToPathAndTags ctx = case ctx of
    SB.SOCBuiltinSort n           -> ([SSort n],            [TagSort, TagOrdering])
    SB.SOCUserSort    n           -> ([SSort n],            [TagSort, TagOrdering])
    SB.SOCProductSort fn          -> ([SFunction fn, STuple], [TagSort, TagFunction, TagFOLFunction, TagTuple, TagOrdering])
    SB.SOCRelationProductSort rn  -> ([SSet rn],            [TagSort, TagSet, TagOrdering])

  -- -------------------------------------------------------------------------
  -- R1. Relation product-sort limit declarations: R_dom_Min, R_dom_Max
  -- (Analogous to productSortLimitAxiomSets for multi-arg FOL functions.)
  -- -------------------------------------------------------------------------
  relProductSortLimitAxiomSets :: [AxiomSet]
  relProductSortLimitAxiomSets = map mkLimits userRelations
    where
      mkLimits r =
        axiomSet [SSet (IR.relName r)] (tags [TagSet, TagDecl])
          [ LeanAxiom (relDomMinName r) LProp
          , LeanAxiom (relDomMaxName r) LProp
          ]

  -- -------------------------------------------------------------------------
  -- R2. Relation declarations: R : Prop → … → Prop (one arrow per arg sort)
  -- (Analogous to functionDeclAxiomSets for SOL functions.)
  -- -------------------------------------------------------------------------
  relDeclAxiomSets :: [AxiomSet]
  relDeclAxiomSets = map mkRelDecl userRelations
    where
      mkRelDecl r =
        let arity   = length (IR.relArgSorts r)
            relType = foldr (\_ acc -> LImpl LProp acc) LProp [1..arity]
        in axiomSet [SSet (IR.relName r)] (tags [TagSet, TagDecl])
             [LeanAxiom (IR.relName r) relType]

  -- -------------------------------------------------------------------------
  -- R3. Relation arg-object declarations: R_1 : Prop, R_2 : Prop, …
  -- (Analogous to functionArgResultDeclAxiomSets.)
  -- -------------------------------------------------------------------------
  relArgObjectDeclAxiomSets :: [AxiomSet]
  relArgObjectDeclAxiomSets = concatMap mkArgDecls userRelations
    where
      mkArgDecls r =
        [ axiomSet [SSet (IR.relName r)] (tags [TagSet, TagDecl])
            [LeanAxiom (sanitizeName (IR.mereoName obj)) LProp]
        | (_, obj) <- zip [1..] (IR.relArgObjects r)
        ]

  -- -------------------------------------------------------------------------
  -- R4. Relation argument-object declaration: R_arg : Prop  (product element)
  -- (Analogous to productArgDeclAxiomSets.)
  -- -------------------------------------------------------------------------
  relArgumentDeclAxiomSets :: [AxiomSet]
  relArgumentDeclAxiomSets = map mkArgDecl userRelations
    where
      mkArgDecl r =
        let argN = sanitizeName (IR.mereoName (IR.relArgument r))
            dMn  = relDomMinName r
            dMx  = relDomMaxName r
        in axiomSet [SSet (IR.relName r)] (tags [TagSet, TagDecl])
             [ LeanAxiom argN LProp
             , LeanAxiom (argN ++ minSuffixForAxiomNames)
                 (LImpl pMin (LImpl (LVar argN) (LVar dMn)))
             , LeanAxiom (argN ++ maxSuffixForAxiomNames)
                 (LImpl pMin (LImpl (LVar dMx) (LVar argN)))
             ]

  -- R5 relation arg-object sorting axioms are now handled by sortBoundAxiomSets.

  -- -------------------------------------------------------------------------
  -- 42. User fact axioms (rendered from FCMereologicalTranslation facts)
  -- -------------------------------------------------------------------------
  userFactAxiomSets :: [AxiomSet]
  userFactAxiomSets =
    zipWith mkTranslationAS [1..] allTranslationFacts
    where
      allTranslationFacts = translationOfFacts ++ translationOfAssertions ++ translationOfMetafacts
      totalFacts = length allTranslationFacts
      mkLabel idx = if totalFacts > 1 then "ax" ++ show idx else ""

      mkTranslationAS idx fact =
        axiomSet [SGlobal] (tags [TagUserFact])
          [LeanAxiom (mkLabel idx)
            (mereoExprToLean (fromJust (IR.factMereoExpr fact)))]

  -- -------------------------------------------------------------------------
  -- 43. Implicit merge axioms
  -- -------------------------------------------------------------------------
  implicitMergeAxiomSets :: [AxiomSet]
  implicitMergeAxiomSets = concatMap mkMergeAS implicitMergeFacts
    where
      mkMergeAS :: IR.Fact -> [AxiomSet]
      mkMergeAS fact = extractMergeAxioms (fromJust (IR.factPropExpr fact))
        where
          -- Walk the IR expression tree to extract lhsName and rhsName (for
          -- the axiom name), then emit the axiom using the pre-built
          -- factMereoExpr (non-functions) or a plain LEq (functions).
          -- The function/non-function distinction is encoded in factSubkind,
          -- which was set at fact-creation time.
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
                -- Functions: plain equality (↔ would be a type error for non-Prop types)
                [ axiomSet [SGlobal] (tags [TagImplicitMerge])
                    [LeanAxiom axName (LEq (LVar lhsName) (LVar rhsName))]
                ]
              _ ->
                -- Non-functions: translate the pre-built WrapMetafact MereoExpr
                [ axiomSet [SGlobal] (tags [TagImplicitMerge])
                    [LeanAxiom axName (mereoExprToLean (fromJust (IR.factMereoExpr fact)))]
                ]

      -- | Build a unique Lean-safe axiom name from the LHS entity name and the
      -- RHS qualified name.  Form: @<safeLhs>_from_<subtheory>@, where
      -- @<subtheory>@ is the source path derived by dropping the last
      -- dot-segment of @rhsName@ and replacing dots with underscores.
      --
      -- This guarantees uniqueness when the same LHS name is contributed by
      -- multiple implicit subtheories (e.g. 𝔻_Min from both lower_semi_lattice
      -- and upper_semi_lattice).
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

-- ---------------------------------------------------------------------------
-- MereoExpr → LeanExpr renderer
-- ---------------------------------------------------------------------------

-- | Translate a 'IR.MereoExpr' to a 'LeanExpr'.
--
-- Mereological operations map to propositional connectives:
--   MSum     → LConj   (+ = ∧)
--   MProd    → LDisj   (× = ∨)
--   MDiff    → LImpl   (a - b = b → a)
--   MRevDiff → LImpl   (a ⇒ b = a → b)
--   MSymDiff → LBicond (a ∸ b = a ↔ b)
--   MZero    → pMin    (least element = True = ℙ_Min)
--   MAbbrevApp → LApp  (abbreviation call)
--   MBoundedSum → LForallKw with IsWithinBounds guard
mereoExprToLean :: IR.MereoExpr -> LeanExpr
mereoExprToLean (IR.MSum a b)     = LConj   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MProd a b)    = LDisj   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MDiff a b)    = LImpl   (mereoExprToLean b) (mereoExprToLean a)
mereoExprToLean (IR.MRevDiff a b) = LImpl   (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MSymDiff a b) = LBicond (mereoExprToLean a) (mereoExprToLean b)
mereoExprToLean (IR.MVar n)       = LVar (resolveName n)
mereoExprToLean IR.MZero          = LVar pMinName
mereoExprToLean (IR.MAbbrevApp name args) =
  LApp (LVar name) (map mereoExprToLean args)
mereoExprToLean (IR.MBoundedSum var lo hi body) =
  LForallKw var LProp
    (LImpl (LApp (LVar "IsWithinBounds") [mereoExprToLean lo, mereoExprToLean hi, LVar var])
           (mereoExprToLean body))

propExprToLean :: IR.ResolvedPropExpr -> LeanExpr
propExprToLean (IR.ResolvedPropBicond lhs rests) =
  foldl (\acc r -> LBicond acc (rightImplToLean (IR.resolvedPropRestRight r)))
        (rightImplToLean lhs)
        rests

rightImplToLean :: IR.ResolvedRightImpl -> LeanExpr
rightImplToLean (IR.ResolvedRightImpl lhs Nothing) = leftImplToLean lhs
rightImplToLean (IR.ResolvedRightImpl lhs (Just (_, rhs))) =
  LImpl (leftImplToLean lhs) (rightImplToLean rhs)

leftImplToLean :: IR.ResolvedLeftImpl -> LeanExpr
leftImplToLean (IR.ResolvedLeftImpl lhs []) = disjToLean lhs
leftImplToLean (IR.ResolvedLeftImpl lhs rests) =
  foldr (\r acc -> LImpl (disjToLean (IR.resolvedLirRight r)) acc)
        (disjToLean lhs) rests

disjToLean :: IR.ResolvedDisj -> LeanExpr
disjToLean (IR.ResolvedDisj lhs []) = conjToLean lhs
disjToLean (IR.ResolvedDisj lhs rests) =
  foldl (\acc r -> LDisj acc (conjToLean (IR.resolvedDisjRestRight r)))
        (conjToLean lhs) rests

conjToLean :: IR.ResolvedConj -> LeanExpr
conjToLean (IR.ResolvedConj lhs []) = negToLean lhs
conjToLean (IR.ResolvedConj lhs rests) =
  foldl (\acc r -> LConj acc (negToLean (IR.resolvedConjRestRight r)))
        (negToLean lhs) rests

negToLean :: IR.ResolvedNeg -> LeanExpr
negToLean (IR.ResolvedNegNot inner) =
  LImpl (negToLean inner) (LVar pMaxName)
negToLean (IR.ResolvedNegChild q) =
  quantifiedToLean q

quantifiedToLean :: IR.ResolvedQuantified -> LeanExpr
quantifiedToLean (IR.ResolvedQuantified [] atom) = atomicPropToLean atom
quantifiedToLean (IR.ResolvedQuantified qs atom) =
  foldr quantifierToLean (atomicPropToLean atom) qs

-- | True when a resolved variable represents a first-order individual —
-- that is, it is bound with ':' (not '⊆') over a user-declared sort
-- (not ℙ or 𝕌).  Only these variables receive the 'IsIndividual' guard.
isFOLIndividual :: IR.ResolvedVarDecl -> Bool
isFOLIndividual vd =
  not (IR.resolvedVarIsSet vd)          -- bound with ':', not '⊆'
  && not (IR.isPropSort    s)            -- not a proposition variable
  && not (IR.isUniverseSort s)           -- not a bare mereological variable
  where s = IR.resolvedVarSort vd

quantifierToLean :: IR.ResolvedQuantifier -> LeanExpr -> LeanExpr
quantifierToLean (IR.ResolvedQForall vd) body =
  let varN     = IR.resolvedVarName vd
      sn       = IR.sortName (IR.resolvedVarSort vd)
      (lo, hi) = sortBounds sn
  in if isFOLIndividual vd
     -- ∀x : A φ(x): FOL individual — bounds + individuality guard.
     then LBoundedForall varN lo hi (LImpl (LIsIndividual lo varN hi) body)
     -- ∀X ⊆ A / ∀X : ℙ / ∀X : 𝕌 — bounds only, no individuality guard.
     else LBoundedForall varN lo hi body
quantifierToLean (IR.ResolvedQExists vd) body =
  let varN     = IR.resolvedVarName vd
      sn       = IR.sortName (IR.resolvedVarSort vd)
      (lo, hi) = sortBounds sn
  in if isFOLIndividual vd
     -- ∃x : A φ(x): FOL individual — bounds + individuality guard.
     then LExists varN (LVar "Prop")
            (LImpl (LIsWithinBounds lo varN hi)
              (LImpl (LIsIndividual lo varN hi) body))
     -- ∃X ⊆ A / ∃X : ℙ / ∃X : 𝕌 — bounds only, no individuality guard.
     else LExists varN (LVar "Prop") (LImpl (LIsWithinBounds lo varN hi) body)

atomicPropToLean :: IR.ResolvedAtomicProp -> LeanExpr
atomicPropToLean (IR.ResolvedAtomicConstant ref) = LVar (resolveConstRef ref)
atomicPropToLean (IR.ResolvedAtomicTermPair tp)  = termPairToLean tp

resolveConstRef :: IR.ResolvedConstantRef -> String
resolveConstRef = resolveName . IR.resolvedConstRefName

resolveName :: String -> String
resolveName n = case n of
  "⊤"     -> pMinName
  "⊥"     -> pMaxName
  "ℙ#min" -> pMinName
  "ℙ#max" -> pMaxName
  "𝕌#min" -> uMinName
  "𝕌#max" -> uMaxName
  other
    | Just base <- stripSuffix "#min" other -> sanitizeName base ++ minSuffix
    | Just base <- stripSuffix "#max" other -> sanitizeName base ++ maxSuffix
    | otherwise -> sanitizeName other
  where
    stripSuffix suffix str =
      let (front, back) = splitAt (length str - length suffix) str
      in if back == suffix then Just front else Nothing

termPairToLean :: IR.ResolvedTermPair -> LeanExpr
termPairToLean (IR.ResolvedTermPair lhs rights ty) =
  foldl (applyRelOp ty) (termToLean lhs) rights

-- | Render a relational operator applied to two already-rendered expressions.
--
-- The 'ExprType' of the LHS (from 'resolvedTPType') is threaded in so that
-- the @"="@ case can choose the correct Lean 4 encoding:
--
--   * For __function-kinded__ and __sort-kinded__ terms (@FOLFunctionClass@,
--     @SOLFunctionClass@, @SortClass@) equality must be rendered as @LEq@
--     (@a = b@), because these types are not 'Prop' and @↔@ would be a
--     type error in Lean 4.
--
--   * For __proposition-kinded__ and __mereological__ terms
--     (@PropositionClass@, @IndividualClass@, @OtherMereologicalClass@,
--     @RelationClass@) the mereological encoding uses @LBicond@ (@a ↔ b@),
--     which is the standard Eidos rendering for propositional equality.
--
-- All other operators are unaffected by the type.
applyRelOp :: IR.ExprType -> LeanExpr -> IR.ResolvedRelationFollowedByTerm -> LeanExpr
applyRelOp lhsTy leftExpr rfbt =
  let op    = IR.resolvedRFTOp rfbt
      right = termToLean (IR.resolvedRFTRight rfbt)
      qual  = IR.resolvedRFTSortQual rfbt
  in case op of
       "+"  -> LConj   leftExpr right
       "×"  -> LDisj   leftExpr right
       "-"  -> LImpl   right leftExpr
       "∸"  -> LBicond leftExpr right
       "="  -> case qual of
                 Just (IR.ResolvedOptionalSortExpr "^" s) ->
                   let lo  = LVar (resolveName (IR.mereoName (IR.sortMin s)))
                       hi  = LVar (resolveName (IR.mereoName (IR.sortMax s)))
                   in LBicond (LProjectIntoInterval leftExpr lo hi)
                              (LProjectIntoInterval right     lo hi)
                 _ -> case lhsTy of
                        -- Functions and sorts are not Prop: use Lean = not ↔
                        IR.FOLFunctionClass _ -> LEq leftExpr right
                        IR.SOLFunctionClass _ -> LEq leftExpr right
                        IR.SortClass          -> LEq leftExpr right
                        -- Propositions, individuals, sets, mereological objects:
                        -- use the mereological ↔ encoding
                        _                     -> LBicond leftExpr right
       "≤"  -> LImpl   leftExpr right
       "∪"  -> LConj   leftExpr right
       "∩"  -> LDisj   leftExpr right
       "⊆"  -> LImpl   right leftExpr
       "∈"  -> LImpl   right leftExpr
       "⇒"  -> LImpl   leftExpr right
       _    -> LVar ("(" ++ op ++ ")")

termToLean :: IR.ResolvedTerm -> LeanExpr
termToLean (IR.ResolvedTerm lhs [] _) = factorToLean lhs
termToLean (IR.ResolvedTerm lhs rests _) =
  foldl applyArithOp (factorToLean lhs) rests

applyArithOp :: LeanExpr -> IR.ResolvedOperationFollowedByFactor -> LeanExpr
applyArithOp leftExpr off =
  let op    = IR.resolvedOFFOp off
      right = factorToLean (IR.resolvedOFFRight off)
  in case op of
       "+"  -> LConj  leftExpr right
       "×"  -> LDisj  leftExpr right
       "-"  -> LImpl  right leftExpr
       "∸"  -> LBicond leftExpr right
       "∪"  -> LConj  leftExpr right
       "∩"  -> LDisj  leftExpr right
       "⇒"  -> LImpl  leftExpr right
       _    -> LVar ("(" ++ op ++ ")")

factorToLean :: IR.ResolvedFactor -> LeanExpr
factorToLean (IR.ResolvedFactor base [] _) = baseTermToLean base
factorToLean (IR.ResolvedFactor base suffixes _) =
  foldl applySuffix (baseTermToLean base) suffixes
  where
    applySuffix expr (IR.ResolvedSuffixDotAttr attr) =
      LVar (sanitizeName (renderLeanExpr expr ++ "_" ++ attr))
    applySuffix expr (IR.ResolvedSuffixCall args) =
      LApp expr (map termToLean args)
    applySuffix expr (IR.ResolvedSuffixSpecialOp attr) =
      case attr of
        "min" -> LVar (sanitizeName (renderLeanExpr expr ++ minSuffix))
        "max" -> LVar (sanitizeName (renderLeanExpr expr ++ maxSuffix))
        _ -> LVar (sanitizeName (renderLeanExpr expr ++ "_" ++ attr))

baseTermToLean :: IR.ResolvedBaseTerm -> LeanExpr
baseTermToLean (IR.ResolvedBTAtomic ref) =
  LVar (resolveConstRef ref)
baseTermToLean (IR.ResolvedBTPropParen expr) = propExprToLean expr
baseTermToLean (IR.ResolvedBTTermParen term) = termToLean term
baseTermToLean (IR.ResolvedBTSingleton t) =
  termToLean t
baseTermToLean (IR.ResolvedBTEvaluationInTheory eit) =
  propExprToLean (IR.resolvedEITOperand eit)
baseTermToLean (IR.ResolvedBTProjectionToSort pts) =
  let s    = IR.resolvedPTSort pts
      lo   = resolveName (IR.mereoName (IR.sortMin s))
      hi   = resolveName (IR.mereoName (IR.sortMax s))
      x    = termToLean (IR.resolvedPTOperand pts)
  in LProjectIntoInterval x (LVar lo) (LVar hi)
baseTermToLean (IR.ResolvedBTProjectionToInterval pti) =
  let lo = termToLean (IR.resolvedPTILo      pti)
      hi = termToLean (IR.resolvedPTIHi      pti)
      x  = termToLean (IR.resolvedPTIOperand pti)
  in LProjectIntoInterval x lo hi
baseTermToLean (IR.ResolvedBTGeneralizedSumOrProduct gsp) =
  let sym     = IR.resolvedGSPSymbol gsp
      operand = termToLean (IR.resolvedGSPOperand gsp)
  in case IR.resolvedGSPVar gsp of
       Left vd ->
         let varN     = IR.resolvedVarName vd
             sn       = IR.sortName (IR.resolvedVarSort vd)
             (lo, hi) = sortBounds sn
         in case sym of
              "Σ" -> LBoundedForall varN lo hi operand
              "Π" -> LExists varN (LVar "Prop")
                       (LImpl (LIsWithinBounds lo varN hi) operand)
              _   -> operand   -- unknown symbol: fall back to operand
       Right bareVar ->
         -- A bare (untyped) binder for Σ/Π is not syntactically well-formed:
         -- a sort must always be specified.  If this branch is reached it
         -- indicates a bug in the parser or IR construction.
         error ("baseTermToLean: GeneralizedSumOrProduct with bare binder '"
                ++ bareVar ++ "' for symbol '" ++ sym
                ++ "' — sort annotation is required")

-- | Both set comprehension { x : A | φ(x) } and description ιx : A φ(x)
-- translate to the same Lean expression:
--
--   forall x : Prop, (IsWithinBounds A_Min A_Max x) → (φ'(x) → x)
--
-- This encodes the mereological reading: we are asserting x for all x
-- that satisfy φ'(x) within the bounds of sort A, which gives us the
-- sum of all such x — the mereological sum of the members of the set.
baseTermToLean (IR.ResolvedBTSetComprehension sc) =
  let vd      = IR.resolvedSCVar sc
      varN    = IR.resolvedVarName vd
      sn      = IR.sortName (IR.resolvedVarSort vd)
      (lo,hi) = sortBounds sn
      phi     = propExprToLean (IR.resolvedSCBody sc)
  in LBoundedForall varN lo hi (LImpl phi (LVar varN))

baseTermToLean (IR.ResolvedBTDescription desc) =
  let vd      = IR.resolvedDescVar desc
      varN    = IR.resolvedVarName vd
      sn      = IR.sortName (IR.resolvedVarSort vd)
      (lo,hi) = sortBounds sn
      phi     = propExprToLean (IR.resolvedDescBody desc)
  in LBoundedForall varN lo hi (LImpl phi (LVar varN))

-- ---------------------------------------------------------------------------
-- Flat post-order block list
-- ---------------------------------------------------------------------------

-- | Collect all theories in the tree rooted at @theory@ into a flat,
-- post-ordered list of @(namespace, axiomSets)@ pairs, suitable for
-- rendering as a sequence of flat Lean 4 @namespace … end@ blocks.
--
-- Post-order (children before parents) ensures that cross-namespace
-- references from a parent to a child are always forward-declared by the
-- time the parent block is emitted.
--
-- The root theory is assigned the reserved namespace @\"__main__\"@.
-- All subtheories use their 'IR.theoryFullyQualifiedName'.
--
-- Reflection subtheories are skipped; their Lean 4 treatment is not yet
-- implemented.
theoryBlocks :: PL.PreparedTheory -> [(String, [AxiomSet])]
theoryBlocks pt =
  childBlocks ++ [rootBlock]
  where
    theory      = PL.ptTheory pt
    rootBlock   = ("__main__", mkAxiomSets pt)
    childBlocks = concatMap subBlocks (IR.theorySubtheories theory)

    subBlocks :: IR.Theory -> [(String, [AxiomSet])]
    subBlocks sub
      | IR.theoryReflection sub = []
      | otherwise =
          concatMap subBlocks (IR.theorySubtheories sub)
          ++ [(IR.theoryFullyQualifiedName sub, mkAxiomSets (PL.prepareTheory (PL.ptOptions pt) sub))]
