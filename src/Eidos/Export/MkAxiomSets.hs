-- | Generation of 'AxiomSet' values from an Eidos 'IR.Theory'.
--
-- This module implements the first stage of the refactored pipeline:
--
-- @
-- IR.Theory  →  [AxiomSet]  →  LeanDoc  →  String
-- @
--
-- Every axiom that 'Eidos.Export.LeanProps.theoryToLeanDoc' currently emits
-- has a corresponding 'AxiomSet' here, with the same logical content but
-- enriched with a 'SubjectPath' and a 'TagSet' that make it introspectable
-- without parsing 'LeanExpr' trees.
module Eidos.Export.MkAxiomSets
  ( mkAxiomSets
  ) where

import qualified Eidos.IR as IR
import Eidos.Export.LeanExpr
import Eidos.Export.LeanAxiomSet

-- ---------------------------------------------------------------------------
-- Naming helpers (kept in sync with LeanProps)
-- ---------------------------------------------------------------------------

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

sortMinName, sortMaxName :: String -> String
sortMinName s = s ++ minSuffix
sortMaxName s = s ++ maxSuffix

uMinName, uMaxName, pMinName, pMaxName :: String
uMinName = "U_Min"
uMaxName = "U_Max"
pMinName = "P_Min"
pMaxName = "P_Max"

uMin, uMax, pMin, pMax :: LeanExpr
uMin = LVar uMinName
uMax = LVar uMaxName
pMin = LVar pMinName
pMax = LVar pMaxName

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
sortBounds sortN = case sortN of
  "ℙ" -> (pMinName, pMaxName)
  "𝕌" -> (uMinName, uMaxName)
  _   -> (sortN ++ minSuffix, sortN ++ maxSuffix)

bForall :: String -> String -> String -> LeanExpr -> LeanExpr
bForall = LBoundedForall

-- ---------------------------------------------------------------------------
-- Tag-set helpers
-- ---------------------------------------------------------------------------

tSort, tSet, tFun, tFOL, tSOL :: [Tag]
tSort = [TagSort, TagDecl]
tSet  = [TagSet,  TagDecl]
tFun  = [TagFunction, TagDecl]
tFOL  = [TagFunction, TagFOLFunction, TagDecl]
tSOL  = [TagFunction, TagSOLFunction, TagDecl]

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Build the complete list of 'AxiomSet' values for a theory.
-- The order matches the current 'theoryToLeanDoc' output exactly, so that
-- 'axiomSetsToLeanDoc' can reproduce the same Lean 4 text.
mkAxiomSets :: IR.Theory -> [AxiomSet]
mkAxiomSets theory = concat
  [ headerAxiomSets
  , userSortLimitAxiomSets
  , productSortLimitAxiomSets
  , functionDeclAxiomSets
  , imageFunctionDeclAxiomSets
  , projectionFunctionDeclAxiomSets
  , projectionInverseDeclAxiomSets
  , tupleFunctionDeclAxiomSets
  , folInverseDeclAxiomSets
  , irPredicateDeclAxiomSets
  , functionArgResultDeclAxiomSets
  , folInverseArgResDeclAxiomSets
  , productArgDeclAxiomSets
  , projectionWitnessDeclAxiomSets
  , invImgWitnessDeclAxiomSets
  , mereoDeclAxiomSets
  , propDeclAxiomSets
  , setDeclAxiomSets
  , functionArgResultSortingAxiomSets
  , folInverseArgResSortingAxiomSets
  , projectionWitnessSortingAxiomSets
  , functionConnectionAxiomSets
  , folInverseConnectionAxiomSets
  , dirImgConnectionAxiomSets
  , invImgConnectionAxiomSets
  , folAdjunctionAxiomSets
  , imageAdjunctionAxiomSets
  , decompositionAxiomSets
  , tupleFact_AxiomSets
  , projectionConnectionAxiomSets
  , projectionAdjunctionAxiomSets
  , tupleInvDecompAxiomSets
  , irTupleProjAxiomSets
  , irProjFromTupleAxiomSets
  , irSeparatesAxiomSets
  , mereoBoundsAxiomSets
  , propBoundsAxiomSets
  , setBoundsAxiomSets
  , userSortSetBoundsAxiomSets
  , sortOrderAxiomSets
  , productSortOrderAxiomSets
  , userFactAxiomSets
  ]
  where
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

  functionObjects =
    concatMap (\f -> IR.funcArgObjects f ++ [IR.funcResObject f]) solFunctions ++
    concatMap (\f -> IR.funcArgObjects f ++ [IR.funcResObject f]) userDeclaredFolFunctions

  mereoObjects =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindIndividual
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
             , IR.sortName  (IR.mereoSort m) == "𝔻"
             ]
    else []

  userSortSets =
    [ m | IR.EntityMereological m <- IR.theoryObjects theory
        , IR.mereoKind   m == IR.MereologicalEntityKindSet
        , IR.mereoOrigin m == IR.FromSignature
        , IR.sortKind  (IR.mereoSort m) == IR.SortKindFromSignature
        ]

  userAssertions =
    [ f | f <- IR.theoryFacts theory
        , IR.factKind f == IR.FactKindAssertion
        , not (IR.factIsInherited f)
        , not (IR.factIsMereologicalTranslation f)
        ]

  userMetafacts =
    [ f | f <- IR.theoryFacts theory
        , IR.factKind f == IR.FactKindMetafactsFact
        , not (IR.factIsInherited f)
        , not (IR.factIsMereologicalTranslation f)
        ]

  -- -------------------------------------------------------------------------
  -- 1. Header: U/P (and optionally D) limit objects
  -- -------------------------------------------------------------------------
  headerAxiomSets :: [AxiomSet]
  headerAxiomSets =
    [ axiomSet [SGlobal] (tags [TagSort, TagDecl])
        [ LeanAxiom uMinName LProp
        , LeanAxiom uMaxName LProp
        , LeanAxiom pMinName LProp
        , LeanAxiom pMaxName LProp
        ]
    ] ++
    [ axiomSet [SGlobal] (tags [TagSort, TagDecl])
        [ LeanAxiom "D_Min" LProp
        , LeanAxiom "D_Max" LProp
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
                dMn  = domMinName f
                dMx  = domMaxName f
            in [ axiomSet [SFunction (IR.funcName f), STuple, SArgObject 0]
                          (tags [TagFunction, TagFOLFunction, TagTuple, TagDecl])
                   [LeanAxiom argN LProp]
               , axiomSet [SFunction (IR.funcName f), STuple, SArgObject 0]
                          (tags [TagFunction, TagFOLFunction, TagTuple, TagSorting])
                   [ LeanAxiom (argN ++ minSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar argN) (LVar dMn)))
                   , LeanAxiom (argN ++ maxSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar dMx) (LVar argN)))
                   ]
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
            rSN  = IR.sortName (IR.funcResSort f)
            dMn  = domMinName f
            dMx  = domMaxName f
        in [ axiomSet [SFunction (IR.funcName f), SImage, SArgObject 1]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
               [LeanAxiom argN LProp]
           , axiomSet [SFunction (IR.funcName f), SImage, SArgObject 1]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagSorting])
               [ LeanAxiom (argN ++ minSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar argN) (LVar (sortMinName rSN))))
               , LeanAxiom (argN ++ maxSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar (sortMaxName rSN)) (LVar argN)))
               ]
           , axiomSet [SFunction (IR.funcName f), SImage, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagDecl])
               [LeanAxiom resN LProp]
           , axiomSet [SFunction (IR.funcName f), SImage, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagImage, TagSorting])
               [ LeanAxiom (resN ++ minSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar resN) (LVar dMn)))
               , LeanAxiom (resN ++ maxSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar dMx) (LVar resN)))
               ]
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
  setDeclAxiomSets = map mkSetDecl setObjects
    where
      mkSetDecl m =
        axiomSet [SGlobal] (tags [TagDecl])
          [LeanAxiom (IR.mereoName m) LProp]

  -- -------------------------------------------------------------------------
  -- 19. Function argument/result object sorting axioms
  -- -------------------------------------------------------------------------
  functionArgResultSortingAxiomSets :: [AxiomSet]
  functionArgResultSortingAxiomSets = concatMap mkSorting functionObjects
    where
      mkSorting m =
        let n       = sanitizeName (IR.mereoName m)
            sN      = IR.sortName (IR.mereoSort m)
            (lo,hi) = sortBounds sN
        in [ axiomSet (pathFor m) (tags [TagFunction, TagSorting])
               [ LeanAxiom (n ++ minSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar n) (LVar lo)))
               , LeanAxiom (n ++ maxSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar hi) (LVar n)))
               ]
           ]
      pathFor m = [SGlobal]  -- obj sorting not easily attributed to one function

  -- -------------------------------------------------------------------------
  -- 20. FOL inverse arg/res sorting axioms
  -- -------------------------------------------------------------------------
  folInverseArgResSortingAxiomSets :: [AxiomSet]
  folInverseArgResSortingAxiomSets = concatMap mkInvSorting folSingleArgFunctions
    where
      mkInvSorting f =
        let fInv    = invName f
            argSort = IR.sortName (head (IR.funcArgSorts f))
            resSort = IR.sortName (IR.funcResSort f)
            n1      = fInv ++ "_1"
            nr      = fInv ++ "_res"
        in [ axiomSet [SFunction (IR.funcName f), SInverse, SArgObject 1]
                      (tags [TagFunction, TagFOLFunction, TagInverse, TagSorting])
               [ LeanAxiom (n1 ++ minSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar n1) (LVar (sortMinName resSort))))
               , LeanAxiom (n1 ++ maxSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar (sortMaxName resSort)) (LVar n1)))
               ]
           , axiomSet [SFunction (IR.funcName f), SInverse, SResObject]
                      (tags [TagFunction, TagFOLFunction, TagInverse, TagSorting])
               [ LeanAxiom (nr ++ minSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar nr) (LVar (sortMinName argSort))))
               , LeanAxiom (nr ++ maxSuffixForAxiomNames)
                   (LImpl pMin (LImpl (LVar (sortMaxName argSort)) (LVar nr)))
               ]
           ]

  -- -------------------------------------------------------------------------
  -- 21. Projection witness sorting axioms
  -- -------------------------------------------------------------------------
  projectionWitnessSortingAxiomSets :: [AxiomSet]
  projectionWitnessSortingAxiomSets = concatMap mkProjSorting multiArgFolFunctions
    where
      mkProjSorting f =
        let dMn = domMinName f
            dMx = domMaxName f
        in concatMap (mkOne dMn dMx) (zip [1..] (IR.funcArgSorts f))
        where
          mkOne dMn dMx (k, srt) =
            let n1 = piName f k ++ "_1"
                nr = piName f k ++ "_res"
                sN = IR.sortName srt
            in [ axiomSet [SFunction (IR.funcName f), SProjection k, SArgObject 1]
                          (tags [TagFunction, TagFOLFunction, TagProjection, TagSorting])
                   [ LeanAxiom (n1 ++ minSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar n1) (LVar dMn)))
                   , LeanAxiom (n1 ++ maxSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar dMx) (LVar n1)))
                   ]
               , axiomSet [SFunction (IR.funcName f), SProjection k, SResObject]
                          (tags [TagFunction, TagFOLFunction, TagProjection, TagSorting])
                   [ LeanAxiom (nr ++ minSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar nr) (LVar (sortMinName sN))))
                   , LeanAxiom (nr ++ maxSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar (sortMaxName sN)) (LVar nr)))
                   ]
               ]

  -- -------------------------------------------------------------------------
  -- 22. Function connection axioms (f_fact, g_fact, etc.)
  -- -------------------------------------------------------------------------
  functionConnectionAxiomSets :: [AxiomSet]
  functionConnectionAxiomSets =
    concatMap mkConn (solFunctions ++ userDeclaredFolFunctions)
    where
      mkConn f =
        [ axiomSet [SFunction (IR.funcName f)]
                   (tags [TagFunction, TagConnection])
            [mkConnectionAxiom f]
        ]
      mkConnectionAxiom f =
        let fName    = IR.funcName f
            argObjs  = IR.funcArgObjects f
            resObj   = IR.funcResObject f
            argCount = length argObjs
            argVarNames = ["X" ++ show i | i <- [1..argCount]]
            resVarName  = "X" ++ show (argCount + 1)
            argEqs = [ LEq (LVar varN) (LVar (sanitizeName (IR.mereoName obj)))
                     | (varN, obj) <- zip argVarNames argObjs ]
            resEq  = LEq (LVar resVarName)
                         (LVar (sanitizeName (IR.mereoName resObj)))
            lhsConj = case argEqs of
              []     -> resEq
              (e:es) -> foldl LConj e (es ++ [resEq])
            funcApp = LApp (LVar fName) (map LVar argVarNames)
            rhsEq   = LEq (LVar resVarName) funcApp
            body    = LBicond lhsConj rhsEq
            sortOf obj = IR.sortName (IR.mereoSort obj)
            mkBQ varN sN = bForall varN (fst (sortBounds sN)) (snd (sortBounds sN))
            quantified  =
              foldr (\(varN, obj) acc -> mkBQ varN (sortOf obj) acc)
                    (mkBQ resVarName (sortOf resObj) body)
                    (zip argVarNames argObjs)
        in LeanAxiom (fName ++ "_fact") quantified

  -- -------------------------------------------------------------------------
  -- 23. FOL inverse connection axioms
  -- -------------------------------------------------------------------------
  folInverseConnectionAxiomSets :: [AxiomSet]
  folInverseConnectionAxiomSets = map mkInvConn folSingleArgFunctions
    where
      mkInvConn f =
        axiomSet [SFunction (IR.funcName f), SInverse]
                 (tags [TagFunction, TagFOLFunction, TagInverse, TagConnection])
          [mkInvConnectionAxiom f]
      mkInvConnectionAxiom f =
        let fInv    = invName f
            argSort = IR.sortName (head (IR.funcArgSorts f))
            resSort = IR.sortName (IR.funcResSort f)
            n1      = fInv ++ "_1"
            nr      = fInv ++ "_res"
            lhs     = LConj (LEq (LVar "X1") (LVar n1))
                            (LEq (LVar "X2") (LVar nr))
            rhs     = LEq (LVar "X2") (LApp (LVar fInv) [LVar "X1"])
            body    = LBicond lhs rhs
            q2      = bForall "X2" (sortMinName argSort) (sortMaxName argSort) body
            q1      = bForall "X1" (sortMinName resSort) (sortMaxName resSort) q2
        in LeanAxiom (fInv ++ "_fact") q1

  -- -------------------------------------------------------------------------
  -- 24. Direct image connection axioms
  -- -------------------------------------------------------------------------
  dirImgConnectionAxiomSets :: [AxiomSet]
  dirImgConnectionAxiomSets = concatMap mkDirImgConn multiArgFolFunctions
    where
      mkDirImgConn f =
        case IR.funcArgument f of
          Nothing  -> []
          Just arg ->
            let dMn  = domMinName f
                dMx  = domMaxName f
                rSN  = IR.sortName (IR.funcResSort f)
                argN = sanitizeName (IR.mereoName arg)
                resN = sanitizeName (IR.mereoName (IR.funcResObject f))
                lhs  = LConj (LEq (LVar "A") (LVar argN))
                             (LEq (LVar "B") (LVar resN))
                rhs  = LEq (LVar "B") (LApp (LVar (dirImgName f)) [LVar "A"])
                body = LBicond lhs rhs
                qB   = bForall "B" (sortMinName rSN) (sortMaxName rSN) body
                qA   = bForall "A" dMn dMx qB
            in [ axiomSet [SFunction (IR.funcName f), SImage]
                          (tags [TagFunction, TagFOLFunction, TagImage, TagConnection])
                   [LeanAxiom (dirImgName f ++ "_fact") qA]
               ]

  -- -------------------------------------------------------------------------
  -- 25. Inverse image connection axioms
  -- -------------------------------------------------------------------------
  invImgConnectionAxiomSets :: [AxiomSet]
  invImgConnectionAxiomSets = map mkInvImgConn multiArgFolFunctions
    where
      mkInvImgConn f =
        let fN   = invImgName f
            argN = fN ++ "_arg"
            resN = fN ++ "_res"
            rSN  = IR.sortName (IR.funcResSort f)
            dMn  = domMinName f
            dMx  = domMaxName f
            lhs  = LConj (LEq (LVar "A") (LVar argN))
                         (LEq (LVar "B") (LVar resN))
            rhs  = LEq (LVar "B") (LApp (LVar fN) [LVar "A"])
            body = LBicond lhs rhs
            qB   = bForall "B" dMn dMx body
            qA   = bForall "A" (sortMinName rSN) (sortMaxName rSN) qB
        in axiomSet [SFunction (IR.funcName f), SImage]
                    (tags [TagFunction, TagFOLFunction, TagImage, TagConnection])
             [LeanAxiom (fN ++ "_fact") qA]

  -- -------------------------------------------------------------------------
  -- 26. FOL adjunction axioms
  -- -------------------------------------------------------------------------
  folAdjunctionAxiomSets :: [AxiomSet]
  folAdjunctionAxiomSets = map mkAdj folSingleArgFunctions
    where
      mkAdj f =
        let fN      = IR.funcName f
            argSort = IR.sortName (head (IR.funcArgSorts f))
            resSort = IR.sortName (IR.funcResSort f)
            fX      = LApp (LVar fN) [LVar "X"]
            fInvY   = LApp (LVar (invName f)) [LVar "Y"]
            lhs     = LImpl (LVar "Y") fX
            rhs     = LImpl fInvY (LVar "X")
            body    = LBicond lhs rhs
            qY      = bForall "Y" (sortMinName resSort) (sortMaxName resSort) body
            qX      = bForall "X" (sortMinName argSort) (sortMaxName argSort) qY
        in axiomSet [SFunction fN, SInverse]
                    (tags [TagFunction, TagFOLFunction, TagInverse, TagAdjunction])
             [LeanAxiom (fN ++ "_adjunction") qX]

  -- -------------------------------------------------------------------------
  -- 27. Image adjunction axioms
  -- -------------------------------------------------------------------------
  imageAdjunctionAxiomSets :: [AxiomSet]
  imageAdjunctionAxiomSets = map mkAdj multiArgFolFunctions
    where
      mkAdj f =
        let dMn  = domMinName f
            dMx  = domMaxName f
            rSN  = IR.sortName (IR.funcResSort f)
            dirX = LApp (LVar (dirImgName f)) [LVar "X"]
            invY = LApp (LVar (invImgName f)) [LVar "Y"]
            lhs  = LImpl (LVar "Y") dirX
            rhs  = LImpl invY (LVar "X")
            body = LBicond lhs rhs
            qY   = bForall "Y" (sortMinName rSN) (sortMaxName rSN) body
            qX   = bForall "X" dMn dMx qY
        in axiomSet [SFunction (IR.funcName f), SImage]
                    (tags [TagFunction, TagFOLFunction, TagImage, TagAdjunction])
             [LeanAxiom (IR.funcName f ++ "_image_adjunction") qX]

  -- -------------------------------------------------------------------------
  -- 28. Decomposition axioms: f = f_dir_img ∘ f_tuple
  -- -------------------------------------------------------------------------
  decompositionAxiomSets :: [AxiomSet]
  decompositionAxiomSets = map mkDecomp multiArgFolFunctions
    where
      mkDecomp f =
        let fN      = IR.funcName f
            argSNs  = map IR.sortName (IR.funcArgSorts f)
            varNs   = ["X" ++ show i | i <- [1..length argSNs]]
            tupleApp = LApp (LVar (tupleName f)) (map LVar varNs)
            dirApp   = LApp (LVar (dirImgName f)) [tupleApp]
            fApp     = LApp (LVar fN) (map LVar varNs)
            body     = LEq fApp dirApp
            quantified =
              foldr (\(varN, sN) acc ->
                        bForall varN (sortMinName sN) (sortMaxName sN) acc)
                    body (zip varNs argSNs)
        in axiomSet [SFunction fN]
                    (tags [TagFunction, TagFOLFunction, TagDecomposition])
             [LeanAxiom (fN ++ "_decomposition") quantified]

  -- -------------------------------------------------------------------------
  -- 29. Tuple connection axioms: f_tuple_fact
  -- -------------------------------------------------------------------------
  tupleFact_AxiomSets :: [AxiomSet]
  tupleFact_AxiomSets = concatMap mkTupleFact multiArgFolFunctions
    where
      mkTupleFact f =
        case IR.funcArgument f of
          Nothing  -> []
          Just arg ->
            let argObjs  = IR.funcArgObjects f
                argSorts = IR.funcArgSorts f
                arity    = length argObjs
                argVars  = ["X" ++ show i | i <- [1..arity]]
                resVar   = "X" ++ show (arity + 1)
                dMn      = domMinName f
                dMx      = domMaxName f
                argN     = sanitizeName (IR.mereoName arg)
                argEqs   = [ LEq (LVar xi) (LVar (sanitizeName (IR.mereoName obj)))
                           | (xi, obj) <- zip argVars argObjs ]
                resEq    = LEq (LVar resVar) (LVar argN)
                lhsConj  = case argEqs of
                  []     -> resEq
                  (e:es) -> foldl LConj e (es ++ [resEq])
                tupleApp = LApp (LVar (tupleName f)) (map LVar argVars)
                rhsEq    = LEq (LVar resVar) tupleApp
                body     = LBicond lhsConj rhsEq
                mkArgQ (varN, sN) acc =
                  bForall varN (sortMinName sN) (sortMaxName sN) acc
                resQ acc = bForall resVar dMn dMx acc
                quantified =
                  foldr mkArgQ (resQ body) (zip argVars (map IR.sortName argSorts))
            in [ axiomSet [SFunction (IR.funcName f), STuple]
                          (tags [TagFunction, TagFOLFunction, TagTuple, TagConnection])
                   [LeanAxiom (tupleName f ++ "_fact") quantified]
               ]

  -- -------------------------------------------------------------------------
  -- 30. Projection connection axioms: f_pi_k_fact
  -- -------------------------------------------------------------------------
  projectionConnectionAxiomSets :: [AxiomSet]
  projectionConnectionAxiomSets = concatMap mkProjConn multiArgFolFunctions
    where
      mkProjConn f =
        let dMn = domMinName f
            dMx = domMaxName f
        in [ mkOne dMn dMx k srt
           | (k, srt) <- zip [1..] (IR.funcArgSorts f) ]
        where
          mkOne dMn dMx k srt =
            let n1   = piName f k ++ "_1"
                nr   = piName f k ++ "_res"
                sN   = IR.sortName srt
                lhs  = LConj (LEq (LVar "X1") (LVar n1))
                             (LEq (LVar "X2") (LVar nr))
                rhs  = LEq (LVar "X2") (LApp (LVar (piName f k)) [LVar "X1"])
                body = LBicond lhs rhs
                qX2  = bForall "X2" (sortMinName sN) (sortMaxName sN) body
                qX1  = bForall "X1" dMn dMx qX2
            in axiomSet [SFunction (IR.funcName f), SProjection k]
                        (tags [TagFunction, TagFOLFunction, TagProjection, TagConnection])
                 [LeanAxiom (piName f k ++ "_fact") qX1]

  -- -------------------------------------------------------------------------
  -- 31. Projection adjunction axioms: f_pi_k_adjunction
  -- -------------------------------------------------------------------------
  projectionAdjunctionAxiomSets :: [AxiomSet]
  projectionAdjunctionAxiomSets = concatMap mkProjAdj multiArgFolFunctions
    where
      mkProjAdj f =
        [ mkOneAdj f k srt
        | (k, srt) <- zip [1..] (IR.funcArgSorts f) ]
        where
          mkOneAdj f k srt =
            let dMn    = domMinName f
                dMx    = domMaxName f
                sN     = IR.sortName srt
                piN    = piName f k
                piInvN = piInvName f k
                piX    = LApp (LVar piN) [LVar "X"]
                piInvY = LApp (LVar piInvN) [LVar "Y"]
                lhs    = LImpl (LVar "Y") piX
                rhs    = LImpl piInvY (LVar "X")
                body   = LBicond lhs rhs
                qY     = bForall "Y" (sortMinName sN) (sortMaxName sN) body
                qX     = bForall "X" dMn dMx qY
            in axiomSet [SFunction (IR.funcName f), SProjection k, SInverse]
                        (tags [TagFunction, TagFOLFunction, TagProjection, TagInverse, TagAdjunction])
                 [LeanAxiom (piN ++ "_adjunction") qX]

  -- -------------------------------------------------------------------------
  -- 32. Tuple inverse decomposition: f_tuple = f_pi_1_inv ∩ f_pi_2_inv ∩ ...
  -- -------------------------------------------------------------------------
  tupleInvDecompAxiomSets :: [AxiomSet]
  tupleInvDecompAxiomSets = map mkTupleInvDecomp multiArgFolFunctions
    where
      mkTupleInvDecomp f =
        let argSNs   = map IR.sortName (IR.funcArgSorts f)
            arity    = length argSNs
            varNs    = ["X" ++ show i | i <- [1..arity]]
            tupleApp = LApp (LVar (tupleName f)) (map LVar varNs)
            invApps  = [ LApp (LVar (piInvName f k)) [LVar xk]
                       | (k, xk) <- zip [1..] varNs ]
            meetExpr = foldl1 LConj invApps
            body     = LEq tupleApp meetExpr
            quantified =
              foldr (\(varN, sN) acc ->
                        bForall varN (sortMinName sN) (sortMaxName sN) acc)
                    body (zip varNs argSNs)
        in axiomSet [SFunction (IR.funcName f), STuple]
                    (tags [TagFunction, TagFOLFunction, TagTuple, TagInvDecomposition])
             [LeanAxiom (tupleName f ++ "_inv_decomposition") quantified]

  -- -------------------------------------------------------------------------
  -- 33. IR tuple-with-projections axioms
  -- -------------------------------------------------------------------------
  irTupleProjAxiomSets :: [AxiomSet]
  irTupleProjAxiomSets = map mkIRTuple multiArgFolFunctions
    where
      mkIRTuple f =
        let dMn     = domMinName f
            dMx     = domMaxName f
            irN     = irPredicateName f
            arity   = length (IR.funcArgSorts f)
            piApps  = [LApp (LVar (piName f k)) [LVar "Z"] | k <- [1..arity]]
            tupleApp = LApp (LVar (tupleName f)) piApps
            irZ     = LApp (LVar irN) [LVar "Z"]
            body    = LBicond irZ (LEq (LVar "Z") tupleApp)
            qZ      = bForall "Z" dMn dMx body
        in axiomSet [SFunction (IR.funcName f), SIR]
                    (tags [TagFunction, TagFOLFunction, TagIR, TagIRTupleProj])
             [LeanAxiom (irN ++ "_tuple_with_projections") qZ]

  -- -------------------------------------------------------------------------
  -- 34. IR projections-from-tuple axioms
  -- -------------------------------------------------------------------------
  irProjFromTupleAxiomSets :: [AxiomSet]
  irProjFromTupleAxiomSets = map mkIRProj multiArgFolFunctions
    where
      mkIRProj f =
        let argSNs   = map IR.sortName (IR.funcArgSorts f)
            arity    = length argSNs
            varNs    = ["X" ++ show i | i <- [1..arity]]
            irN      = irPredicateName f
            tupleApp = LApp (LVar (tupleName f)) (map LVar varNs)
            irTuple  = LApp (LVar irN) [tupleApp]
            projEqs  = [ LEq (LApp (LVar (piName f k)) [tupleApp]) (LVar xk)
                       | (k, xk) <- zip [1..] varNs ]
            rhsConj  = foldl1 LConj projEqs
            body     = LBicond irTuple rhsConj
            quantified =
              foldr (\(varN, sN) acc ->
                        bForall varN (sortMinName sN) (sortMaxName sN) acc)
                    body (zip varNs argSNs)
        in axiomSet [SFunction (IR.funcName f), SIR]
                    (tags [TagFunction, TagFOLFunction, TagIR, TagIRProjFromTuple])
             [LeanAxiom (irN ++ "_projections_from_tuple") quantified]

  -- -------------------------------------------------------------------------
  -- 35. IR separates axioms
  -- -------------------------------------------------------------------------
  irSeparatesAxiomSets :: [AxiomSet]
  irSeparatesAxiomSets = map mkIRSep multiArgFolFunctions
    where
      mkIRSep f =
        let dMn  = domMinName f
            dMx  = domMaxName f
            irN  = irPredicateName f
            irZ  = LApp (LVar irN) [LVar "Z"]
            body = LBicond (LImpl (LVar "X") (LVar "Z"))
                           (LImpl (LVar "Y") (LVar "Z"))
            inner = LImpl irZ body
            qZ    = bForall "Z" dMn dMx inner
            sep   = LBicond (LEq (LVar "X") (LVar "Y")) qZ
            qY    = bForall "Y" dMn dMx sep
            qX    = bForall "X" dMn dMx qY
        in axiomSet [SFunction (IR.funcName f), SIR]
                    (tags [TagFunction, TagFOLFunction, TagIR, TagIRSeparates])
             [LeanAxiom (irN ++ "_separates") qX]

  -- -------------------------------------------------------------------------
  -- 36. Mereological object bounds
  -- -------------------------------------------------------------------------
  mereoBoundsAxiomSets :: [AxiomSet]
  mereoBoundsAxiomSets = map mkMereoBounds mereoObjects
    where
      mkMereoBounds m =
        let n = IR.mereoName m
        in axiomSet [SGlobal] (tags [TagSorting])
             [ LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) uMin)
             , LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl uMax (LVar n))
             ]

  -- -------------------------------------------------------------------------
  -- 37. Propositional object bounds
  -- -------------------------------------------------------------------------
  propBoundsAxiomSets :: [AxiomSet]
  propBoundsAxiomSets = map mkPropBounds propObjects
    where
      mkPropBounds m =
        let n = IR.mereoName m
        in axiomSet [SGlobal] (tags [TagSorting])
             [ LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) pMin)
             , LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl pMax (LVar n))
             ]

  -- -------------------------------------------------------------------------
  -- 38. 𝔻-sorted set bounds
  -- -------------------------------------------------------------------------
  setBoundsAxiomSets :: [AxiomSet]
  setBoundsAxiomSets = map mkSetBounds setObjects
    where
      mkSetBounds m =
        let n = IR.mereoName m
        in axiomSet [SGlobal] (tags [TagSorting])
             [ LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) (LVar "D_Min"))
             , LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl (LVar "D_Max") (LVar n))
             ]

  -- -------------------------------------------------------------------------
  -- 39. User sort set bounds
  -- -------------------------------------------------------------------------
  userSortSetBoundsAxiomSets :: [AxiomSet]
  userSortSetBoundsAxiomSets = map mkSetBounds userSortSets
    where
      mkSetBounds m =
        let n    = IR.mereoName m
            sN   = IR.sortName (IR.mereoSort m)
            sMin = sortMinName sN
            sMax = sortMaxName sN
        in axiomSet [SSet n] (tags [TagSet, TagSorting])
             [ LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) (LVar sMin))
             , LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl (LVar sMax) (LVar n))
             ]

  -- -------------------------------------------------------------------------
  -- 40. Sort ordering axioms
  -- -------------------------------------------------------------------------
  sortOrderAxiomSets :: [AxiomSet]
  sortOrderAxiomSets =
    [ axiomSet [SGlobal] (tags [TagSort, TagOrdering])
        (  [ LeanAxiom "U_ordering" (LImpl uMax uMin)
           , LeanAxiom "U_to_P"     (LImpl uMax pMax)
           , LeanAxiom "P_ordering" (LImpl pMax pMin)
           , LeanAxiom "P_to_U"     (LImpl pMin uMin)
           ]
        ++  if usesDomain then
              [ LeanAxiom "D_upper"    (LImpl uMax (LVar "D_Max"))
              , LeanAxiom "D_ordering" (LImpl (LVar "D_Max") (LVar "D_Min"))
              , LeanAxiom "D_lower"    (LImpl (LVar "D_Min") pMax)
              ]
            else []
        )
    ]
    ++ map mkUserSortOrder userSorts
    where
      mkUserSortOrder s =
        let sN   = IR.sortName s
            sMax = sortMaxName sN
            sMin = sortMinName sN
        in axiomSet [SSort sN] (tags [TagSort, TagOrdering])
             [ LeanAxiom (sN ++ "_upper")    (LImpl uMax (LVar sMax))
             , LeanAxiom (sN ++ "_ordering") (LImpl (LVar sMax) (LVar sMin))
             , LeanAxiom (sN ++ "_lower")    (LImpl (LVar sMin) pMax)
             ]

  -- -------------------------------------------------------------------------
  -- 41. Product sort ordering axioms
  -- -------------------------------------------------------------------------
  productSortOrderAxiomSets :: [AxiomSet]
  productSortOrderAxiomSets = map mkOrder multiArgFolFunctions
    where
      mkOrder f =
        let fN  = IR.funcName f
            dMx = domMaxName f
            dMn = domMinName f
        in axiomSet [SFunction fN, STuple] (tags [TagSort, TagFOLFunction, TagTuple, TagOrdering])
             [ LeanAxiom (fN ++ "_dom_upper")   (LImpl uMax (LVar dMx))
             , LeanAxiom (fN ++ "_dom_ordering") (LImpl (LVar dMx) (LVar dMn))
             , LeanAxiom (fN ++ "_dom_lower")   (LImpl (LVar dMn) pMax)
             ]

  -- -------------------------------------------------------------------------
  -- 42. User fact axioms
  -- -------------------------------------------------------------------------
  userFactAxiomSets :: [AxiomSet]
  userFactAxiomSets =
       zipWith mkAssertionAS [1..] userAssertions
    ++ zipWith mkMetafactAS  [1 + length userAssertions..] userMetafacts
    where
      totalFacts = length userAssertions + length userMetafacts
      mkLabel idx = if totalFacts > 1 then "ax" ++ show idx else ""

      mkAssertionAS idx fact =
        axiomSet [SGlobal] (tags [TagUserFact])
          [LeanAxiom (mkLabel idx)
            (LBicond (LConj pMin (factBodyExpr fact)) pMin)]

      mkMetafactAS idx fact =
        axiomSet [SGlobal] (tags [TagUserFact])
          [LeanAxiom (mkLabel idx)
            (LBicond (LConj uMin (factBodyExpr fact)) uMin)]

      factBodyExpr fact =
        wrapFreeVars' (IR.factFreeVars fact) (propExprToLean' (IR.factPropExpr fact))

      -- Inline free-var wrapper (mirrors LeanProps.wrapFreeVars)
      wrapFreeVars' [] body = body
      wrapFreeVars' (vd:rest) body =
        let varN     = IR.resolvedVarName vd
            sn       = IR.sortName (IR.resolvedVarSort vd)
            (lo, hi) = sortBounds sn
        in LBoundedForall varN lo hi (wrapFreeVars' rest body)

      -- Inline prop-expr translator (mirrors LeanProps.propExprToLean)
      propExprToLean' = propExprToLean

propExprToLean :: IR.ResolvedPropExpr -> LeanExpr
propExprToLean (IR.ResolvedPropBicond lhs rests) =
  case rests of
    []    -> rightImplToLean lhs
    (r:_) -> LBicond (rightImplToLean lhs)
                     (rightImplToLean (IR.resolvedPropRestRight r))

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

quantifierToLean :: IR.ResolvedQuantifier -> LeanExpr -> LeanExpr
quantifierToLean (IR.ResolvedQForall vd) body =
  let varN     = IR.resolvedVarName vd
      sn       = IR.sortName (IR.resolvedVarSort vd)
      (lo, hi) = sortBounds sn
  in LBoundedForall varN lo hi body
quantifierToLean (IR.ResolvedQExists vd) body =
  let varN     = IR.resolvedVarName vd
      sn       = IR.sortName (IR.resolvedVarSort vd)
      (lo, hi) = sortBounds sn
  in LExists varN (LVar "Prop") (LImpl (LIsWithinBounds lo varN hi) body)

atomicPropToLean :: IR.ResolvedAtomicProp -> LeanExpr
atomicPropToLean (IR.ResolvedAtomicConstant ref) = LVar (resolveConstRef ref)
atomicPropToLean (IR.ResolvedAtomicTermPair tp)  = termPairToLean tp

resolveConstRef :: IR.ResolvedConstantRef -> String
resolveConstRef = resolveName . IR.resolvedConstRefName

resolveName :: String -> String
resolveName n = case n of
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
termPairToLean (IR.ResolvedTermPair lhs rights _) =
  foldl applyRelOp (termToLean lhs) rights

applyRelOp :: LeanExpr -> IR.ResolvedRelationFollowedByTerm -> LeanExpr
applyRelOp leftExpr rfbt =
  let op    = IR.resolvedRFTOp rfbt
      right = termToLean (IR.resolvedRFTRight rfbt)
  in case op of
       "+"  -> LConj   leftExpr right
       "×"  -> LDisj   leftExpr right
       "-"  -> LImpl   right leftExpr
       "∸"  -> LBicond leftExpr right
       "="  -> LBicond leftExpr right
       "≤"  -> LImpl   leftExpr right
       "∪"  -> LConj   leftExpr right
       "∩"  -> LDisj   leftExpr right
       "⊆"  -> LImpl   right leftExpr
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
baseTermToLean (IR.ResolvedBTParen expr) =
  propExprToLean expr
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
  termToLean (IR.resolvedGSPOperand gsp)
