-- | Export an Eidos theory to Lean 4 using the "all Props" strategy.
--
-- The pipeline has two stages:
--
--   1. 'theoryToLeanDoc' – converts an 'IR.Theory' into a 'LeanDoc', a
--      structured internal representation of every declaration the output
--      will contain.  This is the stage you unit-test.
--
--   2. 'renderLeanDoc' – pretty-prints a 'LeanDoc' to a 'String' of Lean 4
--      source.
--
-- The public entry point 'exportToLeanProps' just composes the two.
--
-- == Encoding conventions
--
-- * A 𝕌-kinded object @P@ gets bounds axioms @P → U_Min@ and @U_Max → P@.
-- * A ℙ-kinded object @P@ gets bounds axioms @P → P_Min@ and @P_Max → P@.
-- * A 𝔻-kinded set @S@ gets bounds axioms @S → D_Min@ and @D_Max → S@.
-- * A user-sort set @S ⊆ T@ gets bounds axioms @S → T_Min@ and @T_Max → S@.
-- * @A - B@ (mereological difference) renders as @B → A@.
-- * @+, ×, ∸@ map to @∧, ∨, ↔@.
-- * Assertions are wrapped with @P_Min@; metafacts with @U_Min@.
module Eidos.Export.LeanProps
  ( -- * Internal representation (re-exported from Eidos.Export.LeanExpr)
    LeanDoc (..)
  , LeanDecl (..)
  , LeanAxiom (..)
  , LeanExpr (..)
    -- * Pipeline stages
  , theoryToLeanDoc
  , renderLeanDoc
  , renderLeanExpr
    -- * Convenience entry point
  , LeanPropsOptions (..)
  , defaultLeanPropsOptions
  , exportToLeanPropsWithOptions
  , exportToLeanProps
  ) where

import qualified Eidos.IR as IR
import Eidos.Export.LeanExpr
import Data.List (sortOn)
import Eidos.Export.MkAxiomSets (mkAxiomSets)
import Eidos.Export.LeanAxiomSet

-- ---------------------------------------------------------------------------
-- Naming conventions
-- ---------------------------------------------------------------------------
-- Base names for built-in sorts
uName, pName, dName :: String
uName = "U"
pName = "P"
dName = "D"

-- Suffixes for bounds
minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

minSuffixForAxiomNames, maxSuffixForAxiomNames :: String
minSuffixForAxiomNames = "_min"
maxSuffixForAxiomNames = "_max"

-- Bound object NAMES (as Strings)
uMinName, uMaxName, pMinName, pMaxName, dMinName, dMaxName :: String
uMinName = uName ++ minSuffix
uMaxName = uName ++ maxSuffix
pMinName = pName ++ minSuffix
pMaxName = pName ++ maxSuffix
dMinName = dName ++ minSuffix
dMaxName = dName ++ maxSuffix

-- Bound object EXPRESSIONS (as LeanExpr)
uMin, uMax, pMin, pMax, dMin, dMax :: LeanExpr
uMin = LVar uMinName
uMax = LVar uMaxName
pMin = LVar pMinName
pMax = LVar pMaxName
dMin = LVar dMinName
dMax = LVar dMaxName

-- User sort bound names (as Strings)
sortMinName, sortMaxName :: String -> String
sortMinName name = name ++ minSuffix
sortMaxName name = name ++ maxSuffix

-- Helper to convert names with # to _
sanitizeName :: String -> String
sanitizeName = map (\c -> if c == '#' then '_' else c)



-- ---------------------------------------------------------------------------
-- Stage 1 – Theory → LeanDoc
-- ---------------------------------------------------------------------------

-- | Prepend a blank line to a non-empty list of decls, producing a visually
--   separated section.  Empty lists are left empty (no spurious blank lines).
section :: [LeanDecl] -> [LeanDecl]
section [] = []
section ds = DeclBlankLine : ds

-- | Convert an Eidos 'IR.Theory' into a structured 'LeanDoc'.
theoryToLeanDoc :: IR.Theory -> LeanDoc
theoryToLeanDoc theory = LeanDoc
  { leanDocTheoryName = IR.theoryFullyQualifiedName theory
  , leanDocDecls      = concatMap section
      [ headerDecls
      , userSortLimitDecls
      , productSortLimitDecls
      , functionDecls
      , imageFunctionDecls
      , projectionFunctionDecls
      , projectionInverseFunctionDecls
      , tupleFunctionDecls
      , folInverseDecls
      , irPredicateDecls
      , functionArgResultDecls
      , folInverseArgResDecls
      , productArgDecls
      , projectionWitnessDecls
      , invImgWitnessDecls
      , mereoDecls
      , propDecls
      , setDecls
      , functionArgResultBoundsAxioms
      , folInverseArgResBoundsAxioms
      , projectionWitnessBoundsAxioms
      , functionFactAxioms
      , folInverseFactAxioms
      , dirImgFactAxioms
      , invImgFactAxioms
      , folAdjunctionAxioms
      , imageAdjunctionAxioms
      , decompositionAxioms
      , tupleFact
      , projectionFacts
      , projectionAdjunctionAxioms
      , tupleInverseDecompositionFacts
      , irTupleWithProjectionsAxioms
      , irProjectionsFromTupleAxioms
      , irSeparationAxioms
      , mereoBoundsAxioms
      , propBoundsAxioms
      , setBoundsAxioms
      , userSortSetBoundsAxioms
      , sortOrderDecls
      , productSortOrderAxioms
      , userFactDecls
      ]
  }
  where
    -- | Smart constructor for bounded universal quantification.
    -- Replaces the verbose pattern:
    --   LForallKw var LProp (LImpl (LIsWithinBounds lo var hi) body)
    -- with a single, introspectable node.
    bForall :: String -> String -> String -> LeanExpr -> LeanExpr
    bForall = LBoundedForall

    usesDomain :: Bool
    usesDomain = IR.theoryUsesDomain theory

    -- -----------------------------------------------------------------------
    -- Header – the four or six built-in bound objects
    -- -----------------------------------------------------------------------
    headerDecls :: [LeanDecl]
    headerDecls =
      [ DeclAxiom (LeanAxiom uMinName LProp)
      , DeclAxiom (LeanAxiom uMaxName LProp)
      , DeclAxiom (LeanAxiom pMinName LProp)
      , DeclAxiom (LeanAxiom pMaxName LProp)
      ] ++ (if usesDomain
            then [ DeclAxiom (LeanAxiom dMinName LProp)
                 , DeclAxiom (LeanAxiom dMaxName LProp)
                 ]
            else [])

    -- -----------------------------------------------------------------------
    -- User-declared sorts: S_Min / S_Max limit objects
    -- -----------------------------------------------------------------------
    userSorts :: [IR.Sort]
    userSorts =
      [ s
      | IR.EntitySort s <- IR.theoryObjects theory
      , IR.sortKind s == IR.SortKindFromSignature
      ]

    userSortLimitDecls :: [LeanDecl]
    userSortLimitDecls = concatMap mkSortLimitDecls userSorts
      where
        mkSortLimitDecls s =
          [ DeclAxiom (LeanAxiom (sortMinName (IR.sortName s)) LProp)
          , DeclAxiom (LeanAxiom (sortMaxName (IR.sortName s)) LProp)
          ]

    -- -----------------------------------------------------------------------
    -- SOL function declarations (F, G, H, IdS, etc.)
    -- -----------------------------------------------------------------------
    solFunctions :: [IR.Function]
    solFunctions = IR.theorySOLFunctions theory

    -- Build function type: Prop → Prop → ... → Prop
    functionType :: IR.Function -> LeanExpr
    functionType f = 
      let arity = length (IR.funcArgObjects f)
          buildImpl 0 = LProp
          buildImpl n = foldr (\_ acc -> LImpl LProp acc) LProp [1..n]
      in buildImpl arity

    functionDecls :: [LeanDecl]
    functionDecls =
         map (\f -> DeclAxiom (LeanAxiom (IR.funcName f) (functionType f))) solFunctions
      ++ map (\f -> DeclAxiom (LeanAxiom (IR.funcName f) (functionType f))) userDeclaredFolFunctions

    -- -----------------------------------------------------------------------
    -- FOL functions
    -- -----------------------------------------------------------------------
    folFunctions :: [IR.Function]
    folFunctions = IR.theoryFOLFunctions theory

    -- Only user-declared single-argument FOL functions get an inverse.
    -- We exclude auto-generated functions (origin /= FromSignature) so that
    -- _inv functions don't themselves spawn _inv_inv functions.
    folSingleArgFunctions :: [IR.Function]
    folSingleArgFunctions =
      filter (\f -> length (IR.funcArgSorts f) == 1
                 && IR.funcOrigin f == IR.FromSignature)
             folFunctions

    -- Inverse name convention: append "_inv"
    invName :: IR.Function -> String
    invName f = IR.funcName f ++ "_inv"

    -- FOL inverse declarations (single-arg, user-declared only)
    folInverseDecls :: [LeanDecl]
    folInverseDecls =
      map (\f -> DeclAxiom (LeanAxiom (invName f) (LImpl LProp LProp)))
          folSingleArgFunctions

    -- Adjunction axioms for user-declared single-arg FOL functions only.
    -- f_adjunction connects f and f_inv; we do NOT generate inv_adjunction.
    -- Multi-arg functions (like f : S,S → T) are excluded — they would need
    -- product sorts which are not yet axiomatised.
    folAdjunctionAxioms :: [LeanDecl]
    folAdjunctionAxioms = map mkAdjunction folSingleArgFunctions
      where
        mkAdjunction f =
          let fN      = IR.funcName f
              argSort = IR.sortName (head (IR.funcArgSorts f))
              resSort = IR.sortName (IR.funcResSort f)
              -- forall X : Prop, (IsWithinBounds argSort_Min argSort_Max X) →
              -- forall Y : Prop, (IsWithinBounds resSort_Min resSort_Max Y) →
              --   (f(X) ⊆ Y ↔ X ⊆ f_inv(Y))
              -- A ⊆ B  =>  B → A
              fX      = LApp (LVar fN) [LVar "X"]
              fInvY   = LApp (LVar (invName f)) [LVar "Y"]
              lhs     = LImpl (LVar "Y") fX       -- f(X) ⊆ Y
              rhs     = LImpl fInvY (LVar "X")     -- X ⊆ f_inv(Y)
              body    = LBicond lhs rhs
              innerQ  = bForall "Y" (sortMinName resSort) (sortMaxName resSort) body
              outerQ  = bForall "X" (sortMinName argSort) (sortMaxName argSort) innerQ
          in DeclAxiom (LeanAxiom (fN ++ "_adjunction") outerQ)

    -- Synthetic arg/res object declarations for _inv functions.
    -- We build these manually from the original function so we can use the
    -- correct sorts (argSort for inv-result, resSort for inv-argument),
    -- rather than relying on the IR-generated domain/product sorts.
    folInverseObjects :: [(String, String, String, String)]
    -- Each tuple: (inv_1_name, argSortName, inv_res_name, resSortName)
    -- inv takes resSort → argSort, so:
    --   inv_1  lives in resSort  (what you feed in)
    --   inv_res lives in argSort  (what comes out)
    folInverseObjects =
      [ ( invName f ++ "_1"
        , IR.sortName (IR.funcResSort f)
        , invName f ++ "_res"
        , IR.sortName (head (IR.funcArgSorts f))
        )
      | f <- folSingleArgFunctions
      ]

    folInverseArgResDecls :: [LeanDecl]
    folInverseArgResDecls =
      concatMap (\(n1,_,nr,_) ->
        [ DeclAxiom (LeanAxiom n1 LProp)
        , DeclAxiom (LeanAxiom nr LProp)
        ])
        folInverseObjects

    folInverseArgResBoundsAxioms :: [LeanDecl]
    folInverseArgResBoundsAxioms =
      concatMap mkBounds folInverseObjects
      where
        mkBounds (n1, s1, nr, sr) =
          [ DeclAxiom (LeanAxiom (n1 ++ minSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar n1) (LVar (sortMinName s1)))))
          , DeclAxiom (LeanAxiom (n1 ++ maxSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar (sortMaxName s1)) (LVar n1))))
          , DeclAxiom (LeanAxiom (nr ++ minSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar nr) (LVar (sortMinName sr)))))
          , DeclAxiom (LeanAxiom (nr ++ maxSuffixForAxiomNames)
                       (LImpl pMin (LImpl (LVar (sortMaxName sr)) (LVar nr))))
          ]

    folInverseFactAxioms :: [LeanDecl]
    folInverseFactAxioms = map mkInvFact folSingleArgFunctions
      where
        mkInvFact f =
          let fInv    = invName f
              argSort = IR.sortName (head (IR.funcArgSorts f))
              resSort = IR.sortName (IR.funcResSort f)
              n1      = fInv ++ "_1"   -- lives in resSort
              nr      = fInv ++ "_res" -- lives in argSort
              -- forall X1 : Prop, (IsWithinBounds resSort X1) →
              -- forall X2 : Prop, (IsWithinBounds argSort X2) →
              --   (X1 = fInv_1 ∧ X2 = fInv_res) ↔ X2 = fInv(X1)
              lhsConj = LConj (LEq (LVar "X1") (LVar n1))
                              (LEq (LVar "X2") (LVar nr))
              rhsEq   = LEq (LVar "X2") (LApp (LVar fInv) [LVar "X1"])
              body    = LBicond lhsConj rhsEq
              q2      = bForall "X2" (sortMinName argSort) (sortMaxName argSort) body
              q1      = bForall "X1" (sortMinName resSort) (sortMaxName resSort) q2
          in DeclAxiom (LeanAxiom (fInv ++ "_fact") q1)

    -- -----------------------------------------------------------------------
    -- Product sorts for multi-argument FOL functions
    -- -----------------------------------------------------------------------
    -- Multi-arg FOL functions (arity > 1) get a product sort f#dom with its
    -- own Min/Max, ordering axioms, projection functions f_pi_k, tuple
    -- formation function f_tuple, direct/inverse image functions, and a
    -- decomposition axiom connecting f with f_tuple and f_dir_img.
    multiArgFolFunctions :: [IR.Function]
    multiArgFolFunctions =
      filter (\f -> length (IR.funcArgSorts f) > 1
                 && IR.funcOrigin f == IR.FromSignature)
             folFunctions

    -- Sanitized names derived from a function's product sort
    domMinName, domMaxName :: IR.Function -> String
    domMinName f = sanitizeName (IR.sortName dom) ++ minSuffix
      where dom = maybe (error "no domain sort") id (IR.funcDomain f)
    domMaxName f = sanitizeName (IR.sortName dom) ++ maxSuffix
      where dom = maybe (error "no domain sort") id (IR.funcDomain f)

    -- Helper: projection function name for the k-th argument (1-based)
    piName :: IR.Function -> Int -> String
    piName f k = IR.funcName f ++ "_pi_" ++ show k

    -- Helper: tuple formation function name
    tupleName :: IR.Function -> String
    tupleName f = IR.funcName f ++ "_tuple"

    -- Helper: direct/inverse image function names
    dirImgName, invImgName :: IR.Function -> String
    dirImgName f = IR.funcName f ++ "_dir_img"
    invImgName f = IR.funcName f ++ "_inv_img"

    -- (1) Min/Max limit objects for the product sort
    productSortLimitDecls :: [LeanDecl]
    productSortLimitDecls = concatMap mkLimits multiArgFolFunctions
      where
        mkLimits f =
          [ DeclAxiom (LeanAxiom (domMinName f) LProp)
          , DeclAxiom (LeanAxiom (domMaxName f) LProp)
          ]

    -- (2) Sort ordering: U_Max → dom_Max, dom_Max → dom_Min, dom_Min → P_Max
    productSortOrderAxioms :: [LeanDecl]
    productSortOrderAxioms = concatMap mkOrder multiArgFolFunctions
      where
        mkOrder f =
          let fN  = IR.funcName f
              dMx = domMaxName f
              dMn = domMinName f
          in [ DeclAxiom (LeanAxiom (fN ++ "_dom_upper")
                         (LImpl uMax (LVar dMx)))
             , DeclAxiom (LeanAxiom (fN ++ "_dom_ordering")
                         (LImpl (LVar dMx) (LVar dMn)))
             , DeclAxiom (LeanAxiom (fN ++ "_dom_lower")
                         (LImpl (LVar dMn) pMax))
             ]

    -- (3) Projection functions f_pi_1, f_pi_2, ... : Prop → Prop
    projectionFunctionDecls :: [LeanDecl]
    projectionFunctionDecls = concatMap mkProjDecls multiArgFolFunctions
      where
        mkProjDecls f =
          [ DeclAxiom (LeanAxiom (piName f k) (LImpl LProp LProp))
          | k <- [1 .. length (IR.funcArgSorts f)]
          ]

    -- (4) Tuple formation function f_tuple : Prop → Prop → ... → Prop
    --     (same arity as f)
    tupleFunctionDecls :: [LeanDecl]
    tupleFunctionDecls = map mkTupleDecl multiArgFolFunctions
      where
        mkTupleDecl f =
          let arity = length (IR.funcArgSorts f)
              ty    = foldr (\_ acc -> LImpl LProp acc) LProp [1..arity]
          in DeclAxiom (LeanAxiom (tupleName f) ty)

    -- (5) Direct image function f_dir_img : Prop → Prop  (f#dom → resSort)
    --     Inverse image function f_inv_img : Prop → Prop (resSort → f#dom)
    imageFunctionDecls :: [LeanDecl]
    imageFunctionDecls = concatMap mkImgDecls multiArgFolFunctions
      where
        mkImgDecls f =
          [ DeclAxiom (LeanAxiom (dirImgName f) (LImpl LProp LProp))
          , DeclAxiom (LeanAxiom (invImgName f) (LImpl LProp LProp))
          ]

    -- (6) f_arg : canonical element of f#dom (read from IR's funcArgument)
    --     Bounds: P_Min → f_arg → dom_Min  and  P_Min → dom_Max → f_arg
    productArgDecls :: [LeanDecl]
    productArgDecls = concatMap mkArgDecl multiArgFolFunctions
      where
        mkArgDecl f =
          case IR.funcArgument f of
            Nothing  -> []
            Just arg ->
              let n   = sanitizeName (IR.mereoName arg)
                  dMn = domMinName f
                  dMx = domMaxName f
              in [ DeclAxiom (LeanAxiom n LProp)
                 , DeclAxiom (LeanAxiom (n ++ minSuffixForAxiomNames)
                               (LImpl pMin (LImpl (LVar n) (LVar dMn))))
                 , DeclAxiom (LeanAxiom (n ++ maxSuffixForAxiomNames)
                               (LImpl pMin (LImpl (LVar dMx) (LVar n))))
                 ]

    -- (7) f_dir_img_fact: canonical-element fact for the direct image function
    --     forall A : Prop, (IsWithinBounds dom_Min dom_Max A) →
    --     forall B : Prop, (IsWithinBounds res_Min res_Max B) →
    --       (A = f_arg ∧ B = f_res) ↔ B = f_dir_img(A)
    dirImgFactAxioms :: [LeanDecl]
    dirImgFactAxioms = concatMap mkDirImgFact multiArgFolFunctions
      where
        mkDirImgFact f =
          case IR.funcArgument f of
            Nothing  -> []
            Just arg ->
              let dMn    = domMinName f
                  dMx    = domMaxName f
                  rSN    = IR.sortName (IR.funcResSort f)
                  argN   = sanitizeName (IR.mereoName arg)
                  resN   = sanitizeName (IR.mereoName (IR.funcResObject f))
                  lhs    = LConj (LEq (LVar "A") (LVar argN))
                                 (LEq (LVar "B") (LVar resN))
                  rhs    = LEq (LVar "B") (LApp (LVar (dirImgName f)) [LVar "A"])
                  body   = LBicond lhs rhs
                  qB     = bForall "B" (sortMinName rSN) (sortMaxName rSN) body
                  qA     = bForall "A" dMn dMx qB
              in [DeclAxiom (LeanAxiom (dirImgName f ++ "_fact") qA)]

    -- (8) f_inv_img_fact: similar fact for the inverse image function
    --     We use fresh names f_inv_img_arg, f_inv_img_res for its witnesses.
    --     forall A : Prop, (IsWithinBounds res_Min res_Max A) →
    --     forall B : Prop, (IsWithinBounds dom_Min dom_Max B) →
    --       (A = f_inv_img_arg ∧ B = f_inv_img_res) ↔ B = f_inv_img(A)
    invImgWitnessDecls :: [LeanDecl]
    invImgWitnessDecls = concatMap mkWitnesses multiArgFolFunctions
      where
        mkWitnesses f =
          let fN    = invImgName f
              argN  = fN ++ "_arg"
              resN  = fN ++ "_res"
              rSN   = IR.sortName (IR.funcResSort f)
              dMn   = domMinName f
              dMx   = domMaxName f
          in [ DeclAxiom (LeanAxiom argN LProp)
             , DeclAxiom (LeanAxiom (argN ++ minSuffixForAxiomNames)
                           (LImpl pMin (LImpl (LVar argN) (LVar (sortMinName rSN)))))
             , DeclAxiom (LeanAxiom (argN ++ maxSuffixForAxiomNames)
                           (LImpl pMin (LImpl (LVar (sortMaxName rSN)) (LVar argN))))
             , DeclAxiom (LeanAxiom resN LProp)
             , DeclAxiom (LeanAxiom (resN ++ minSuffixForAxiomNames)
                           (LImpl pMin (LImpl (LVar resN) (LVar dMn))))
             , DeclAxiom (LeanAxiom (resN ++ maxSuffixForAxiomNames)
                           (LImpl pMin (LImpl (LVar dMx) (LVar resN))))
             ]

    invImgFactAxioms :: [LeanDecl]
    invImgFactAxioms = map mkInvImgFact multiArgFolFunctions
      where
        mkInvImgFact f =
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
          in DeclAxiom (LeanAxiom (fN ++ "_fact") qA)

    -- (9) Adjunction between f_dir_img and f_inv_img:
    --     forall X : Prop, (IsWithinBounds dom_Min dom_Max X) →
    --     forall Y : Prop, (IsWithinBounds res_Min res_Max Y) →
    --       f_dir_img(X) ⊆ Y ↔ X ⊆ f_inv_img(Y)
    --     where A ⊆ B  =  B → A
    imageAdjunctionAxioms :: [LeanDecl]
    imageAdjunctionAxioms = map mkAdj multiArgFolFunctions
      where
        mkAdj f =
          let dMn   = domMinName f
              dMx   = domMaxName f
              rSN   = IR.sortName (IR.funcResSort f)
              dirN  = dirImgName f
              invN  = invImgName f
              dirX  = LApp (LVar dirN) [LVar "X"]
              invY  = LApp (LVar invN) [LVar "Y"]
              lhs   = LImpl (LVar "Y") dirX   -- dir_img(X) ⊆ Y
              rhs   = LImpl invY (LVar "X")   -- X ⊆ inv_img(Y)
              body  = LBicond lhs rhs
              qY    = bForall "Y" (sortMinName rSN) (sortMaxName rSN) body
              qX    = bForall "X" dMn dMx qY
          in DeclAxiom (LeanAxiom (IR.funcName f ++ "_image_adjunction") qX)

    -- (10) Decomposition axiom:
    --      forall X1 : Prop, (IsWithinBounds s1_Min s1_Max X1) →
    --      forall X2 : Prop, (IsWithinBounds s2_Min s2_Max X2) →
    --        f(X1, X2) = f_dir_img(f_tuple(X1, X2))
    decompositionAxioms :: [LeanDecl]
    decompositionAxioms = map mkDecomp multiArgFolFunctions
      where
        mkDecomp f =
          let fN      = IR.funcName f
              argSNs  = map IR.sortName (IR.funcArgSorts f)
              arity   = length argSNs
              varNs   = [ "X" ++ show i | i <- [1..arity] ]
              tupleApp = LApp (LVar (tupleName f)) (map LVar varNs)
              dirApp   = LApp (LVar (dirImgName f)) [tupleApp]
              fApp     = LApp (LVar fN) (map LVar varNs)
              body     = LEq fApp dirApp
              quantified =
                foldr (\(varN, sN) acc ->
                          bForall varN (sortMinName sN) (sortMaxName sN) acc)
                      body
                      (zip varNs argSNs)
          in DeclAxiom (LeanAxiom (fN ++ "_decomposition") quantified)

    -- (11) f_tuple_fact: canonical-element fact for tuple formation.
    --      f_tuple maps (S1, S2, ...) → f_dom, with witnesses f_1, f_2, ..., f_arg.
    --      forall X1, (IsWithinBounds s1 X1) → ... → forall Xn, (IsWithinBounds sn Xn) →
    --      forall Xr, (IsWithinBounds dom Xr) →
    --        (X1 = f_1 ∧ ... ∧ Xn = f_n ∧ Xr = f_arg) ↔ Xr = f_tuple(X1, ..., Xn)
    tupleFact :: [LeanDecl]
    tupleFact = concatMap mkTupleFact multiArgFolFunctions
      where
        mkTupleFact f =
          case IR.funcArgument f of
            Nothing  -> []
            Just arg ->
              let argObjs  = IR.funcArgObjects f
                  argSorts = IR.funcArgSorts f
                  arity    = length argObjs
                  argVars  = [ "X" ++ show i | i <- [1..arity] ]
                  resVar   = "X" ++ show (arity + 1)
                  dMn      = domMinName f
                  dMx      = domMaxName f
                  argN     = sanitizeName (IR.mereoName arg)
                  argEqs   =
                    [ LEq (LVar xi) (LVar (sanitizeName (IR.mereoName obj)))
                    | (xi, obj) <- zip argVars argObjs
                    ]
                  resEq    = LEq (LVar resVar) (LVar argN)
                  lhsConj  = case argEqs of
                    []     -> resEq
                    (e:es) -> foldl LConj e (es ++ [resEq])
                  tupleApp = LApp (LVar (tupleName f)) (map LVar argVars)
                  rhsEq    = LEq (LVar resVar) tupleApp
                  body     = LBicond lhsConj rhsEq
                  mkArgQ (varN, sN) acc =
                    bForall varN (sortMinName sN) (sortMaxName sN) acc
                  resQ acc =
                    bForall resVar dMn dMx acc
                  quantified =
                    foldr mkArgQ (resQ body) (zip argVars (map IR.sortName argSorts))
              in [DeclAxiom (LeanAxiom (tupleName f ++ "_fact") quantified)]

    -- (12) Projection witness objects: f_pi_k_1 (input, lives in f_dom) and
    --      f_pi_k_res (output, lives in S_k).  Treated exactly like the arg/res
    --      witnesses of ordinary FOL functions (g_1, g_res, etc.).
    projectionWitnessDecls :: [LeanDecl]
    projectionWitnessDecls = concatMap mkProjWitnesses multiArgFolFunctions
      where
        mkProjWitnesses f =
          concatMap mkOne [1 .. length (IR.funcArgSorts f)]
          where
            mkOne k =
              [ DeclAxiom (LeanAxiom (piName f k ++ "_1") LProp)
              , DeclAxiom (LeanAxiom (piName f k ++ "_res") LProp)
              ]

    projectionWitnessBoundsAxioms :: [LeanDecl]
    projectionWitnessBoundsAxioms = concatMap mkProjWitnessBounds multiArgFolFunctions
      where
        mkProjWitnessBounds f =
          let dMn = domMinName f
              dMx = domMaxName f
          in concatMap (mkBoundsForK dMn dMx)
               (zip [1..] (IR.funcArgSorts f))
          where
            mkBoundsForK dMn dMx (k, srt) =
              let n1  = piName f k ++ "_1"    -- lives in f_dom
                  nr  = piName f k ++ "_res"  -- lives in S_k
                  sN  = IR.sortName srt
              in [ DeclAxiom (LeanAxiom (n1 ++ minSuffixForAxiomNames)
                               (LImpl pMin (LImpl (LVar n1) (LVar dMn))))
                 , DeclAxiom (LeanAxiom (n1 ++ maxSuffixForAxiomNames)
                               (LImpl pMin (LImpl (LVar dMx) (LVar n1))))
                 , DeclAxiom (LeanAxiom (nr ++ minSuffixForAxiomNames)
                               (LImpl pMin (LImpl (LVar nr) (LVar (sortMinName sN)))))
                 , DeclAxiom (LeanAxiom (nr ++ maxSuffixForAxiomNames)
                               (LImpl pMin (LImpl (LVar (sortMaxName sN)) (LVar nr))))
                 ]

    -- (12b) f_pi_k_fact: full ↔ biconditional, exactly like g_fact / h_fact.
    --      f_pi_k : f_dom → S_k, with witnesses f_pi_k_1 (input) and f_pi_k_res (output).
    --      forall X1, (IsWithinBounds dom X1) →
    --      forall X2, (IsWithinBounds s_k X2) →
    --        (X1 = f_pi_k_1 ∧ X2 = f_pi_k_res) ↔ X2 = f_pi_k(X1)
    projectionFacts :: [LeanDecl]
    projectionFacts = concatMap mkProjFacts multiArgFolFunctions
      where
        mkProjFacts f =
          let dMn = domMinName f
              dMx = domMaxName f
          in [ mkOneProjFact dMn dMx k srt
             | (k, srt) <- zip [1..] (IR.funcArgSorts f)
             ]
          where
            mkOneProjFact dMn dMx k srt =
              let n1   = piName f k ++ "_1"
                  nr   = piName f k ++ "_res"
                  sN   = IR.sortName srt
                  lhs  = LConj (LEq (LVar "X1") (LVar n1))
                               (LEq (LVar "X2") (LVar nr))
                  rhs  = LEq (LVar "X2") (LApp (LVar (piName f k)) [LVar "X1"])
                  body = LBicond lhs rhs
                  qX2  = bForall "X2" (sortMinName sN) (sortMaxName sN) body
                  qX1  = bForall "X1" dMn dMx qX2
              in DeclAxiom (LeanAxiom (piName f k ++ "_fact") qX1)

    -- Helper: inverse projection function name for the k-th argument (1-based)
    piInvName :: IR.Function -> Int -> String
    piInvName f k = IR.funcName f ++ "_pi_" ++ show k ++ "_inv"

    -- (13) Inverse projection function declarations: f_pi_k_inv : Prop → Prop
    --      These are the right adjoints to the projection functions f_pi_k.
    --      f_pi_k : f_dom → S_k,   f_pi_k_inv : S_k → f_dom
    projectionInverseFunctionDecls :: [LeanDecl]
    projectionInverseFunctionDecls = concatMap mkProjInvDecls multiArgFolFunctions
      where
        mkProjInvDecls f =
          [ DeclAxiom (LeanAxiom (piInvName f k) (LImpl LProp LProp))
          | k <- [1 .. length (IR.funcArgSorts f)]
          ]

    -- (14) Adjunction axioms: f_pi_k ⊣ f_pi_k_inv
    --      forall X : Prop, (IsWithinBounds dom_Min dom_Max X) →
    --      forall Y : Prop, (IsWithinBounds s_k_Min s_k_Max Y) →
    --        (f_pi_k(X) ⊆ Y) ↔ (X ⊆ f_pi_k_inv(Y))
    --      i.e. (Y → f_pi_k(X)) ↔ (f_pi_k_inv(Y) → X)
    projectionAdjunctionAxioms :: [LeanDecl]
    projectionAdjunctionAxioms = concatMap mkProjAdj multiArgFolFunctions
      where
        mkProjAdj f =
          [ mkOneAdj f k srt
          | (k, srt) <- zip [1..] (IR.funcArgSorts f)
          ]
          where
            mkOneAdj f k srt =
              let dMn   = domMinName f
                  dMx   = domMaxName f
                  sN    = IR.sortName srt
                  piN   = piName f k
                  piInvN = piInvName f k
                  piX   = LApp (LVar piN) [LVar "X"]
                  piInvY = LApp (LVar piInvN) [LVar "Y"]
                  lhs   = LImpl (LVar "Y") piX       -- f_pi_k(X) ⊆ Y
                  rhs   = LImpl piInvY (LVar "X")    -- X ⊆ f_pi_k_inv(Y)
                  body  = LBicond lhs rhs
                  qY    = bForall "Y" (sortMinName sN) (sortMaxName sN) body
                  qX    = bForall "X" dMn dMx qY
              in DeclAxiom (LeanAxiom (piN ++ "_adjunction") qX)

    -- (15) f_tuple_inv_decomposition: connects f_tuple to the inverse projections.
    --      forall X1 : Prop, (IsWithinBounds s1_Min s1_Max X1) →
    --      ...
    --      forall Xn : Prop, (IsWithinBounds sn_Min sn_Max Xn) →
    --        f_tuple(X1, ..., Xn) = f_pi_1_inv(X1) ∩ ... ∩ f_pi_n_inv(Xn)
    --      where ∩ is meet, encoded as ∧ in the Prop lattice.
    tupleInverseDecompositionFacts :: [LeanDecl]
    tupleInverseDecompositionFacts = map mkTupleInvDecomp multiArgFolFunctions
      where
        mkTupleInvDecomp f =
          let argSNs  = map IR.sortName (IR.funcArgSorts f)
              arity   = length argSNs
              varNs   = [ "X" ++ show i | i <- [1..arity] ]
              -- f_tuple(X1, ..., Xn)
              tupleApp = LApp (LVar (tupleName f)) (map LVar varNs)
              -- f_pi_k_inv(Xk) for each k
              invApps  = [ LApp (LVar (piInvName f k)) [LVar xk]
                         | (k, xk) <- zip [1..] varNs ]
              -- fold them together with ∧ (meet / intersection)
              meetExpr = foldl1 LConj invApps
              body     = LEq tupleApp meetExpr
              quantified =
                foldr (\(varN, sN) acc ->
                          bForall varN (sortMinName sN) (sortMaxName sN) acc)
                      body
                      (zip varNs argSNs)
          in DeclAxiom (LeanAxiom (tupleName f ++ "_inv_decomposition") quantified)

    -- (16) IR_f predicate: a Prop → Prop predicate saying that an element of
    --      f_dom is an "invertible rectangle."
    --      IR_f_tuple_with_projections:
    --        forall Z, (IsWithinBounds dom Z) →
    --          IR_f(Z) ↔ Z = f_tuple(f_pi_1(Z), f_pi_2(Z))
    --      IR_f_projections_from_tuple:
    --        forall X, (IsWithinBounds S_1 X) →
    --        forall Y, (IsWithinBounds S_2 Y) →
    --          IR_f(f_tuple(X,Y)) ↔ (f_pi_1(f_tuple(X,Y)) = X ∧ f_pi_2(f_tuple(X,Y)) = Y)
    --      IR_f_separates:
    --        forall X, (IsWithinBounds S_1 X) →
    --        forall Y, (IsWithinBounds S_1 Y) →
    --          X = Y ↔ forall Z, (IsWithinBounds dom Z) →
    --                    IR_f(Z) → ((X → Z) ↔ (Y → Z))
    irPredicateName :: IR.Function -> String
    irPredicateName f = "IR_" ++ IR.funcName f

    irPredicateDecls :: [LeanDecl]
    irPredicateDecls = map mkIRDecl multiArgFolFunctions
      where
        mkIRDecl f = DeclAxiom (LeanAxiom (irPredicateName f) (LImpl LProp LProp))

    irTupleWithProjectionsAxioms :: [LeanDecl]
    irTupleWithProjectionsAxioms = map mkIRTuple multiArgFolFunctions
      where
        mkIRTuple f =
          let dMn    = domMinName f
              dMx    = domMaxName f
              irN    = irPredicateName f
              tupN   = tupleName f
              -- build f_tuple(f_pi_1(Z), ..., f_pi_n(Z))
              arity  = length (IR.funcArgSorts f)
              piApps = [ LApp (LVar (piName f k)) [LVar "Z"] | k <- [1..arity] ]
              tupleApp = LApp (LVar tupN) piApps
              irZ    = LApp (LVar irN) [LVar "Z"]
              body   = LBicond irZ (LEq (LVar "Z") tupleApp)
              qZ     = bForall "Z" dMn dMx body
          in DeclAxiom (LeanAxiom (irN ++ "_tuple_with_projections") qZ)

    irProjectionsFromTupleAxioms :: [LeanDecl]
    irProjectionsFromTupleAxioms = map mkIRProj multiArgFolFunctions
      where
        mkIRProj f =
          let argSNs  = map IR.sortName (IR.funcArgSorts f)
              arity   = length argSNs
              varNs   = [ "X" ++ show i | i <- [1..arity] ]
              irN     = irPredicateName f
              tupN    = tupleName f
              tupleApp = LApp (LVar tupN) (map LVar varNs)
              irTuple  = LApp (LVar irN) [tupleApp]
              -- f_pi_k(f_tuple(X1,...,Xn)) = Xk  for each k
              projEqs  = [ LEq (LApp (LVar (piName f k)) [tupleApp]) (LVar xk)
                         | (k, xk) <- zip [1..] varNs ]
              rhsConj  = foldl1 LConj projEqs
              body     = LBicond irTuple rhsConj
              quantified =
                foldr (\(varN, sN) acc ->
                          bForall varN (sortMinName sN) (sortMaxName sN) acc)
                      body
                      (zip varNs argSNs)
          in DeclAxiom (LeanAxiom (irPredicateName f ++ "_projections_from_tuple") quantified)

    irSeparationAxioms :: [LeanDecl]
    irSeparationAxioms = map mkIRSep multiArgFolFunctions
      where
        mkIRSep f =
          -- We separate over the first argument sort (S_1).
          -- X = Y ↔ ∀ Z : Prop, (IsWithinBounds dom Z) →
          --           IR_f(Z) → ((X → Z) ↔ (Y → Z))
          let dMn   = domMinName f
              dMx   = domMaxName f
              irN   = irPredicateName f
              irZ   = LApp (LVar irN) [LVar "Z"]
              body  = LBicond (LImpl (LVar "X") (LVar "Z"))
                              (LImpl (LVar "Y") (LVar "Z"))
              inner = LImpl irZ body
              qZ    = bForall "Z" dMn dMx inner
              sep   = LBicond (LEq (LVar "X") (LVar "Y")) qZ
              qY    = bForall "Y" dMn dMx sep
              qX    = bForall "X" dMn dMx qY
          in DeclAxiom (LeanAxiom (irPredicateName f ++ "_separates") qX)
    -- separately via folInverseArgResDecls / folInverseArgResBoundsAxioms.
    userDeclaredFolFunctions :: [IR.Function]
    userDeclaredFolFunctions =
      filter (\f -> IR.funcOrigin f == IR.FromSignature) folFunctions

    functionObjects :: [IR.MereologicalObject]
    functionObjects =
      concatMap (\f -> IR.funcArgObjects f ++ [IR.funcResObject f]) solFunctions ++
      concatMap (\f -> IR.funcArgObjects f ++ [IR.funcResObject f]) userDeclaredFolFunctions

    -- Sanitize names for Lean (replace # with _)
    functionArgResultDecls :: [LeanDecl]
    functionArgResultDecls = 
      map (\m -> DeclAxiom (LeanAxiom (sanitizeName (IR.mereoName m)) LProp)) functionObjects

    functionArgResultBoundsAxioms :: [LeanDecl]
    functionArgResultBoundsAxioms = concatMap functionArgResultBoundsFor functionObjects
      where
        functionArgResultBoundsFor m =
          let n = IR.mereoName m
              nSanitized = sanitizeName n
              -- Get the sort of this function object
              sortName = IR.sortName (IR.mereoSort m)
          in [ DeclAxiom (LeanAxiom (nSanitized ++ minSuffixForAxiomNames) 
                         (LImpl pMin (LImpl (LVar nSanitized) (LVar (sortMinName sortName)))))
             , DeclAxiom (LeanAxiom (nSanitized ++ maxSuffixForAxiomNames) 
                         (LImpl pMin (LImpl (LVar (sortMaxName sortName)) (LVar nSanitized))))
             ]

    -- -----------------------------------------------------------------------
    -- Function fact axioms: connect function with its argument/result objects
    -- -----------------------------------------------------------------------
    -- -----------------------------------------------------------------------
    -- Function fact axioms: connect function with its argument/result objects
    -- -----------------------------------------------------------------------
    functionFactAxioms :: [LeanDecl]
    functionFactAxioms = concatMap mkFunctionFact (solFunctions ++ userDeclaredFolFunctions)
      where
        mkBoundedForall :: String -> String -> LeanExpr -> LeanExpr
        mkBoundedForall varN sortN = bForall varN (sortMinName sortN) (sortMaxName sortN)

        mkFunctionFact f =
          let fName    = IR.funcName f
              argObjs  = IR.funcArgObjects f
              resObj   = IR.funcResObject f
              argCount = length argObjs

              -- arg vars X1..Xn, result var X(n+1)
              argVarNames = [ "X" ++ show i | i <- [1..argCount] ]
              resVarName  = "X" ++ show (argCount + 1)

              -- (X1 = F_1 ∧ X2 = F_2 ∧ ... ∧ Xres = F_res)
              argEqs =
                [ LEq (LVar varN) (LVar (sanitizeName (IR.mereoName obj)))
                | (varN, obj) <- zip argVarNames argObjs
                ]
              resEq = LEq (LVar resVarName)
                          (LVar (sanitizeName (IR.mereoName resObj)))
              -- left side: X1=F_1 ∧ X2=F_2 ∧ ... ∧ Xres=F_res
              -- build left-fold: ((X1=F_1 ∧ X2=F_2) ∧ X3=F_res)
              lhsConj = case argEqs of
                []     -> resEq
                (e:es) -> foldl LConj e (es ++ [resEq])

              -- right side: Xres = (F X1 X2 ...)
              funcApp = LApp (LVar fName) (map LVar argVarNames)
              rhsEq   = LEq (LVar resVarName) funcApp

              -- body: lhsConj ↔ rhsEq
              body = LBicond lhsConj rhsEq

              -- wrap in forall quantifiers: args first, then result
              sortOf obj = IR.sortName (IR.mereoSort obj)

              -- build the chain of foralls from inside out (foldr)
              -- order: X1, X2, ..., Xn, X(n+1)
              allVarsAndSorts =
                   zip argVarNames (map sortOf argObjs)
                ++ [(resVarName, sortOf resObj)]

              quantifiedBody =
                foldr (\(varN, sN) acc -> mkBoundedForall varN sN acc)
                      body
                      allVarsAndSorts

              axName = fName ++ "_fact"

          in [DeclAxiom (LeanAxiom axName quantifiedBody)]
            
    -- -----------------------------------------------------------------------
    -- 𝕌-kinded (mereological) objects
    -- -----------------------------------------------------------------------
    mereoObjects :: [IR.MereologicalObject]
    mereoObjects =
      [ m
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindMereological
      , IR.mereoOrigin m == IR.FromSignature
      , IR.mereoName   m `notElem` [uMinName, uMaxName, "⊤", "⊥"]
      ]

    mereoDecls :: [LeanDecl]
    mereoDecls = map (\m -> DeclAxiom (LeanAxiom (IR.mereoName m) LProp)) mereoObjects

    mereoBoundsAxioms :: [LeanDecl]
    mereoBoundsAxioms = concatMap mereoBoundsFor mereoObjects
      where
        mereoBoundsFor m =
          let n = IR.mereoName m
          in [ DeclAxiom (LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) uMin))
             , DeclAxiom (LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl uMax (LVar n)))
             ]

    -- -----------------------------------------------------------------------
    -- ℙ-kinded (propositional) objects
    -- -----------------------------------------------------------------------
    propObjects :: [IR.MereologicalObject]
    propObjects =
      [ m
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindProposition
      , IR.mereoOrigin m == IR.FromSignature
      , IR.mereoName   m `notElem` [pMinName, pMaxName, "⊤", "⊥", "ℙ#min", "ℙ#max"]
      ]

    propDecls :: [LeanDecl]
    propDecls = map (\m -> DeclAxiom (LeanAxiom (IR.mereoName m) LProp)) propObjects

    propBoundsAxioms :: [LeanDecl]
    propBoundsAxioms = concatMap propBoundsFor propObjects
      where
        propBoundsFor m =
          let n = IR.mereoName m
          in [ DeclAxiom (LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) pMin))
             , DeclAxiom (LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl pMax (LVar n)))
             ]

    -- -----------------------------------------------------------------------
    -- 𝔻-kinded sets (only if theory uses domain)
    -- -----------------------------------------------------------------------
    setObjects :: [IR.MereologicalObject]
    setObjects =
      if usesDomain
      then [ m
           | IR.EntityMereological m <- IR.theoryObjects theory
           , IR.mereoKind   m == IR.MereologicalEntityKindSet
           , IR.mereoOrigin m == IR.FromSignature
           , IR.sortKind  (IR.mereoSort m) == IR.SortKindDomain
           , IR.sortName  (IR.mereoSort m) == "𝔻"
           ]
      else []

    setDecls :: [LeanDecl]
    setDecls = map (\m -> DeclAxiom (LeanAxiom (IR.mereoName m) LProp)) setObjects

    setBoundsAxioms :: [LeanDecl]
    setBoundsAxioms = concatMap setBoundsFor setObjects
      where
        setBoundsFor m =
          let n = IR.mereoName m
          in [ DeclAxiom (LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) dMin))
             , DeclAxiom (LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl dMax (LVar n)))
             ]

    -- -----------------------------------------------------------------------
    -- Sets declared against user-defined sorts
    -- -----------------------------------------------------------------------
    userSortSets :: [IR.MereologicalObject]
    userSortSets =
      [ m
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindSet
      , IR.mereoOrigin m == IR.FromSignature
      , IR.sortKind  (IR.mereoSort m) == IR.SortKindFromSignature
      ]

    userSortSetBoundsAxioms :: [LeanDecl]
    userSortSetBoundsAxioms = concatMap setBounds userSortSets
      where
        setBounds m =
          let n    = IR.mereoName m
              sMin = sortMinName (IR.sortName (IR.mereoSort m))
              sMax = sortMaxName (IR.sortName (IR.mereoSort m))
          in [ DeclAxiom (LeanAxiom (n ++ minSuffixForAxiomNames) (LImpl (LVar n) (LVar sMin)))
             , DeclAxiom (LeanAxiom (n ++ maxSuffixForAxiomNames) (LImpl (LVar sMax) (LVar n)))
             ]

    -- -----------------------------------------------------------------------
    -- Sort-ordering axioms (conditionally include D-related axioms)
    -- -----------------------------------------------------------------------
    sortOrderDecls :: [LeanDecl]
    sortOrderDecls =
      [  
        DeclAxiom (LeanAxiom "U_ordering" (LImpl uMax uMin))
      , DeclAxiom (LeanAxiom "U_to_P" (LImpl uMax pMax))
      , DeclAxiom (LeanAxiom "P_ordering" (LImpl pMax pMin))
      , DeclAxiom (LeanAxiom "P_to_U" (LImpl pMin uMin))
      ] ++ (if usesDomain
            then [ DeclAxiom (LeanAxiom "D_upper" (LImpl uMax dMax))
                 , DeclAxiom (LeanAxiom "D_ordering" (LImpl dMax dMin))
                 , DeclAxiom (LeanAxiom "D_lower" (LImpl dMin pMax))
                 ]
            else [])
      ++ concatMap userSortOrderAxioms userSorts
      ++ [DeclBlankLine]
      where
        userSortOrderAxioms s =
          let sortName = IR.sortName s
              sMax = sortMaxName sortName
              sMin = sortMinName sortName
          in [ DeclAxiom (LeanAxiom (sortName ++ "_upper") (LImpl uMax (LVar sMax)))
             , DeclAxiom (LeanAxiom (sortName ++ "_ordering") (LImpl (LVar sMax) (LVar sMin)))
             , DeclAxiom (LeanAxiom (sortName ++ "_lower") (LImpl (LVar sMin) pMax))
             ]
            
    -- -----------------------------------------------------------------------
    -- User facts
    -- -----------------------------------------------------------------------
    userAssertions :: [IR.Fact]
    userAssertions =
      [ f
      | f <- IR.theoryFacts theory
      , IR.factKind f == IR.FactKindAssertion
      , not (IR.factIsInherited f)
      , not (IR.factIsMereologicalTranslation f)
      ]

    userMetafacts :: [IR.Fact]
    userMetafacts =
      [ f
      | f <- IR.theoryFacts theory
      , IR.factKind f == IR.FactKindMetafactsFact
      , not (IR.factIsInherited f)
      , not (IR.factIsMereologicalTranslation f)
      ]

    totalFacts :: Int
    totalFacts = length userAssertions + length userMetafacts

    mkLabel :: Int -> String
    mkLabel idx = if totalFacts > 1 then "ax" ++ show idx else ""

    -- Wrap fact body in (P_Min ∧ body) ↔ P_Min  or  (U_Min ∧ body) ↔ U_Min
    mkFactAxiom :: String -> LeanExpr -> LeanExpr -> LeanDecl
    mkFactAxiom label wrapper body =
      DeclAxiom (LeanAxiom label (LBicond (LConj wrapper body) wrapper))

    factBody :: IR.Fact -> LeanExpr
    factBody fact = wrapFreeVars (IR.factFreeVars fact) (propExprToLean (IR.factPropExpr fact))

    assertionDecl :: Int -> IR.Fact -> LeanDecl
    assertionDecl idx fact = mkFactAxiom (mkLabel idx) pMin (factBody fact)

    metafactDecl :: Int -> IR.Fact -> LeanDecl
    metafactDecl idx fact = mkFactAxiom (mkLabel idx) uMin (factBody fact)

    userFactDecls :: [LeanDecl]
    userFactDecls =
         zipWith assertionDecl [1 ..] userAssertions
      ++ zipWith metafactDecl  [1 + length userAssertions ..] userMetafacts

-- ---------------------------------------------------------------------------
-- Free-variable wrapping
-- ---------------------------------------------------------------------------

wrapFreeVars :: [IR.ResolvedVarDecl] -> LeanExpr -> LeanExpr
wrapFreeVars [] body = body
wrapFreeVars (vd : rest) body =
  varDeclToForall vd (wrapFreeVars rest body)

varDeclToForall :: IR.ResolvedVarDecl -> LeanExpr -> LeanExpr
varDeclToForall vd body =
  let varN = IR.resolvedVarName vd
      sn   = IR.sortName (IR.resolvedVarSort vd)
      (lo, hi) = sortBounds sn
  in LBoundedForall varN lo hi body

-- | Resolve a sort name to its (lo, hi) bound names.
sortBounds :: String -> (String, String)
sortBounds sortN = case sortN of
  "ℙ" -> (pMinName, pMaxName)
  "𝕌" -> (uMinName, uMaxName)
  "𝔻" -> (dMinName, dMaxName)
  _   ->
    let n = sanitizeName sortN
    in (n ++ minSuffix, n ++ maxSuffix)

-- ---------------------------------------------------------------------------
-- Converting IR prop-expressions to LeanExpr
-- ---------------------------------------------------------------------------

propExprToLean :: IR.ResolvedPropExpr -> LeanExpr
propExprToLean (IR.ResolvedPropBicond lhs rests) =
  case rests of
    []    -> rightImplToLean lhs
    (r:_) -> LBicond (rightImplToLean lhs)
                     (rightImplToLean (IR.resolvedPropRestRight r))

rightImplToLean :: IR.ResolvedRightImpl -> LeanExpr
rightImplToLean (IR.ResolvedRightImpl lhs Nothing) =
  leftImplToLean lhs
rightImplToLean (IR.ResolvedRightImpl lhs (Just (_, rhs))) =
  LImpl (leftImplToLean lhs) (rightImplToLean rhs)

leftImplToLean :: IR.ResolvedLeftImpl -> LeanExpr
leftImplToLean (IR.ResolvedLeftImpl lhs []) =
  disjToLean lhs
leftImplToLean (IR.ResolvedLeftImpl lhs rests) =
  foldr (\r acc -> LImpl (disjToLean (IR.resolvedLirRight r)) acc)
        (disjToLean lhs)
        rests

disjToLean :: IR.ResolvedDisj -> LeanExpr
disjToLean (IR.ResolvedDisj lhs []) = conjToLean lhs
disjToLean (IR.ResolvedDisj lhs rests) =
  foldl (\acc r -> LDisj acc (conjToLean (IR.resolvedDisjRestRight r)))
        (conjToLean lhs)
        rests

conjToLean :: IR.ResolvedConj -> LeanExpr
conjToLean (IR.ResolvedConj lhs []) = negToLean lhs
conjToLean (IR.ResolvedConj lhs rests) =
  foldl (\acc r -> LConj acc (negToLean (IR.resolvedConjRestRight r)))
        (negToLean lhs)
        rests

negToLean :: IR.ResolvedNeg -> LeanExpr
negToLean (IR.ResolvedNegNot inner) =
  LImpl (negToLean inner) pMax
negToLean (IR.ResolvedNegChild q) =
  quantifiedToLean q

quantifiedToLean :: IR.ResolvedQuantified -> LeanExpr
quantifiedToLean (IR.ResolvedQuantified [] atom) =
  atomicPropToLean atom
quantifiedToLean (IR.ResolvedQuantified qs atom) =
  foldr quantifierToLean (atomicPropToLean atom) qs

quantifierToLean :: IR.ResolvedQuantifier -> LeanExpr -> LeanExpr
quantifierToLean (IR.ResolvedQForall vd) body =
  let varN    = IR.resolvedVarName vd
      sn      = IR.sortName (IR.resolvedVarSort vd)
      (lo, hi) = sortBounds sn
  in LBoundedForall varN lo hi body
quantifierToLean (IR.ResolvedQExists vd) body =
  let varN = IR.resolvedVarName vd
      sn   = IR.sortName (IR.resolvedVarSort vd)
  in LExists varN (LVar "Prop") (LImpl (LIsWithinBounds (fst (sortBounds sn)) varN (snd (sortBounds sn))) body)

atomicPropToLean :: IR.ResolvedAtomicProp -> LeanExpr
atomicPropToLean (IR.ResolvedAtomicConstant ref) = 
  LVar (resolveConstRef ref)
atomicPropToLean (IR.ResolvedAtomicTermPair tp)  = termPairToLean tp

-- ---------------------------------------------------------------------------
-- Constant-reference resolution
-- ---------------------------------------------------------------------------

-- | Map a raw constant name to its Lean 4 identifier.
-- Built-in sorts get explicit mappings; user-sort names of the form
-- @S#min@ / @S#max@ are converted to @S_Min@ / @S_Max@.
resolveName :: String -> String
resolveName n = case n of
  "ℙ#min" -> pMinName
  "ℙ#max" -> pMaxName
  "𝕌#min" -> uMinName
  "𝕌#max" -> uMaxName
  "𝔻#min" -> dMinName
  "𝔻#max" -> dMaxName
  "⊤"     -> pMinName
  "⊥"     -> pMaxName
  other
    | Just base <- stripSuffix "#min" other -> sanitizeName base ++ minSuffix
    | Just base <- stripSuffix "#max" other -> sanitizeName base ++ maxSuffix
    | otherwise                             -> sanitizeName other
  where
    stripSuffix :: String -> String -> Maybe String
    stripSuffix suffix str =
      let (front, back) = splitAt (length str - length suffix) str
      in if back == suffix then Just front else Nothing

resolveConstRef :: IR.ResolvedConstantRef -> String
resolveConstRef = resolveName . IR.resolvedConstRefName

-- ---------------------------------------------------------------------------
-- Term-pair → LeanExpr  (relation-level operations, left-fold)
-- ---------------------------------------------------------------------------

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
       "-"  -> LImpl   right leftExpr   -- A - B  =>  B -> A
       "∸"  -> LBicond leftExpr right
       "="  -> LBicond leftExpr right
       "≤"  -> LImpl   leftExpr right
       "∪"  -> LConj   leftExpr right   -- set union  => conjunction
       "∩"  -> LDisj   leftExpr right   -- set intersection => disjunction
       "⊆"  -> LImpl   right leftExpr   -- A ⊆ B  =>  B -> A
       _    -> LVar ("(" ++ op ++ ")")  -- fallback

-- ---------------------------------------------------------------------------
-- Term / factor -> LeanExpr  (arithmetic inside a term, left-fold)
-- ---------------------------------------------------------------------------

termToLean :: IR.ResolvedTerm -> LeanExpr
termToLean (IR.ResolvedTerm lhs [] _) = factorToLean lhs
termToLean (IR.ResolvedTerm lhs rests _) =
  foldl applyArithOp (factorToLean lhs) rests

applyArithOp :: LeanExpr -> IR.ResolvedOperationFollowedByFactor -> LeanExpr
applyArithOp leftExpr off =
  let op    = IR.resolvedOFFOp off
      right = factorToLean (IR.resolvedOFFRight off)
  in case op of
       "+"  -> LConj   leftExpr right
       "×"  -> LDisj   leftExpr right
       "-"  -> LImpl   right leftExpr   -- A - B  =>  B -> A
       "∸"  -> LBicond leftExpr right
       "∪"  -> LConj   leftExpr right   -- set union  => conjunction
       "∩"  -> LDisj   leftExpr right   -- set intersection => disjunction
       _    -> LVar ("(" ++ op ++ ")")  -- fallback

factorToLean :: IR.ResolvedFactor -> LeanExpr
factorToLean (IR.ResolvedFactor base [] _) = baseTermToLean base
factorToLean (IR.ResolvedFactor base suffixes _) =
  let baseExpr = baseTermToLean base
  in foldl applySuffix baseExpr suffixes
  where
    applySuffix :: LeanExpr -> IR.ResolvedTermSuffix -> LeanExpr
    applySuffix expr (IR.ResolvedSuffixDotAttr attr) =
      LVar (sanitizeName (renderLeanExpr expr ++ "_" ++ attr))
    applySuffix expr (IR.ResolvedSuffixCall args) =
      let argExprs = map termToLean args
      in LApp expr argExprs
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

-- ---------------------------------------------------------------------------
-- Convenience entry point
-- ---------------------------------------------------------------------------

-- | Convert an Eidos theory directly to Lean 4 source (combines both stages).
exportToLeanPropsWithOptions :: LeanPropsOptions -> IR.Theory -> String
exportToLeanPropsWithOptions opts theory =
  let axiomSets0 = mkAxiomSets theory
      axiomSets1 = if optUseSortingAxioms opts
                   then map collapseSortingSet axiomSets0
                   else axiomSets0
      axiomSets2 = if optGroupByEntity opts then sortOn asPath axiomSets1 else axiomSets1
      doc = LeanDoc
        { leanDocTheoryName = IR.theoryFullyQualifiedName theory
        , leanDocDecls = renderAxiomSetsToDecls opts axiomSets2
        }
      header =
        if optUseBoundedForallSyntax opts
        then unlines
          [ "macro \"bforall \" x:ident \" in \" lo:term \"..\" hi:term \", \" body:term : term =>"
          , "  `(forall $x : Prop, (IsWithinBounds $lo $hi $x) → $body)"
          , ""
          ]
        else ""
  in header ++ renderLeanDoc doc

exportToLeanProps :: IR.Theory -> String
exportToLeanProps = exportToLeanPropsWithOptions defaultLeanPropsOptions

renderAxiomSetsToDecls :: LeanPropsOptions -> [AxiomSet] -> [LeanDecl]
renderAxiomSetsToDecls opts = concatMap renderOne
  where
    renderOne as_ =
      let commentDecls = if optAddGroupComments opts
                         then [DeclComment (subjectPathComment (asPath as_))]
                         else []
          axDecls = map (DeclAxiom . mapAxiom) (asAxioms as_)
      in DeclBlankLine : commentDecls ++ axDecls

    mapAxiom ax = ax { axiomType = rewriteBounded (axiomType ax) }

    rewriteBounded (LBoundedForall var lo hi body)
      | optUseBoundedForallSyntax opts =
          LApp (LVar "bforall")
            [ LVar var, LVar lo, LVar hi, rewriteBounded body ]
      | otherwise = LBoundedForall var lo hi (rewriteBounded body)
    rewriteBounded (LImpl a b) = LImpl (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LConj a b) = LConj (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LDisj a b) = LDisj (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LBicond a b) = LBicond (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LForall x ty b) = LForall x (rewriteBounded ty) (rewriteBounded b)
    rewriteBounded (LForallKw x ty b) = LForallKw x (rewriteBounded ty) (rewriteBounded b)
    rewriteBounded (LExists x ty b) = LExists x (rewriteBounded ty) (rewriteBounded b)
    rewriteBounded (LEq a b) = LEq (rewriteBounded a) (rewriteBounded b)
    rewriteBounded (LApp f args) = LApp (rewriteBounded f) (map rewriteBounded args)
    rewriteBounded (LProjectIntoInterval x lo hi) =
      LProjectIntoInterval (rewriteBounded x) (rewriteBounded lo) (rewriteBounded hi)
    rewriteBounded x = x

subjectPathComment :: SubjectPath -> String
subjectPathComment = unwords . map show

collapseSortingSet :: AxiomSet -> AxiomSet
collapseSortingSet as_
  | not (hasTag TagSorting as_) = as_
  | otherwise =
      case asAxioms as_ of
        [LeanAxiom nMin (LImpl _ (LImpl (LVar obj1) (LVar lo))),
         LeanAxiom nMax (LImpl _ (LImpl (LVar hi) (LVar obj2)))]
          | obj1 == obj2
          , stripSuffix "_min" nMin == Just obj1
          , stripSuffix "_max" nMax == Just obj1
          -> as_ { asAxioms = [LeanAxiom (obj1 ++ "_sorting") (LIsWithinBounds lo obj1 hi)] }
        [LeanAxiom nMin (LImpl (LVar obj1) (LVar lo)),
         LeanAxiom nMax (LImpl (LVar hi) (LVar obj2))]
          | obj1 == obj2
          , stripSuffix "_min" nMin == Just obj1
          , stripSuffix "_max" nMax == Just obj1
          -> as_ { asAxioms = [LeanAxiom (obj1 ++ "_sorting") (LIsWithinBounds lo obj1 hi)] }
        _ -> as_
  where
    stripSuffix suffix str =
      let n = length str - length suffix
      in if n >= 0 && drop n str == suffix then Just (take n str) else Nothing
data LeanPropsOptions = LeanPropsOptions
  { optGroupByEntity      :: Bool
  , optUseSortingAxioms   :: Bool
  , optAddGroupComments   :: Bool
  , optUseBoundedForallSyntax :: Bool
  } deriving (Eq, Show)

defaultLeanPropsOptions :: LeanPropsOptions
defaultLeanPropsOptions = LeanPropsOptions
  { optGroupByEntity = False
  , optUseSortingAxioms = False
  , optAddGroupComments = False
  , optUseBoundedForallSyntax = False
  }
