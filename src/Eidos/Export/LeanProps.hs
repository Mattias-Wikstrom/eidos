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
  ( -- * Internal representation
    LeanDoc (..)
  , LeanDecl (..)
  , LeanAxiom (..)
  , LeanExpr (..)
    -- * Pipeline stages
  , theoryToLeanDoc
  , renderLeanDoc
  , renderLeanExpr
    -- * Convenience entry point
  , exportToLeanProps
  ) where

import qualified Eidos.IR as IR

-- ---------------------------------------------------------------------------
-- Internal representation
-- ---------------------------------------------------------------------------

-- | A complete Lean 4 document ready to be printed.
data LeanDoc = LeanDoc
  { leanDocTheoryName :: String
  , leanDocDecls      :: [LeanDecl]
  } deriving (Eq, Show)

-- | A single top-level item in a Lean 4 file.
data LeanDecl
  = DeclComment  String       -- ^ @-- comment@
  | DeclBlankLine              -- ^ empty line
  | DeclAxiom    LeanAxiom    -- ^ @axiom name : body@
  deriving (Eq, Show)

-- | An @axiom@ statement with a name and a type expression.
data LeanAxiom = LeanAxiom
  { axiomName :: String
  , axiomType :: LeanExpr
  } deriving (Eq, Show)

-- | A Lean 4 proposition (the expression language we need).
data LeanExpr
  = LProp                              -- ^ @Prop@
  | LVar   String                      -- ^ atomic name
  | LApp   LeanExpr [LeanExpr]         -- ^ function application
  | LImpl  LeanExpr LeanExpr           -- ^ @A → B@
  | LConj  LeanExpr LeanExpr           -- ^ @A ∧ B@
  | LDisj  LeanExpr LeanExpr           -- ^ @A ∨ B@
  | LBicond LeanExpr LeanExpr          -- ^ @A ↔ B@
  | LForall String LeanExpr LeanExpr   -- ^ @∀ x : T, body@
  | LForallKw String LeanExpr LeanExpr -- ^ @forall x : T, body@ (keyword style)
  | LExists String LeanExpr LeanExpr   -- ^ @∃ x : T, body@
  | LEq LeanExpr LeanExpr              -- ^ @A = B@
  | LIsWithinBounds String String String
    -- ^ @IsWithinBounds lo var hi@ — bounded-membership guard
  | LProjectIntoInterval LeanExpr LeanExpr LeanExpr
    -- ^ @ProjectIntoInterval x lo hi@ — interval projection
  deriving (Eq, Show)


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

-- | Convert an Eidos 'IR.Theory' into a structured 'LeanDoc'.
theoryToLeanDoc :: IR.Theory -> LeanDoc
theoryToLeanDoc theory = LeanDoc
  { leanDocTheoryName = IR.theoryFullyQualifiedName theory
  , leanDocDecls      = concat
      [ headerDecls
      , userSortLimitDecls
      , functionDecls
      , folInverseDecls
      , functionArgResultDecls
      , folInverseArgResDecls
      , mereoDecls
      , propDecls
      , setDecls
      , functionArgResultBoundsAxioms
      , folInverseArgResBoundsAxioms
      , functionFactAxioms
      , folInverseFactAxioms
      , folAdjunctionAxioms
      , mereoBoundsAxioms
      , propBoundsAxioms
      , setBoundsAxioms
      , userSortSetBoundsAxioms
      , sortOrderDecls
      , userFactDecls
      ]
  }
  where
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
              innerQ  = LForallKw "Y" LProp
                          (LImpl (LIsWithinBounds (sortMinName resSort) "Y" (sortMaxName resSort))
                                 body)
              outerQ  = LForallKw "X" LProp
                          (LImpl (LIsWithinBounds (sortMinName argSort) "X" (sortMaxName argSort))
                                 innerQ)
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
              q2      = LForallKw "X2" LProp
                          (LImpl (LIsWithinBounds (sortMinName argSort) "X2" (sortMaxName argSort))
                                 body)
              q1      = LForallKw "X1" LProp
                          (LImpl (LIsWithinBounds (sortMinName resSort) "X1" (sortMaxName resSort))
                                 q2)
          in DeclAxiom (LeanAxiom (fInv ++ "_fact") q1)

    -- -----------------------------------------------------------------------
    -- Function argument and result objects
    -- -----------------------------------------------------------------------
    -- Only user-declared FOL functions — _inv arg/res objects are handled
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
        -- Build: forall X : Prop, (IsWithinBounds lo hi X) → <rest>
        mkBoundedForall :: String -> String -> LeanExpr -> LeanExpr
        mkBoundedForall varN sortN rest =
          let lo = sortMinName sortN
              hi = sortMaxName sortN
          in LForallKw varN LProp
               (LImpl (LIsWithinBounds lo varN hi) rest)

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
  in LForall varN (LVar "Prop") (addBoundedGuard sn varN body)

-- | For built-in sorts, add the membership-guard @IsWithinBounds lo var hi → body@.
-- For user-defined sorts, adds the same using the sort's Min/Max limits.
addBoundedGuard :: String -> String -> LeanExpr -> LeanExpr
addBoundedGuard sortN varN body =
  case sortN of
    "ℙ" -> LImpl (LIsWithinBounds pMinName varN pMaxName) body
    "𝕌" -> LImpl (LIsWithinBounds uMinName varN uMaxName) body
    "𝔻" -> LImpl (LIsWithinBounds dMinName varN dMaxName) body
    _   -> LImpl (LIsWithinBounds (sortN ++ minSuffix) varN (sortN ++ maxSuffix)) body

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
  let varN = IR.resolvedVarName vd
      sn   = IR.sortName (IR.resolvedVarSort vd)
  in LForall varN (LVar "Prop") (addBoundedGuard sn varN body)
quantifierToLean (IR.ResolvedQExists vd) body =
  let varN = IR.resolvedVarName vd
      sn   = IR.sortName (IR.resolvedVarSort vd)
  in LExists varN (LVar "Prop") (addBoundedGuard sn varN body)

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
    | Just base <- stripSuffix "#min" other -> base ++ minSuffix
    | Just base <- stripSuffix "#max" other -> base ++ maxSuffix
    | otherwise                             -> other
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
-- Stage 2 – LeanDoc -> String
-- ---------------------------------------------------------------------------

-- | Render a 'LeanDoc' to Lean 4 source text.
renderLeanDoc :: LeanDoc -> String
renderLeanDoc doc =
  unlines $
       [ "-- Generated by Eidos compiler"
       , "-- Theory: " ++ leanDocTheoryName doc
       , ""
       , "def IsWithinBounds (lo hi x : Prop) : Prop := (hi → x) ∧ (x → lo)"
       , "def ProjectIntoInterval (x lo hi : Prop) : Prop := (x ∧ lo) ∨ hi"
       , ""
       ]
    ++ map renderDecl (leanDocDecls doc)

renderDecl :: LeanDecl -> String
renderDecl DeclBlankLine        = ""
renderDecl (DeclComment c)      = "-- " ++ c
renderDecl (DeclAxiom ax)       = renderAxiom ax

renderAxiom :: LeanAxiom -> String
renderAxiom (LeanAxiom name ty) =
  "axiom " ++ name ++ ": " ++ renderLeanExpr ty

-- | Render a 'LeanExpr' to a Lean 4 string.
renderLeanExpr :: LeanExpr -> String
renderLeanExpr LProp          = "Prop"
renderLeanExpr (LVar n)       = n
renderLeanExpr (LApp f args)  = "(" ++ renderLeanExpr f ++ " " ++ unwords (map renderLeanExpr args) ++ ")"
renderLeanExpr (LImpl a b)    = "(" ++ renderLeanExpr a ++ " → " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LConj a b)    = "(" ++ renderLeanExpr a ++ " ∧ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LDisj a b)    = "(" ++ renderLeanExpr a ++ " ∨ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LBicond a b)  = "(" ++ renderLeanExpr a ++ " ↔ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LForall x ty body) =
  "∀ " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LForallKw x ty body) =
  "forall " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LExists x ty body) =
  "∃ " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LEq a b) =
  renderLeanExpr a ++ " = " ++ renderLeanExpr b
renderLeanExpr (LIsWithinBounds lo v hi) =
  "(IsWithinBounds " ++ lo ++ " " ++ hi ++ " " ++ v ++ ")"
renderLeanExpr (LProjectIntoInterval x lo hi) =
  "(ProjectIntoInterval " ++ renderLeanExpr x ++ " " ++ renderLeanExpr lo ++ " " ++ renderLeanExpr hi ++ ")"

-- ---------------------------------------------------------------------------
-- Convenience entry point
-- ---------------------------------------------------------------------------

-- | Convert an Eidos theory directly to Lean 4 source (combines both stages).
exportToLeanProps :: IR.Theory -> String
exportToLeanProps = renderLeanDoc . theoryToLeanDoc