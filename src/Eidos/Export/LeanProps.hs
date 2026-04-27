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
  | LImpl  LeanExpr LeanExpr           -- ^ @A → B@
  | LConj  LeanExpr LeanExpr           -- ^ @A ∧ B@
  | LDisj  LeanExpr LeanExpr           -- ^ @A ∨ B@
  | LBicond LeanExpr LeanExpr          -- ^ @A ↔ B@
  | LForall String LeanExpr LeanExpr   -- ^ @∀ x : T, body@
  | LExists String LeanExpr LeanExpr   -- ^ @∃ x : T, body@
  | LIsWithinBounds String String String
    -- ^ @IsWithinBounds lo var hi@ — bounded-membership guard
  deriving (Eq, Show)

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
      , mereoDecls
      , propDecls
      , setDecls
      , mereoBoundsAxioms
      , propBoundsAxioms
      , setBoundsAxioms
      , userSortSetBoundsAxioms
      , sortOrderDecls
      , userFactDecls
      ]
  }
  where
    -- -----------------------------------------------------------------------
    -- Header – the six built-in bound objects
    -- -----------------------------------------------------------------------
    headerDecls :: [LeanDecl]
    headerDecls =
      [ DeclComment "Bound objects"
      , DeclAxiom (LeanAxiom "U_Min" LProp)
      , DeclAxiom (LeanAxiom "U_Max" LProp)
      , DeclAxiom (LeanAxiom "P_Min" LProp)
      , DeclAxiom (LeanAxiom "P_Max" LProp)
      , DeclAxiom (LeanAxiom "D_Min" LProp)
      , DeclAxiom (LeanAxiom "D_Max" LProp)
      , DeclBlankLine
      ]

    -- -----------------------------------------------------------------------
    -- User-declared sorts: S_Min / S_Max limit objects
    -- -----------------------------------------------------------------------
    userSorts :: [IR.Sort]
    userSorts =
      [ s
      | IR.EntitySort s <- IR.theoryObjects theory
      , IR.sortKind s == IR.SortKindFromSignature
      ]

    sortMinName :: IR.Sort -> String
    sortMinName s = IR.sortName s ++ "_Min"

    sortMaxName :: IR.Sort -> String
    sortMaxName s = IR.sortName s ++ "_Max"

    userSortLimitDecls :: [LeanDecl]
    userSortLimitDecls = concatMap mkSortLimitDecls userSorts
      where
        mkSortLimitDecls s =
          [ DeclAxiom (LeanAxiom (sortMinName s) LProp)
          , DeclAxiom (LeanAxiom (sortMaxName s) LProp)
          ]

    -- -----------------------------------------------------------------------
    -- 𝕌-kinded (mereological) objects
    -- -----------------------------------------------------------------------
    mereoObjects :: [IR.MereologicalObject]
    mereoObjects =
      [ m
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindMereological
      , IR.mereoOrigin m == IR.FromSignature
      , IR.mereoName   m `notElem` ["U_Min", "U_Max", "⊤", "⊥"]
      ]

    mereoDecls :: [LeanDecl]
    mereoDecls = map (\m -> DeclAxiom (LeanAxiom (IR.mereoName m) LProp)) mereoObjects

    mereoBoundsAxioms :: [LeanDecl]
    mereoBoundsAxioms = concatMap mereoBoundsFor mereoObjects
      where
        mereoBoundsFor m =
          let n = IR.mereoName m
          in [ DeclAxiom (LeanAxiom (n ++ "_min") (LImpl (LVar n) (LVar "U_Min")))
             , DeclAxiom (LeanAxiom (n ++ "_max") (LImpl (LVar "U_Max") (LVar n)))
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
      , IR.mereoName   m `notElem` ["P_Min", "P_Max", "⊤", "⊥", "ℙ#min", "ℙ#max"]
      ]

    propDecls :: [LeanDecl]
    propDecls = map (\m -> DeclAxiom (LeanAxiom (IR.mereoName m) LProp)) propObjects

    propBoundsAxioms :: [LeanDecl]
    propBoundsAxioms = concatMap propBoundsFor propObjects
      where
        propBoundsFor m =
          let n = IR.mereoName m
          in [ DeclAxiom (LeanAxiom (n ++ "_min") (LImpl (LVar n) (LVar "P_Min")))
             , DeclAxiom (LeanAxiom (n ++ "_max") (LImpl (LVar "P_Max") (LVar n)))
             ]

    -- -----------------------------------------------------------------------
    -- 𝔻-kinded sets
    -- -----------------------------------------------------------------------
    setObjects :: [IR.MereologicalObject]
    setObjects =
      [ m
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind   m == IR.MereologicalEntityKindSet
      , IR.mereoOrigin m == IR.FromSignature
      , IR.sortKind  (IR.mereoSort m) == IR.SortKindDomain
      , IR.sortName  (IR.mereoSort m) == "𝔻"
      ]

    setDecls :: [LeanDecl]
    setDecls = map (\m -> DeclAxiom (LeanAxiom (IR.mereoName m) LProp)) setObjects

    setBoundsAxioms :: [LeanDecl]
    setBoundsAxioms = concatMap setBoundsFor setObjects
      where
        setBoundsFor m =
          let n = IR.mereoName m
          in [ DeclAxiom (LeanAxiom (n ++ "_min") (LImpl (LVar n) (LVar "D_Min")))
             , DeclAxiom (LeanAxiom (n ++ "_max") (LImpl (LVar "D_Max") (LVar n)))
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
              sMin = sortMinName (IR.mereoSort m)
              sMax = sortMaxName (IR.mereoSort m)
          in [ DeclAxiom (LeanAxiom (n ++ "_min") (LImpl (LVar n) (LVar sMin)))
             , DeclAxiom (LeanAxiom (n ++ "_max") (LImpl (LVar sMax) (LVar n)))
             ]

    -- -----------------------------------------------------------------------
    -- Sort-ordering axioms
    -- -----------------------------------------------------------------------
    sortOrderDecls :: [LeanDecl]
    sortOrderDecls =
      [ DeclBlankLine
      , DeclComment "Sort ordering lattice"
      , DeclComment "U_Max is the top, U_Min is the bottom"
      , DeclAxiom (LeanAxiom "U_ordering" (LImpl (LVar "U_Max") (LVar "U_Min")))
      , DeclComment "P sits between user sorts and U_Min"
      , DeclAxiom (LeanAxiom "U_to_P" (LImpl (LVar "U_Max") (LVar "P_Max")))
      , DeclAxiom (LeanAxiom "P_ordering" (LImpl (LVar "P_Max") (LVar "P_Min")))
      , DeclAxiom (LeanAxiom "P_to_U" (LImpl (LVar "P_Min") (LVar "U_Min")))
      , DeclComment "D and all user sorts sit between U_Max and P_Max"
      , DeclAxiom (LeanAxiom "D_upper" (LImpl (LVar "U_Max") (LVar "D_Max")))
      , DeclAxiom (LeanAxiom "D_ordering" (LImpl (LVar "D_Max") (LVar "D_Min")))
      , DeclAxiom (LeanAxiom "D_lower" (LImpl (LVar "D_Min") (LVar "P_Max")))
      ]
      ++ concatMap userSortOrderAxioms userSorts
      ++ [DeclBlankLine]
      where
        userSortOrderAxioms s =
          let sortName = IR.sortName s
              sMax = sortMaxName s
              sMin = sortMinName s
          in [ DeclAxiom (LeanAxiom (sortName ++ "_upper") (LImpl (LVar "U_Max") (LVar sMax)))
            , DeclAxiom (LeanAxiom (sortName ++ "_ordering") (LImpl (LVar sMax) (LVar sMin)))
            , DeclAxiom (LeanAxiom (sortName ++ "_lower") (LImpl (LVar sMin) (LVar "P_Max")))
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
    assertionDecl idx fact = mkFactAxiom (mkLabel idx) (LVar "P_Min") (factBody fact)

    metafactDecl :: Int -> IR.Fact -> LeanDecl
    metafactDecl idx fact = mkFactAxiom (mkLabel idx) (LVar "U_Min") (factBody fact)

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
    "ℙ" -> LImpl (LIsWithinBounds "P_Min" varN "P_Max") body
    "𝕌" -> LImpl (LIsWithinBounds "U_Min" varN "U_Max") body
    "𝔻" -> LImpl (LIsWithinBounds "D_Min" varN "D_Max") body
    _   -> LImpl (LIsWithinBounds (sortN ++ "_Min") varN (sortN ++ "_Max")) body

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
  LImpl (negToLean inner) (LVar "P_Max")
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
atomicPropToLean (IR.ResolvedAtomicConstant ref) = LVar (resolveConstRef ref)
atomicPropToLean (IR.ResolvedAtomicTermPair tp)  = termPairToLean tp

-- ---------------------------------------------------------------------------
-- Constant-reference resolution
-- ---------------------------------------------------------------------------

resolveConstRef :: IR.ResolvedConstantRef -> String
resolveConstRef ref =
  case IR.resolvedConstRefName ref of
    "ℙ#min" -> "P_Min"
    "ℙ#max" -> "P_Max"
    "𝕌#min" -> "U_Min"
    "𝕌#max" -> "U_Max"
    "𝔻#min" -> "D_Min"
    "𝔻#max" -> "D_Max"
    "⊤"     -> "P_Min"
    "⊥"     -> "P_Max"
    other   -> other

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
  case (base, suffixes) of
    (IR.ResolvedBTAtomic ref, IR.ResolvedSuffixSpecialOp attr : _rest)
      | attr `elem` ["min", "max"] ->
          let baseName = IR.resolvedConstRefName ref
              leanName = case (baseName, attr) of
                ("ℙ", "min") -> "P_Min"
                ("ℙ", "max") -> "P_Max"
                ("𝕌", "min") -> "U_Min"
                ("𝕌", "max") -> "U_Max"
                ("𝔻", "min") -> "D_Min"
                ("𝔻", "max") -> "D_Max"
                (s,   "min") -> s ++ "_Min"
                (s,   "max") -> s ++ "_Max"
                _            -> baseName ++ "#" ++ attr
          in LVar leanName
    _ -> baseTermToLean base

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
  termToLean (IR.resolvedPTOperand pts)
baseTermToLean (IR.ResolvedBTProjectionToInterval pti) =
  termToLean (IR.resolvedPTIOperand pti)
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
renderLeanExpr (LImpl a b)    = "(" ++ renderLeanExpr a ++ " → " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LConj a b)    = "(" ++ renderLeanExpr a ++ " ∧ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LDisj a b)    = "(" ++ renderLeanExpr a ++ " ∨ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LBicond a b)  = "(" ++ renderLeanExpr a ++ " ↔ " ++ renderLeanExpr b ++ ")"
renderLeanExpr (LForall x ty body) =
  "∀ " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LExists x ty body) =
  "∃ " ++ x ++ " : " ++ renderLeanExpr ty ++ ", " ++ renderLeanExpr body
renderLeanExpr (LIsWithinBounds lo v hi) =
  "IsWithinBounds " ++ lo ++ " " ++ hi ++ " " ++ v

-- ---------------------------------------------------------------------------
-- Convenience entry point
-- ---------------------------------------------------------------------------

-- | Convert an Eidos theory directly to Lean 4 source (combines both stages).
exportToLeanProps :: IR.Theory -> String
exportToLeanProps = renderLeanDoc . theoryToLeanDoc
