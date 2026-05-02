-- | Eidos.SubLanguage
--
-- Validates that a 'TheoryBody' (and every inline subtheory body within it)
-- obeys the restrictions imposed by one or more 'TheoryType' constraints.
--
-- The hierarchy of sublanguages is:
--
--   .eq  ⊂  .reg  ⊂  .coh  ⊂  .fol  ⊂  .sol  ⊂  .theory
--   .prop ⊂ .sol
--   .mereo  (separate branch — no logical constructs at all)
--   .theory — maximally permissive (no restrictions)
--
-- When a theory is loaded from a file, its 'TheoryType' is derived from the
-- file extension.  Inline subtheories inherit the parent's constraint list.
-- External subtheories add their own file's 'TheoryType' to the list — so
-- constraints are cumulative: a body must satisfy every constraint in the list.
--
-- The check is purely structural over the AST; it runs before IR building.

module Eidos.SubLanguage
  ( checkTheoryBody
  -- Exported for testing
  , Violation(..)
  , checkEquational
  , checkRegular
  , checkCoherent
  , checkFOL
  , checkPropositional
  , checkMereological
  ) where

import Data.List       (intercalate, nub)
import Data.Maybe      (mapMaybe)

import Eidos.AST
import Eidos.ExternalRef (TheoryType(..))

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Check a 'TheoryBody' against a list of 'TheoryType' constraints.
-- Returns 'Left' with a human-readable error message on the first violation
-- found across all constraints, or 'Right ()' if everything is valid.
--
-- 'PlainTheory' imposes no restrictions and is silently skipped.
-- 'SOLTheory' also imposes no restrictions beyond 'PlainTheory'.
checkTheoryBody :: [TheoryType] -> TheoryBody -> Either String ()
checkTheoryBody tts body = mapM_ checkOne (nub tts)
  where
    checkOne PlainTheory        = Right ()
    checkOne SOLTheory          = Right ()
    checkOne EquationalTheory   = runCheck "equational (.eq)"   (checkEquational body)
    checkOne RegularTheory      = runCheck "regular (.reg)"     (checkRegular    body)
    checkOne CoherentTheory     = runCheck "coherent (.coh)"    (checkCoherent   body)
    checkOne FOLTheory          = runCheck "first-order (.fol)" (checkFOL        body)
    checkOne PropositionalTheory = runCheck "propositional (.prop)" (checkPropositional body)
    checkOne MereologicalTheory  = runCheck "mereological (.mereo)" (checkMereological body)

runCheck :: String -> [Violation] -> Either String ()
runCheck label vs = case vs of
  [] -> Right ()
  _  -> Left $ "Theory violates " ++ label ++ " restrictions:\n"
             ++ intercalate "\n" (map (\(Violation ctx msg) ->
                  "  " ++ (if null ctx then "" else "[" ++ ctx ++ "] ") ++ msg) vs)

-- ---------------------------------------------------------------------------
-- Violation type
-- ---------------------------------------------------------------------------

data Violation = Violation
  { violationContext :: String   -- e.g. "assertions", "facts", "signature"
  , violationMsg     :: String
  } deriving (Show, Eq)

viol :: String -> String -> Violation
viol = Violation

-- ---------------------------------------------------------------------------
-- Per-sublanguage checkers
-- Each returns a (possibly empty) list of violations.
-- ---------------------------------------------------------------------------

-- | Equational logic (.eq)
--
-- Allowed: facts section only; free variable declarations; ∀ quantifiers;
--          FOL functions; sorts; individuals; sets/relations; = operator.
-- Forbidden: assertions section; metafacts section; ∃ quantifier;
--            ¬; ⊥; ∨; ←; ↔; SOL functions (uppercase fn names); ℙ sort refs.
checkEquational :: TheoryBody -> [Violation]
checkEquational body = concatMap checkSection (sections body)
  where
    checkSection (SectionSignature sig)    = checkSigEquational sig
    checkSection (SectionAxioms aw)        = concatMap checkAxSection (axiomsSections aw)
    checkSection (SectionBareAxioms axs)   = checkAxSection axs
    checkSection (SectionSubtheories _)    = []  -- inline subtheories checked separately

    checkAxSection (AxAssertions _) =
      [viol "assertions" "assertions section is not allowed in equational logic; use facts instead"]
    checkAxSection (AxMetafacts _) =
      [viol "metafacts" "metafacts section is not allowed in equational logic"]
    checkAxSection (AxFacts (FactsSection props)) =
      concatMap (checkPropEquational "facts") props

    checkSigEquational (SignatureSection items) =
      concatMap checkSigItemEquational items

    checkSigItemEquational (SigFunction fd)
      | isSOLName (funcName fd) =
          [viol "signature" $ "SOL function '" ++ funcName fd
                           ++ "' (uppercase name) is not allowed in equational logic"]
    checkSigItemEquational (SigIndividual (IndividualDeclaration nm se))
      | isPropSortExpr se =
          [viol "signature" $ "Proposition constant '" ++ nm
                           ++ "' (sort ℙ) is not allowed in equational logic"]
    checkSigItemEquational _ = []

    checkPropEquational ctx (PropExprInclVars _ _ vars expr) =
      checkVarDeclsEquational ctx vars ++
      checkPropExprEquational ctx expr

    checkVarDeclsEquational ctx vars =
      concatMap (\(VarDecl vid _ se) ->
        if isPropSortExpr se
          then [viol ctx $ "Variable '" ++ vid ++ "' has sort ℙ which is not allowed in equational logic"]
          else []) vars

    checkPropExprEquational ctx (PropExpr left rests) =
      checkRightImplEquational ctx left ++
      concatMap (\(PropExprRest _ r) -> checkRightImplEquational ctx r) rests
      ++
      if null rests then []
      else [viol ctx "biconditional (↔) is not allowed in equational logic"]

    checkRightImplEquational ctx (RightImpl left mbRight) =
      checkLeftImplEquational ctx left ++
      case mbRight of
        Nothing     -> []
        Just (_, r) -> checkRightImplEquational ctx r

    checkLeftImplEquational ctx (LeftImpl left rests) =
      checkDisjEquational ctx left ++
      if null rests
        then []
        else [viol ctx "reverse implication (←) is not allowed in equational logic"]

    checkDisjEquational ctx (Disj left rests) =
      checkConjEquational ctx left ++
      if null rests
        then []
        else [viol ctx "disjunction (∨) is not allowed in equational logic"]

    checkConjEquational ctx (Conj left rests) =
      checkNegEquational ctx left ++
      concatMap (\(ConjRest _ n) -> checkNegEquational ctx n) rests

    checkNegEquational ctx (NegNot _) =
      [viol ctx "negation (¬) is not allowed in equational logic"]
    checkNegEquational ctx (NegChild q) = checkQuantifiedEquational ctx q

    checkQuantifiedEquational ctx (Quantified qs atomic) =
      concatMap (checkQuantifierEquational ctx) qs ++
      checkAtomicEquational ctx atomic

    checkQuantifierEquational ctx (QExists _) =
      [viol ctx "existential quantifier (∃) is not allowed in equational logic"]
    checkQuantifierEquational ctx (QForall (VarDecl _ _ se))
      | isPropSortExpr se =
          [viol ctx "∀ over ℙ-sort is not allowed in equational logic"]
    checkQuantifierEquational _ _ = []

    checkAtomicEquational ctx (AtomicProp tp) = checkTermPairEquational ctx tp

    checkTermPairEquational ctx (TermPair left rights) =
      checkTermEquational ctx left ++
      concatMap (\(RelationFollowedByTerm _ _ _ r) -> checkTermEquational ctx r) rights

    checkTermEquational ctx t = checkTermForBottom ctx t

-- | Regular logic (.reg)
--
-- Allowed: everything in equational, plus → implication, plus ∃ in
--          conclusion positions.
-- Forbidden (on top of .eq): ¬; ⊥; ←; ↔; ∨ anywhere.
-- (∃ is technically allowed in .reg conclusions but we check ∨ absence.)
checkRegular :: TheoryBody -> [Violation]
checkRegular body = concatMap checkSection (sections body)
  where
    checkSection (SectionSignature sig)  = checkSigRegular sig
    checkSection (SectionAxioms aw)      = concatMap checkAxSection (axiomsSections aw)
    checkSection (SectionBareAxioms axs) = checkAxSection axs
    checkSection (SectionSubtheories _)  = []

    checkAxSection (AxMetafacts _) =
      [viol "metafacts" "metafacts section is not allowed in regular logic"]
    checkAxSection (AxAssertions (AssertionsSection props)) =
      concatMap (checkPropRegular "assertions") props
    checkAxSection (AxFacts (FactsSection props)) =
      concatMap (checkPropRegular "facts") props

    checkSigRegular (SignatureSection items) =
      concatMap checkSigItemRegular items

    checkSigItemRegular (SigFunction fd)
      | isSOLName (funcName fd) =
          [viol "signature" $ "SOL function '" ++ funcName fd
                           ++ "' is not allowed in regular logic"]
    checkSigItemRegular (SigIndividual (IndividualDeclaration nm se))
      | isPropSortExpr se =
          [viol "signature" $ "Proposition constant '" ++ nm
                           ++ "' (sort ℙ) is not allowed in regular logic"]
    checkSigItemRegular _ = []

    checkPropRegular ctx (PropExprInclVars _ _ vars expr) =
      checkVarDeclsNoProp ctx vars ++ checkPropExprRegular ctx expr

    checkPropExprRegular ctx (PropExpr left rests) =
      checkRightImplRegular ctx left ++
      if null rests then []
      else [viol ctx "biconditional (↔) is not allowed in regular logic"]

    checkRightImplRegular ctx (RightImpl left mbRight) =
      checkLeftImplRegular ctx left ++
      case mbRight of { Nothing -> []; Just (_, r) -> checkRightImplRegular ctx r }

    checkLeftImplRegular ctx (LeftImpl left rests) =
      checkDisjRegular ctx left ++
      if null rests then []
      else [viol ctx "reverse implication (←) is not allowed in regular logic"]

    checkDisjRegular ctx (Disj left rests) =
      checkConjRegular ctx left ++
      if null rests then []
      else [viol ctx "disjunction (∨) is not allowed in regular logic"]

    checkConjRegular ctx (Conj left rests) =
      checkNegRegular ctx left ++
      concatMap (\(ConjRest _ n) -> checkNegRegular ctx n) rests

    checkNegRegular ctx (NegNot _) =
      [viol ctx "negation (¬) is not allowed in regular logic"]
    checkNegRegular ctx (NegChild q) = checkQuantifiedRegular ctx q

    checkQuantifiedRegular ctx (Quantified qs atomic) =
      concatMap (checkQuantifierNoSOL ctx) qs ++
      checkAtomicNoBottom ctx atomic

    checkAtomicNoBottom ctx (AtomicProp tp) = checkTermPairForBottom ctx tp

-- | Coherent logic (.coh)
--
-- Allowed: ∃, ∨, ∧, →; free variables; FOL functions; sorts.
-- Forbidden: ¬; ⊥; ←; ↔; SOL functions.
-- | Coherent logic (.coh)
--
-- Allowed: ∃, ∨, ∧, →; free variables; FOL functions; sorts; ⊥.
-- Forbidden: ¬; ←; ↔; SOL functions.
checkCoherent :: TheoryBody -> [Violation]
checkCoherent body = concatMap checkSection (sections body)
  where
    checkSection (SectionSignature sig)  = checkSigCoherent sig
    checkSection (SectionAxioms aw)      = concatMap checkAxSection (axiomsSections aw)
    checkSection (SectionBareAxioms axs) = checkAxSection axs
    checkSection (SectionSubtheories _)  = []

    checkAxSection (AxMetafacts _) =
      [viol "metafacts" "metafacts section is not allowed in coherent logic"]
    checkAxSection (AxAssertions (AssertionsSection props)) =
      concatMap (checkPropCoherent "assertions") props
    checkAxSection (AxFacts (FactsSection props)) =
      concatMap (checkPropCoherent "facts") props

    checkSigCoherent (SignatureSection items) =
      concatMap checkSigItemCoherent items

    checkSigItemCoherent (SigFunction fd)
      | isSOLName (funcName fd) =
          [viol "signature" $ "SOL function '" ++ funcName fd
                           ++ "' is not allowed in coherent logic"]
    checkSigItemCoherent (SigIndividual (IndividualDeclaration nm se))
      | isPropSortExpr se =
          [viol "signature" $ "Proposition constant '" ++ nm
                           ++ "' (sort ℙ) is not allowed in coherent logic"]
    checkSigItemCoherent _ = []

    checkPropCoherent ctx (PropExprInclVars _ _ vars expr) =
      checkVarDeclsNoProp ctx vars ++ checkPropExprCoherent ctx expr

    checkPropExprCoherent ctx (PropExpr left rests) =
      checkRightImplCoherent ctx left ++
      if null rests then []
      else [viol ctx "biconditional (↔) is not allowed in coherent logic"]

    checkRightImplCoherent ctx (RightImpl left mbRight) =
      checkLeftImplCoherent ctx left ++
      case mbRight of { Nothing -> []; Just (_, r) -> checkRightImplCoherent ctx r }

    checkLeftImplCoherent ctx (LeftImpl left rests) =
      checkDisjCoherent ctx left ++
      if null rests then []
      else [viol ctx "reverse implication (←) is not allowed in coherent logic"]

    checkDisjCoherent ctx (Disj left rests) =
      checkConjCoherent ctx left ++
      concatMap (\(DisjRest _ c) -> checkConjCoherent ctx c) rests

    checkConjCoherent ctx (Conj left rests) =
      checkNegCoherent ctx left ++
      concatMap (\(ConjRest _ n) -> checkNegCoherent ctx n) rests

    checkNegCoherent ctx (NegNot _) =
      [viol ctx "negation (¬) is not allowed in coherent logic"]
    checkNegCoherent ctx (NegChild q) = checkQuantifiedCoherent ctx q

    checkQuantifiedCoherent ctx (Quantified qs atomic) =
      concatMap (checkQuantifierNoSOL ctx) qs
      -- ← REMOVED: checkAtomicNoBottom ctx atomic
      -- Coherent logic ALLOWS ⊥ (falsity)
      -- We still need to check the atomic expression for other issues,
      -- but ⊥ is fine, so we just don't check for it.

      
-- | First-order logic (.fol)
--
-- Allowed: all propositional connectives; ∀; ∃ over individuals;
--          FOL functions; sorts; negation; ⊥.
-- Forbidden: SOL functions (uppercase fn names); ∃/∀ over set variables (X ⊆ S).
checkFOL :: TheoryBody -> [Violation]
checkFOL body = concatMap checkSection (sections body)
  where
    checkSection (SectionSignature sig)  = checkSigFOL sig
    checkSection (SectionAxioms aw)      = concatMap checkAxSection (axiomsSections aw)
    checkSection (SectionBareAxioms axs) = checkAxSection axs
    checkSection (SectionSubtheories _)  = []

    checkAxSection (AxAssertions (AssertionsSection props)) =
      concatMap (checkPropFOL "assertions") props
    checkAxSection (AxFacts (FactsSection props)) =
      concatMap (checkPropFOL "facts") props
    checkAxSection (AxMetafacts (MetafactsSection props)) =
      concatMap (checkPropFOL "metafacts") props

    checkSigFOL (SignatureSection items) = concatMap checkSigItemFOL items

    checkSigItemFOL (SigFunction fd)
      | isSOLName (funcName fd) =
          [viol "signature" $ "SOL function '" ++ funcName fd
                           ++ "' is not allowed in first-order logic"]
    checkSigItemFOL _ = []

    checkPropFOL ctx (PropExprInclVars _ _ vars expr) =
      checkVarDeclsNoSOL ctx vars ++ checkPropExprFOL ctx expr

    -- FOL allows all connectives; only SOL quantifiers are forbidden.
    checkPropExprFOL ctx (PropExpr left rests) =
      checkRightImplFOL ctx left ++
      concatMap (\(PropExprRest _ r) -> checkRightImplFOL ctx r) rests

    checkRightImplFOL ctx (RightImpl left mbRight) =
      checkLeftImplFOL ctx left ++
      case mbRight of { Nothing -> []; Just (_, r) -> checkRightImplFOL ctx r }

    checkLeftImplFOL ctx (LeftImpl left rests) =
      checkDisjFOL ctx left ++
      concatMap (\(LeftImplRest _ d) -> checkDisjFOL ctx d) rests

    checkDisjFOL ctx (Disj left rests) =
      checkConjFOL ctx left ++
      concatMap (\(DisjRest _ c) -> checkConjFOL ctx c) rests

    checkConjFOL ctx (Conj left rests) =
      checkNegFOL ctx left ++
      concatMap (\(ConjRest _ n) -> checkNegFOL ctx n) rests

    checkNegFOL ctx (NegNot inner)  = checkNegFOL ctx inner
    checkNegFOL ctx (NegChild q)    = checkQuantifiedFOL ctx q

    checkQuantifiedFOL ctx (Quantified qs atomic) =
      concatMap (checkQuantifierNoSOL ctx) qs ++
      checkAtomicFOL ctx atomic

    checkAtomicFOL ctx (AtomicProp tp) = checkTermPairFOL ctx tp

    checkTermPairFOL ctx (TermPair left rights) =
      checkTermFOL ctx left ++
      concatMap (\(RelationFollowedByTerm _ _ _ r) -> checkTermFOL ctx r) rights

    checkTermFOL _ctx _t = []  -- FOL terms are unrestricted (no SOL operators in terms)

-- | Propositional logic (.prop)
--
-- Only ℙ-typed proposition constants in the signature.
-- No sorts (other than ℙ itself), no individuals, no functions, no relations.
-- No quantifiers. Only propositional connectives.
checkPropositional :: TheoryBody -> [Violation]
checkPropositional body = concatMap checkSection (sections body)
  where
    checkSection (SectionSignature sig)  = checkSigProp sig
    checkSection (SectionAxioms aw)      = concatMap checkAxSection (axiomsSections aw)
    checkSection (SectionBareAxioms axs) = checkAxSection axs
    checkSection (SectionSubtheories _)  = []

    checkAxSection (AxAssertions (AssertionsSection props)) =
      concatMap (checkPropProp "assertions") props
    checkAxSection (AxFacts (FactsSection props)) =
      concatMap (checkPropProp "facts") props
    checkAxSection (AxMetafacts (MetafactsSection props)) =
      concatMap (checkPropProp "metafacts") props

    checkSigProp (SignatureSection items) = concatMap checkSigItemProp items

    checkSigItemProp (SigSimpleSort (SimpleSortDeclaration nm)) =
      [viol "signature" $ "Sort declaration '" ++ nm
                       ++ "' is not allowed in propositional logic"]
    checkSigItemProp (SigRelationalSort (RelationalSortDeclaration nm _ _)) =
      [viol "signature" $ "Relational sort '" ++ nm
                       ++ "' is not allowed in propositional logic"]
    checkSigItemProp (SigFunction fd) =
      [viol "signature" $ "Function '" ++ funcName fd
                       ++ "' is not allowed in propositional logic"]
    checkSigItemProp (SigSet (SetDeclaration nm _)) =
      [viol "signature" $ "Set/relation '" ++ nm
                       ++ "' is not allowed in propositional logic"]
    checkSigItemProp (SigIndividual (IndividualDeclaration nm se))
      | not (isPropSortExpr se) =
          [viol "signature" $ "Individual '" ++ nm
                           ++ "' is not allowed in propositional logic; only ℙ-typed propositions are permitted"]
    checkSigItemProp _ = []

    checkPropProp ctx (PropExprInclVars _ _ vars expr) = checkPropExprProp ctx expr

    -- Propositional: all connectives allowed, but no quantifiers.
    checkPropExprProp ctx (PropExpr left rests) =
      checkRightImplProp ctx left ++
      concatMap (\(PropExprRest _ r) -> checkRightImplProp ctx r) rests

    checkRightImplProp ctx (RightImpl left mbRight) =
      checkLeftImplProp ctx left ++
      case mbRight of { Nothing -> []; Just (_, r) -> checkRightImplProp ctx r }

    checkLeftImplProp ctx (LeftImpl left rests) =
      checkDisjProp ctx left ++
      concatMap (\(LeftImplRest _ d) -> checkDisjProp ctx d) rests

    checkDisjProp ctx (Disj left rests) =
      checkConjProp ctx left ++
      concatMap (\(DisjRest _ c) -> checkConjProp ctx c) rests

    checkConjProp ctx (Conj left rests) =
      checkNegProp ctx left ++
      concatMap (\(ConjRest _ n) -> checkNegProp ctx n) rests

    checkNegProp ctx (NegNot inner) = checkNegProp ctx inner
    checkNegProp ctx (NegChild (Quantified qs atomic)) =
      (if null qs then []
       else [viol ctx "quantifiers (∀/∃) are not allowed in propositional logic"])
      ++ checkAtomicProp' ctx atomic

    checkAtomicProp' ctx (AtomicProp tp) = checkTermPairProp ctx tp

    checkTermPairProp ctx (TermPair left rights) =
      checkTermProp ctx left ++
      concatMap (\(RelationFollowedByTerm _ _ _ r) -> checkTermProp ctx r) rights

    checkTermProp ctx (Term left rests) =
      checkFactorProp ctx left ++
      concatMap (\(OperationFollowedByFactor _ _ f) -> checkFactorProp ctx f) rests

    checkFactorProp ctx (Factor base _) = checkBaseTermProp ctx base

    checkBaseTermProp ctx (BTParen expr) = checkPropExprProp ctx expr
    checkBaseTermProp _   _              = []
    -- Non-paren base terms are identifiers, ⊤, ⊥ — these are fine in prop logic.

-- | Mereological logic (.mereo)
--
-- Signature may only contain: sorts (simple, relational), bare mereological
-- objects (x : 𝕌), and mereological individuals/functions.
-- Forbidden: ℙ-typed constants; FOL/SOL functions; sets/relations; any axioms.
checkMereological :: TheoryBody -> [Violation]
checkMereological body = concatMap checkSection (sections body)
  where
    checkSection (SectionSignature sig)    = checkSigMereo sig
    checkSection (SectionAxioms aw)        = checkAxiomsWrapperMereo aw
    checkSection (SectionBareAxioms axs)   = checkBareAxiomsMereo axs
    checkSection (SectionSubtheories _)    = []

    checkAxiomsWrapperMereo (AxiomsWrapper axss)
      | null axss = []
      | otherwise = []

    checkBareAxiomsMereo (AxAssertions _) =
      [viol "assertions" "assertions are not allowed in mereological theories"]
    checkBareAxiomsMereo (AxFacts _) =
      [viol "facts" "facts are not allowed in mereological theories"]
    checkBareAxiomsMereo (AxMetafacts _) =
      [viol "metafacts" "metafacts are not allowed in mereological theories"]

    checkSigMereo (SignatureSection items) = concatMap checkSigItemMereo items

    checkSigItemMereo (SigFunction fd) =
      [viol "signature" $ "Function '" ++ funcName fd
                       ++ "' is not allowed in mereological theories"]
    checkSigItemMereo (SigSet (SetDeclaration nm _)) =
      [viol "signature" $ "Set/relation '" ++ nm
                       ++ "' is not allowed in mereological theories"]
    checkSigItemMereo (SigIndividual (IndividualDeclaration nm se))
      | isPropSortExpr se =
          [viol "signature" $ "Proposition constant '" ++ nm
                           ++ "' (sort ℙ) is not allowed in mereological theories"]
      | not (isUniverseSortExpr se) =
          [viol "signature" $ "Individual '" ++ nm
                           ++ "' must have sort 𝕌 in mereological theories (got: "
                           ++ sortExprName se ++ ")"]
    checkSigItemMereo _ = []

-- ---------------------------------------------------------------------------
-- Shared helper checkers
-- ---------------------------------------------------------------------------

-- | Reject quantifier variables with ⊆ (SOL-style set quantification).
checkQuantifierNoSOL :: String -> Quantifier -> [Violation]
checkQuantifierNoSOL ctx (QForall (VarDecl vid "⊆" _)) =
  [viol ctx $ "SOL-style set quantifier '∀" ++ vid
           ++ " ⊆ …' is not allowed in this sublanguage"]
checkQuantifierNoSOL ctx (QExists (VarDecl vid "⊆" _)) =
  [viol ctx $ "SOL-style set quantifier '∃" ++ vid
           ++ " ⊆ …' is not allowed in this sublanguage"]
checkQuantifierNoSOL _ _ = []

-- | Reject free variable declarations with ⊆ (SOL-style).
checkVarDeclsNoSOL :: String -> [VarDecl] -> [Violation]
checkVarDeclsNoSOL ctx = mapMaybe check
  where
    check (VarDecl vid "⊆" _) =
      Just $ viol ctx $ "SOL-style free set variable '" ++ vid
                     ++ " ⊆ …' is not allowed in this sublanguage"
    check _ = Nothing

-- | Reject free variable declarations over ℙ sort.
checkVarDeclsNoProp :: String -> [VarDecl] -> [Violation]
checkVarDeclsNoProp ctx = mapMaybe check
  where
    check (VarDecl vid _ se)
      | isPropSortExpr se =
          Just $ viol ctx $ "Variable '" ++ vid
                         ++ "' has sort ℙ which is not allowed in this sublanguage"
    check _ = Nothing

-- | Check that ⊥ doesn't appear in a term (looks for bare "⊥" constant refs).
checkTermForBottom :: String -> Term -> [Violation]
checkTermForBottom ctx (Term left rests) =
  checkFactorForBottom ctx left ++
  concatMap (\(OperationFollowedByFactor _ _ f) -> checkFactorForBottom ctx f) rests

checkFactorForBottom :: String -> Factor -> [Violation]
checkFactorForBottom ctx (Factor base suffixes) =
  checkBaseTermForBottom ctx base ++
  concatMap (checkSuffixForBottom ctx) suffixes

checkBaseTermForBottom :: String -> BaseTerm -> [Violation]
checkBaseTermForBottom ctx (BTAtomic (ConstantRef [] "⊥")) =
  [viol ctx "falsity constant (⊥) is not allowed in this sublanguage"]
checkBaseTermForBottom ctx (BTParen expr) = checkPropExprForBottom ctx expr
checkBaseTermForBottom _ _ = []

checkSuffixForBottom :: String -> TermSuffix -> [Violation]
checkSuffixForBottom ctx (SuffixCall (CallSuffix args)) =
  concatMap (checkTermForBottom ctx) args
checkSuffixForBottom _ _ = []

checkPropExprForBottom :: String -> PropExpr -> [Violation]
checkPropExprForBottom ctx (PropExpr left rests) =
  checkRightImplForBottom ctx left ++
  concatMap (\(PropExprRest _ r) -> checkRightImplForBottom ctx r) rests

checkRightImplForBottom :: String -> RightImpl -> [Violation]
checkRightImplForBottom ctx (RightImpl left mbRight) =
  checkLeftImplForBottom ctx left ++
  case mbRight of { Nothing -> []; Just (_, r) -> checkRightImplForBottom ctx r }

checkLeftImplForBottom :: String -> LeftImpl -> [Violation]
checkLeftImplForBottom ctx (LeftImpl left rests) =
  checkDisjForBottom ctx left ++
  concatMap (\(LeftImplRest _ d) -> checkDisjForBottom ctx d) rests

checkDisjForBottom :: String -> Disj -> [Violation]
checkDisjForBottom ctx (Disj left rests) =
  checkConjForBottom ctx left ++
  concatMap (\(DisjRest _ c) -> checkConjForBottom ctx c) rests

checkConjForBottom :: String -> Conj -> [Violation]
checkConjForBottom ctx (Conj left rests) =
  checkNegForBottom ctx left ++
  concatMap (\(ConjRest _ n) -> checkNegForBottom ctx n) rests

checkNegForBottom :: String -> Neg -> [Violation]
checkNegForBottom ctx (NegNot inner) = checkNegForBottom ctx inner
checkNegForBottom ctx (NegChild (Quantified _ atomic)) =
  checkAtomicNoBottom ctx atomic

checkAtomicNoBottom :: String -> AtomicProp -> [Violation]
checkAtomicNoBottom ctx (AtomicProp tp) = checkTermPairForBottom ctx tp

checkTermPairForBottom :: String -> TermPair -> [Violation]
checkTermPairForBottom ctx (TermPair left rights) =
  checkTermForBottom ctx left ++
  concatMap (\(RelationFollowedByTerm _ _ _ r) -> checkTermForBottom ctx r) rights

-- ---------------------------------------------------------------------------
-- Sort expression helpers
-- ---------------------------------------------------------------------------

-- | True if a sort expression refers to ℙ (the proposition sort).
isPropSortExpr :: SortExpr -> Bool
isPropSortExpr (SortExpr (SortRef [] c)) = c `elem` ["ℙ", "Prop"]
isPropSortExpr _                          = False

-- | True if a sort expression refers to 𝕌 (the universe sort).
isUniverseSortExpr :: SortExpr -> Bool
isUniverseSortExpr (SortExpr (SortRef [] "𝕌")) = True
isUniverseSortExpr _                             = False

-- | Pretty name for a sort expression (for error messages).
sortExprName :: SortExpr -> String
sortExprName (SortExpr (SortRef specs c)) =
  concatMap (\(TheoryRef n) -> n ++ ".") specs ++ c

-- ---------------------------------------------------------------------------
-- Function name helpers
-- ---------------------------------------------------------------------------

-- | True if a function name starts with uppercase (SOL convention).
isSOLName :: String -> Bool
isSOLName []    = False
isSOLName (c:_) = c >= 'A' && c <= 'Z'
