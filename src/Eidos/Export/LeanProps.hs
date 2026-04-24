-- | Export an Eidos propositional theory to Lean 4 using the \"all Props\" strategy.
--
-- Every ℙ-kinded object in the signature becomes an @axiom : Prop@.
-- Every assertion becomes an @axiom : (formula) ↔ _Top@.
-- Quantified variables [X : ℙ] become @forall X : Prop,@.
-- Negation ¬P is rendered as @(P → _Bot)@.
-- ⊤ / ⊥ in the source become @_Top@ / @_Bot@.
--
-- Only assertions (FactKindAssertion) that are not inherited and not mereological
-- translations are emitted.  Inherited/auto-generated facts are skipped because
-- they represent compiler bookkeeping, not the user's axioms.
module Eidos.Export.LeanProps
  ( exportToLeanProps
  ) where

import Data.List (intercalate, isPrefixOf)
import qualified Eidos.IR as IR

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

-- | Render a fully-built 'IR.Theory' as a Lean 4 file string using the
--   @--lean_using_props@ strategy.
exportToLeanProps :: IR.Theory -> String
exportToLeanProps theory =
  unlines $
       [ "axiom _Top : Prop"
       , "axiom _Bot : Prop"
       ]
    ++ propAxioms
    ++ assertionAxioms
  where
    -- Collect all ℙ-kinded mereological objects that were declared in the
    -- signature (FromSignature origin, PropositionClass kind).
    propAxioms =
      [ "axiom " ++ IR.mereoName m ++ " : Prop"
      | IR.EntityMereological m <- IR.theoryObjects theory
      , IR.mereoKind m == IR.MereologicalEntityKindProposition
      , IR.mereoOrigin m == IR.FromSignature
      ]

    -- Collect user assertions (not inherited, not mereological translations).
    userAssertions =
      [ f
      | f <- IR.theoryFacts theory
      , IR.factKind f == IR.FactKindAssertion
      , not (IR.factIsInherited f)
      , not (IR.factIsMereologicalTranslation f)
      ]

    -- Render each assertion, numbering them when there are multiple.
    assertionAxioms = zipWith renderFact [1..] userAssertions

    renderFact :: Int -> IR.Fact -> String
    renderFact idx fact =
      let label = if length userAssertions > 1
                    then "ax" ++ show idx ++ ": "
                    else ""
          body  = renderPropExpr (IR.factPropExpr fact)
      in "axiom " ++ label ++ body ++ " <-> _Top"

-- ---------------------------------------------------------------------------
-- Expression rendering
-- ---------------------------------------------------------------------------

renderPropExpr :: IR.ResolvedPropExpr -> String
renderPropExpr (IR.ResolvedPropBicond lhs rests) =
  case rests of
    [] -> renderRightImpl lhs
    _  ->
      let left  = renderRightImpl lhs
          pairs = [ renderRightImpl (IR.resolvedPropRestRight r) | r <- rests ]
      in foldl (\acc p -> "(" ++ acc ++ " ↔ " ++ p ++ ")") left pairs

renderRightImpl :: IR.ResolvedRightImpl -> String
renderRightImpl (IR.ResolvedRightImpl lhs Nothing) =
  renderLeftImpl lhs
renderRightImpl (IR.ResolvedRightImpl lhs (Just (_, rhs))) =
  "(" ++ renderLeftImpl lhs ++ " → " ++ renderRightImpl rhs ++ ")"

renderLeftImpl :: IR.ResolvedLeftImpl -> String
renderLeftImpl (IR.ResolvedLeftImpl lhs []) =
  renderDisj lhs
renderLeftImpl (IR.ResolvedLeftImpl lhs rests) =
  -- Left-implication chains: A ← B ← C  means  C → B → A  in normal logic.
  -- In the IR these appear as rests with op "←".  We render them right-to-left.
  let base = renderDisj lhs
      steps = map (renderDisj . IR.resolvedLirRight) rests
  in foldl (\acc s -> "(" ++ s ++ " → " ++ acc ++ ")") base steps

renderDisj :: IR.ResolvedDisj -> String
renderDisj (IR.ResolvedDisj lhs []) = renderConj lhs
renderDisj (IR.ResolvedDisj lhs rests) =
  let parts = renderConj lhs : map (renderConj . IR.resolvedDisjRestRight) rests
  in "(" ++ intercalate " ∨ " parts ++ ")"

renderConj :: IR.ResolvedConj -> String
renderConj (IR.ResolvedConj lhs []) = renderNeg lhs
renderConj (IR.ResolvedConj lhs rests) =
  let parts = renderNeg lhs : map (renderNeg . IR.resolvedConjRestRight) rests
  in "(" ++ intercalate " ∧ " parts ++ ")"

renderNeg :: IR.ResolvedNeg -> String
renderNeg (IR.ResolvedNegNot inner) =
  "(" ++ renderNeg inner ++ " → _Bot)"
renderNeg (IR.ResolvedNegChild q) =
  renderQuantified q

renderQuantified :: IR.ResolvedQuantified -> String
renderQuantified (IR.ResolvedQuantified [] atom) =
  renderAtomicProp atom
renderQuantified (IR.ResolvedQuantified qs atom) =
  let quantStr = concatMap renderQuantifier qs
      body      = renderAtomicProp atom
  in quantStr ++ body

renderQuantifier :: IR.ResolvedQuantifier -> String
renderQuantifier (IR.ResolvedQForall vd) =
  "forall " ++ IR.resolvedVarName vd ++ " : Prop, "
renderQuantifier (IR.ResolvedQExists vd) =
  "exists " ++ IR.resolvedVarName vd ++ " : Prop, "

renderAtomicProp :: IR.ResolvedAtomicProp -> String
renderAtomicProp (IR.ResolvedAtomicConstant ref) =
  renderConstantRef ref
renderAtomicProp (IR.ResolvedAtomicTermPair tp) =
  renderTermPair tp

renderConstantRef :: IR.ResolvedConstantRef -> String
renderConstantRef ref =
  let name = IR.resolvedConstRefName ref
  in case name of
       "ℙ#min" -> "_Top"   -- ⊤ = ℙ#min  (smallest element of ℙ = truth)
       "ℙ#max" -> "_Bot"   -- ⊥ = ℙ#max  (largest element of ℙ = falsity)
       _        -> name

-- | Render a term-pair as a propositional formula.
--   In propositional theories the term-pair is essentially a parenthesised
--   sub-expression, so we recurse into it.
renderTermPair :: IR.ResolvedTermPair -> String
renderTermPair (IR.ResolvedTermPair lhs [] _) =
  renderTerm lhs
renderTermPair (IR.ResolvedTermPair lhs rights _) =
  -- Relations after the first term (e.g. equality) — unlikely in pure prop
  -- theories, but handle gracefully.
  let l = renderTerm lhs
      rs = map renderRelationFollowedByTerm rights
  in "(" ++ intercalate " " (l : rs) ++ ")"

renderRelationFollowedByTerm :: IR.ResolvedRelationFollowedByTerm -> String
renderRelationFollowedByTerm rfbt =
  IR.resolvedRFTOp rfbt ++ " " ++ renderTerm (IR.resolvedRFTRight rfbt)

renderTerm :: IR.ResolvedTerm -> String
renderTerm (IR.ResolvedTerm lhs [] _) = renderFactor lhs
renderTerm (IR.ResolvedTerm lhs rests _) =
  let base   = renderFactor lhs
      others = map renderOpFactor rests
  in "(" ++ intercalate " " (base : others) ++ ")"

renderOpFactor :: IR.ResolvedOperationFollowedByFactor -> String
renderOpFactor off =
  IR.resolvedOFFOp off ++ " " ++ renderFactor (IR.resolvedOFFRight off)

renderFactor :: IR.ResolvedFactor -> String
renderFactor (IR.ResolvedFactor base [] _) = renderBaseTerm base
renderFactor (IR.ResolvedFactor base suffixes _) =
  renderBaseTerm base ++ concatMap renderSuffix suffixes

renderSuffix :: IR.ResolvedTermSuffix -> String
renderSuffix (IR.ResolvedSuffixDotAttr attr) = "." ++ attr
renderSuffix (IR.ResolvedSuffixCall args)    =
  "(" ++ intercalate ", " (map renderTerm args) ++ ")"
renderSuffix (IR.ResolvedSuffixSpecialOp op) = op

renderBaseTerm :: IR.ResolvedBaseTerm -> String
renderBaseTerm (IR.ResolvedBTAtomic ref) =
  renderConstantRef ref
renderBaseTerm (IR.ResolvedBTParen expr) =
  "(" ++ renderPropExpr expr ++ ")"
renderBaseTerm (IR.ResolvedBTSingleton t) =
  "{" ++ renderTerm t ++ "}"
renderBaseTerm (IR.ResolvedBTEvaluationInTheory eit) =
  renderPropExpr (IR.resolvedEITOperand eit)
renderBaseTerm (IR.ResolvedBTProjectionToSort pts) =
  renderTerm (IR.resolvedPTOperand pts)
renderBaseTerm (IR.ResolvedBTProjectionToInterval pti) =
  renderTerm (IR.resolvedPTIOperand pti)
renderBaseTerm (IR.ResolvedBTGeneralizedSumOrProduct gsp) =
  -- Generalized sum/product — render body (unusual in propositional theories)
  renderTerm (IR.resolvedGSPOperand gsp)