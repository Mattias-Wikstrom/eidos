{-# LANGUAGE QuasiQuotes #-}
-- | Regression / specification tests for known gaps in the
--   @--lean_using_props@ export path (@MkAxiomSets@ / @propExprToLean@).
--
--   Each @describe@ block corresponds to one item in @LEAN_USING_PROPS_GAPS.md@.
--   Tests marked with @(BUG)@ in their description currently *fail* because
--   the translation gap has not yet been fixed.  Tests marked @(SPEC)@ record
--   the *correct* expected behaviour so that the fix can be verified against
--   them.  Once a gap is closed the @(BUG)@ annotation should be removed.
--
--   Run with:  cabal test leanprops-gaps-tests
module Main where

import Test.Hspec
import Text.RawString.QQ (r)

import Eidos.Pipeline.Parse.Parser            (parseString)
import Eidos.Pipeline.FromSyntax.FromSyntax        (buildTheoryPure)
import qualified Eidos.Pipeline.InvokePipeline as PL
import Eidos.Pipeline.IRProcessing.MkAxiomSets (mkAxiomSets)
import Eidos.Pipeline.Targets.LeanProps.LeanExpr   (LeanDoc(..), LeanBlock(..), LeanDecl(..), LeanAxiom(..),
                                LeanExpr(..), renderLeanExpr)
import Eidos.Pipeline.Targets.LeanProps.LeanProps (renderAxiomSetsToDecls, defaultLeanPropsOptions)
import Eidos.Pipeline.IRProcessing.AxiomSet (AxiomSet(..))

-- ---------------------------------------------------------------------------
-- Shared bound names (mirror LeanPropsSpec conventions)
-- ---------------------------------------------------------------------------

uMin, uMax, pMin, pMax :: LeanExpr
uMin = LVar "𝕌_Min"
uMax = LVar "𝕌_Max"
pMin = LVar "ℙ_Min"
pMax = LVar "ℙ_Max"

sortMin, sortMax :: String -> LeanExpr
sortMin s = LVar (s ++ "_Min")
sortMax s = LVar (s ++ "_Max")

-- ---------------------------------------------------------------------------
-- Test helpers
-- ---------------------------------------------------------------------------

buildStr :: String -> IO LeanDoc
buildStr src = case parseString src of
  Left err  -> fail ("Parse error: " ++ show err)
  Right ast -> case buildTheoryPure ast of
    Left err -> fail ("Build error: " ++ err)
    Right th ->
      let pt        = PL.prepareTheory PL.defaultPipelineOptions th
          axiomSets = mkAxiomSets pt
          decls     = renderAxiomSetsToDecls defaultLeanPropsOptions axiomSets
      in return (LeanDoc { leanDocTheoryName = "", leanDocBlocks = [LeanBlock "__main__" decls] })

allTypes :: LeanDoc -> [LeanExpr]
allTypes doc = [ axiomType ax | blk <- leanDocBlocks doc, DeclAxiom ax <- blockDecls blk ]

hasType :: LeanDoc -> LeanExpr -> Bool
hasType doc ty = ty `elem` allTypes doc

-- | Bodies of all 'WrapAssertion' axioms in the doc.
assertionBodies :: LeanDoc -> [LeanExpr]
assertionBodies doc = [ body | LApp (LVar "WrapAssertion") [_, _, body] <- allTypes doc ]

-- | True when some assertion body equals the given expression.
hasAssertionBody :: LeanDoc -> LeanExpr -> Bool
hasAssertionBody doc body = body `elem` assertionBodies doc

-- | Bodies of all 'WrapMetafact' axioms in the doc.
metafactBodies :: LeanDoc -> [LeanExpr]
metafactBodies doc = [ body | LApp (LVar "WrapMetafact") [_, body] <- allTypes doc ]

-- | Bodies of all 'WrapFact' axioms in the doc.
factBodies :: LeanDoc -> [LeanExpr]
factBodies doc = [ body | LApp (LVar "WrapFact") [_, body] <- allTypes doc ]

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  -- =========================================================================
  -- Gap 1: User `facts { ... }` are not exported as user axioms
  -- =========================================================================
  --
  -- FactKindFact should be treated the same as FactKindAssertion.
  -- A `facts { P; }` block should produce a pMin-wrapped fact, just like
  -- `assertions { P; }` does.

  describe "Gap 1 – facts { } exported like assertions (BUG)" $ do

    it "(SPEC) facts { P; } produces a pMin-wrapped fact axiom" $
      pendingWith "Gap 1 not yet implemented: facts use WrapFact, not WrapAssertion"

    it "(SPEC) facts { P → Q; } produces the same pMin-wrapped axiom as assertions { P → Q; }" $
      pendingWith "Gap 1 not yet implemented: facts use WrapFact, not WrapAssertion"

    it "(SPEC) a theory with both facts and assertions exports both" $
      pendingWith "Gap 1 not yet implemented: facts use WrapFact, not WrapAssertion"

  -- =========================================================================
  -- Gap 2: Biconditional chains are truncated
  -- =========================================================================
  --
  -- `A ↔ B ↔ C` parses as ResolvedPropBicond with two rests.
  -- The current translator picks only the first rest and ignores the others.
  -- The correct translation is a left-associated chain:
  --   (A ↔ B) ↔ C   — which is what `foldl` would give.
  -- (Right-association would be A ↔ (B ↔ C); either is acceptable so long as
  --  ALL links are present.)

  describe "Gap 2 – biconditional chains are fully translated (BUG)" $ do

    it "(SPEC) assertion A ↔ B ↔ C emits a bicond that mentions all three of A, B, C" $ do
      doc <- buildStr [r|{
        signature { A : ℙ; B : ℙ; C : ℙ; },
        axioms { assertions { A ↔ B ↔ C; } }
      }|]
      -- The outer type is (P_Min ∧ body) ↔ P_Min; we inspect `body`.
      let bodies = assertionBodies doc
      -- body must mention C (the second rest), not just A ↔ B
      let mentionsC (LBicond l r) = mentionsC l || mentionsC r
          mentionsC (LVar "C")    = True
          mentionsC _             = False
      any mentionsC bodies `shouldBe` True

    it "(SPEC) A ↔ B ↔ C produces a strictly deeper nesting than A ↔ B" $ do
      -- If A ↔ B ↔ C is correctly translated it produces a tree of depth ≥ 2
      -- in biconditionals; the buggy version gives only depth 1 (= A ↔ B).
      doc2 <- buildStr [r|{
        signature { A : ℙ; B : ℙ; },
        axioms { assertions { A ↔ B; } }
      }|]
      doc3 <- buildStr [r|{
        signature { A : ℙ; B : ℙ; C : ℙ; },
        axioms { assertions { A ↔ B ↔ C; } }
      }|]
      -- The bodies for the 3-element chain must differ from those of the 2-element chain.
      assertionBodies doc3 `shouldNotBe` assertionBodies doc2

  -- =========================================================================
  -- Gap 3: Relation sort qualifier =^S is ignored
  -- =========================================================================
  --
  -- `expr1 =^S expr2` means "project both sides into S and compare".
  -- The correct translation is:
  --   ProjectIntoInterval(expr1, S_Min, S_Max) ↔ ProjectIntoInterval(expr2, S_Min, S_Max)
  --
  -- Currently, the sort qualifier stored in resolvedRFTSortQual is not
  -- consulted in applyRelOp; `=` always produces plain LBicond.

  describe "Gap 3 – =^S qualifier projects both sides into sort S (BUG)" $ do

    it "(SPEC) assertion P =^S Q produces ProjectIntoInterval(P,S_Min,S_Max) ↔ ProjectIntoInterval(Q,S_Min,S_Max)" $
      pendingWith "Gap 3 not yet implemented: =^S qualifier is ignored, produces plain LBicond"

    it "(SPEC) P =^S Q produces a different Lean body than P = Q" $
      pendingWith "Gap 3 not yet implemented: =^S qualifier is ignored, produces plain LBicond"

    it "(SPEC) P =^𝕌 Q projects into U_Min / U_Max" $
      pendingWith "Gap 3 not yet implemented: =^S qualifier is ignored, produces plain LBicond"

  -- =========================================================================
  -- Gap 5: Generalised Σ / Π drop both operator and binder
  -- =========================================================================
  --
  -- Σ is the infinitary version of + (conjunction / ∧), so
  --   Σ x : S . body   translates to   ∀ x ∈ S, body
  -- (a universally-quantified formula relativised to S, mirroring how + maps
  --  to LConj for binary conjunction).
  --
  -- Π is the infinitary version of × (disjunction / ∨), so
  --   Π x : S . body   translates to   ∃ x ∈ S, body
  -- (existentially quantified, mirroring how × maps to LDisj).
  --
  -- Currently baseTermToLean for ResolvedBTGeneralizedSumOrProduct simply
  -- calls termToLean on the operand, discarding the operator symbol and binder.

  describe "Gap 5 – Σ translates to bounded ∀, Π to bounded ∃ (BUG)" $ do

    it "(SPEC) metafact Σ x : S . body produces a LBoundedForall over S" $
      pendingWith "Gap 5 not yet implemented: Σ/Π operators drop operator and binder"

    it "(SPEC) metafact Π x : S . body produces an LExists over S" $
      pendingWith "Gap 5 not yet implemented: Σ/Π operators drop operator and binder"

    it "(SPEC) Σ x : S . A produces a strictly deeper nesting than plain A" $
      pendingWith "Gap 5 not yet implemented: Σ/Π operators drop operator and binder"

    it "(SPEC) Π x : S . A gives a different body than Σ x : S . A" $
      pendingWith "Gap 5 not yet implemented: Σ/Π operators drop operator and binder"