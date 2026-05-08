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

import Eidos.Parse.Parser            (parseString)
import Eidos.FromSyntax        (buildTheoryPure)
import Eidos.BuildMonad        (emptyPureResolver)
import Eidos.Backend.LeanProps.LeanExpr   (LeanDoc(..), LeanDecl(..), LeanAxiom(..),
                                LeanExpr(..), renderLeanExpr)
import Eidos.Backend.LeanProps.MkAxiomSets (mkAxiomSets)
import Eidos.Backend.LeanProps.LeanAxiomSet (AxiomSet(..))

-- ---------------------------------------------------------------------------
-- Shared bound names (mirror LeanPropsSpec conventions)
-- ---------------------------------------------------------------------------

uMin, uMax, pMin, pMax :: LeanExpr
uMin = LVar "U_Min"
uMax = LVar "U_Max"
pMin = LVar "P_Min"
pMax = LVar "P_Max"

sortMin, sortMax :: String -> LeanExpr
sortMin s = LVar (s ++ "_Min")
sortMax s = LVar (s ++ "_Max")

-- ---------------------------------------------------------------------------
-- Test helpers
-- ---------------------------------------------------------------------------

buildStr :: String -> IO LeanDoc
buildStr src = case parseString src of
  Left err  -> fail ("Parse error: " ++ show err)
  Right ast -> case buildTheoryPure emptyPureResolver Nothing ast of
    Left err -> fail ("Build error: " ++ err)
    Right th ->
      let axiomSets = mkAxiomSets th
          decls = [ DeclAxiom ax | as <- axiomSets, ax <- asAxioms as ]
      in return (LeanDoc { leanDocTheoryName = "", leanDocDecls = decls })

allTypes :: LeanDoc -> [LeanExpr]
allTypes doc = [ axiomType ax | DeclAxiom ax <- leanDocDecls doc ]

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

    it "(SPEC) facts { P; } produces a pMin-wrapped fact axiom" $ do
      doc <- buildStr [r|{
        signature { P : ℙ; },
        axioms { facts { P; } }
      }|]
      hasAssertionBody doc (LVar "P") `shouldBe` True

    it "(SPEC) facts { P → Q; } produces the same pMin-wrapped axiom as assertions { P → Q; }" $ do
      docFacts <- buildStr [r|{
        signature { P : ℙ; Q : ℙ; },
        axioms { facts { P → Q; } }
      }|]
      docAssertions <- buildStr [r|{
        signature { P : ℙ; Q : ℙ; },
        axioms { assertions { P → Q; } }
      }|]
      -- Facts and assertions should produce the same wrapper node body.
      factBodies docFacts `shouldBe` assertionBodies docAssertions

    it "(SPEC) a theory with both facts and assertions exports both" $ do
      doc <- buildStr [r|{
        signature { P : ℙ; Q : ℙ; },
        axioms {
          assertions { P; },
          facts { Q; }
        }
      }|]
      hasAssertionBody doc (LVar "P") `shouldBe` True
      hasAssertionBody doc (LVar "Q") `shouldBe` True

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

    it "(SPEC) assertion P =^S Q produces ProjectIntoInterval(P,S_Min,S_Max) ↔ ProjectIntoInterval(Q,S_Min,S_Max)" $ do
      doc <- buildStr [r|{
        signature { sort S; P : ℙ; Q : ℙ; },
        axioms { assertions { P =^S Q; } }
      }|]
      let projP = LProjectIntoInterval (LVar "P") (sortMin "S") (sortMax "S")
          projQ = LProjectIntoInterval (LVar "Q") (sortMin "S") (sortMax "S")
      hasAssertionBody doc (LBicond projP projQ) `shouldBe` True

    it "(SPEC) P =^S Q produces a different Lean body than P = Q" $ do
      docQual  <- buildStr [r|{
        signature { sort S; P : ℙ; Q : ℙ; },
        axioms { assertions { P =^S Q; } }
      }|]
      docPlain <- buildStr [r|{
        signature { sort S; P : ℙ; Q : ℙ; },
        axioms { assertions { P = Q; } }
      }|]
      assertionBodies docQual `shouldNotBe` assertionBodies docPlain

    it "(SPEC) P =^𝕌 Q projects into U_Min / U_Max" $ do
      doc <- buildStr [r|{
        signature { P : ℙ; Q : ℙ; },
        axioms { assertions { P =^𝕌 Q; } }
      }|]
      let projP = LProjectIntoInterval (LVar "P") uMin uMax
          projQ = LProjectIntoInterval (LVar "Q") uMin uMax
      hasAssertionBody doc (LBicond projP projQ) `shouldBe` True

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

    it "(SPEC) metafact Σ x : S . body produces a LBoundedForall over S" $ do
      -- Σ x : S . A   should yield a bounded-forall body, not just A.
      doc <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { Σx : S(A); } }
      }|]
      let bodies = metafactBodies doc
      let isBoundedForall (LBoundedForall _ "S_Min" "S_Max" _) = True
          isBoundedForall _                                      = False
      any isBoundedForall bodies `shouldBe` True

    it "(SPEC) metafact Π x : S . body produces an LExists over S" $ do
      doc <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { Πx : S(A); } }
      }|]
      let bodies = metafactBodies doc
      let isExists (LExists _ _ _) = True
          isExists _                = False
      any isExists bodies `shouldBe` True

    it "(SPEC) Σ x : S . A produces a strictly deeper nesting than plain A" $ do
      docSigma <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { Σx : S(A); } }
      }|]
      docPlain <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { A; } }
      }|]
      -- After the fix the Sigma body is wrapped in a forall; currently both
      -- give the same flat LVar "A".
      metafactBodies docSigma `shouldNotBe` metafactBodies docPlain

    it "(SPEC) Π x : S . A gives a different body than Σ x : S . A" $ do
      docSigma <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { Σx : S(A); } }
      }|]
      docPi    <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { Πx : S(A); } }
      }|]
      metafactBodies docSigma `shouldNotBe` metafactBodies docPi