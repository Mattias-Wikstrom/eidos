{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase  #-}
-- | Unit tests for Eidos.Export.LeanProps.
--
-- Tests operate primarily on the 'LeanDoc' internal representation produced
-- by 'theoryToLeanDoc', which is easier to assert on than raw strings.
-- A handful of rendering tests at the end verify 'renderLeanExpr' directly.
--
-- Run with: cabal test leanprops-tests
module Main where

import Test.Hspec
import Text.RawString.QQ (r)
import Data.List (find, nub)

import Eidos.Parser     (parseString)
import Eidos.FromSyntax (buildTheoryPure)
import Eidos.BuildMonad (emptyPureResolver)
import Eidos.Export.LeanProps

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

buildStr :: String -> IO LeanDoc
buildStr src = case parseString src of
  Left err  -> fail ("Parse error: " ++ show err)
  Right ast -> case buildTheoryPure emptyPureResolver Nothing ast of
    Left err -> fail ("Build error: " ++ err)
    Right th -> return (theoryToLeanDoc th)

-- | Collect all axioms from a doc.
axioms :: LeanDoc -> [LeanAxiom]
axioms doc = [ ax | DeclAxiom ax <- leanDocDecls doc ]

-- | Look up an axiom by name.
findAxiom :: LeanDoc -> String -> Maybe LeanAxiom
findAxiom doc n = find (\ax -> axiomName ax == n) (axioms doc)

-- | All axiom names in the doc.
axiomNames :: LeanDoc -> [String]
axiomNames doc = map axiomName (axioms doc)

-- | True when the doc contains an axiom with exactly the given name and type.
hasAxiom :: LeanDoc -> String -> LeanExpr -> Bool
hasAxiom doc n ty = case findAxiom doc n of
  Just ax -> axiomType ax == ty
  Nothing -> False

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  -- =========================================================================
  describe "renderLeanExpr" $ do
  -- =========================================================================

    it "renders LProp" $
      renderLeanExpr LProp `shouldBe` "Prop"

    it "renders LVar" $
      renderLeanExpr (LVar "Foo") `shouldBe` "Foo"

    it "renders LImpl" $
      renderLeanExpr (LImpl (LVar "A") (LVar "B"))
        `shouldBe` "(A → B)"

    it "renders LConj" $
      renderLeanExpr (LConj (LVar "A") (LVar "B"))
        `shouldBe` "(A ∧ B)"

    it "renders LDisj" $
      renderLeanExpr (LDisj (LVar "A") (LVar "B"))
        `shouldBe` "(A ∨ B)"

    it "renders LBicond" $
      renderLeanExpr (LBicond (LVar "A") (LVar "B"))
        `shouldBe` "(A ↔ B)"

    it "renders LForall" $
      renderLeanExpr (LForall "X" (LVar "Prop") (LVar "body"))
        `shouldBe` "∀ X : Prop, body"

    it "renders LExists" $
      renderLeanExpr (LExists "X" (LVar "Prop") (LVar "body"))
        `shouldBe` "∃ X : Prop, body"

    it "renders nested implications" $
      renderLeanExpr (LImpl (LImpl (LVar "A") (LVar "B")) (LVar "C"))
        `shouldBe` "((A → B) → C)"

    it "renders bounded forall with guard" $
      renderLeanExpr
        (LForall "X" (LVar "Prop")
          (LImpl (LConj (LImpl (LVar "P_Max") (LVar "X"))
                        (LImpl (LVar "X") (LVar "P_Min")))
                 (LVar "body")))
        `shouldBe` "∀ X : Prop, (((P_Max → X) ∧ (X → P_Min)) → body)"

  -- =========================================================================
  describe "theoryToLeanDoc – header" $ do
  -- =========================================================================

    it "always includes U_Min, U_Max, P_Min, P_Max, D_Min, D_Max as Prop" $ do
      doc <- buildStr "{ }"
      mapM_ (\n -> hasAxiom doc n LProp `shouldBe` True)
        ["U_Min", "U_Max", "P_Min", "P_Max", "D_Min", "D_Max"]

    it "includes sort ordering axioms in every theory" $ do
      doc <- buildStr "{ }"
      hasAxiom doc "sort_order_1" (LImpl (LVar "U_Max") (LVar "P_Max")) `shouldBe` True
      hasAxiom doc "sort_order_2" (LImpl (LVar "P_Max") (LVar "P_Min")) `shouldBe` True
      hasAxiom doc "sort_order_3" (LImpl (LVar "P_Min") (LVar "U_Min")) `shouldBe` True
      hasAxiom doc "D_sort_order" (LImpl (LVar "D_Max") (LVar "D_Min")) `shouldBe` True

    it "does not duplicate the six built-in bound object names" $ do
      doc <- buildStr "{ }"
      let names = axiomNames doc
          builtins = ["U_Min", "U_Max", "P_Min", "P_Max", "D_Min", "D_Max"]
      mapM_ (\n -> length (filter (== n) names) `shouldBe` 1) builtins

  -- =========================================================================
  describe "theoryToLeanDoc – mereological (𝕌-sorted) objects" $ do
  -- =========================================================================

    it "emits a Prop axiom for each 𝕌-kinded signature object" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; } }|]
      hasAxiom doc "A" LProp `shouldBe` True
      hasAxiom doc "B" LProp `shouldBe` True

    it "emits A_min : A → U_Min for each 𝕌-sorted object" $ do
      doc <- buildStr [r|{ signature { MyObj : 𝕌; } }|]
      hasAxiom doc "MyObj_min" (LImpl (LVar "MyObj") (LVar "U_Min")) `shouldBe` True

    it "emits A_max : U_Max → A for each 𝕌-sorted object" $ do
      doc <- buildStr [r|{ signature { MyObj : 𝕌; } }|]
      hasAxiom doc "MyObj_max" (LImpl (LVar "U_Max") (LVar "MyObj")) `shouldBe` True

    it "does NOT emit a bounds axiom for U_Min itself" $ do
      doc <- buildStr "{ }"
      findAxiom doc "U_Min_min" `shouldBe` Nothing

  -- =========================================================================
  describe "theoryToLeanDoc – propositional (ℙ-sorted) objects" $ do
  -- =========================================================================

    it "emits a Prop axiom for each ℙ-kinded signature object" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; } }|]
      hasAxiom doc "P" LProp `shouldBe` True
      hasAxiom doc "Q" LProp `shouldBe` True

    it "emits P_top : P → P_Min" $ do
      doc <- buildStr [r|{ signature { MyProp : ℙ; } }|]
      hasAxiom doc "MyProp_top" (LImpl (LVar "MyProp") (LVar "P_Min")) `shouldBe` True

    it "emits P_bot : P_Max → P" $ do
      doc <- buildStr [r|{ signature { MyProp : ℙ; } }|]
      hasAxiom doc "MyProp_bot" (LImpl (LVar "P_Max") (LVar "MyProp")) `shouldBe` True

    it "does NOT emit bounds for P_Min or P_Max themselves" $ do
      doc <- buildStr "{ }"
      findAxiom doc "P_Min_top" `shouldBe` Nothing
      findAxiom doc "P_Max_bot" `shouldBe` Nothing

  -- =========================================================================
  describe "theoryToLeanDoc – 𝔻-sorted sets" $ do
  -- =========================================================================

    it "emits a Prop axiom for a 𝔻-sorted set" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasAxiom doc "MySet" LProp `shouldBe` True

    it "emits MySet_top : MySet → D_Min" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasAxiom doc "MySet_top" (LImpl (LVar "MySet") (LVar "D_Min")) `shouldBe` True

    it "emits MySet_bot : D_Max → MySet" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasAxiom doc "MySet_bot" (LImpl (LVar "D_Max") (LVar "MySet")) `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – user-declared sorts" $ do
  -- =========================================================================

    it "emits S_Min and S_Max Prop axioms for a user sort" $ do
      doc <- buildStr [r|{ signature { sort S; } }|]
      hasAxiom doc "S_Min" LProp `shouldBe` True
      hasAxiom doc "S_Max" LProp `shouldBe` True

    it "emits S_sort_order : S_Max → S_Min" $ do
      doc <- buildStr [r|{ signature { sort S; } }|]
      hasAxiom doc "S_sort_order" (LImpl (LVar "S_Max") (LVar "S_Min")) `shouldBe` True

    it "emits bounds for sets inside user sorts" $ do
      doc <- buildStr [r|{ signature { sort S; MySet ⊆ S; } }|]
      hasAxiom doc "MySet_top" (LImpl (LVar "MySet") (LVar "S_Min")) `shouldBe` True
      hasAxiom doc "MySet_bot" (LImpl (LVar "S_Max") (LVar "MySet")) `shouldBe` True

    it "emits limit objects for multiple user sorts independently" $ do
      doc <- buildStr [r|{ signature { sort S; sort T; } }|]
      hasAxiom doc "S_Min" LProp `shouldBe` True
      hasAxiom doc "S_Max" LProp `shouldBe` True
      hasAxiom doc "T_Min" LProp `shouldBe` True
      hasAxiom doc "T_Max" LProp `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – assertions" $ do
  -- =========================================================================

    it "wraps a single assertion with (P_Min ∧ body) ↔ P_Min" $ do
      doc <- buildStr [r|{ signature { P : ℙ; }, axioms { assertions { P; } } }|]
      -- Single fact: no label
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "P_Min") _) (LVar "P_Min"))) -> True
        _ -> False

    it "labels multiple assertions ax1, ax2, ..." $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P; Q; } } }|]
      findAxiom doc "ax1" `shouldSatisfy` \case
        Just (LeanAxiom "ax1" (LBicond (LConj (LVar "P_Min") _) (LVar "P_Min"))) -> True
        _ -> False
      findAxiom doc "ax2" `shouldSatisfy` \case
        Just (LeanAxiom "ax2" (LBicond (LConj (LVar "P_Min") _) (LVar "P_Min"))) -> True
        _ -> False

    it "renders a disjunction assertion P ∨ Q" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P ∨ Q; } } }|]
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "P_Min") (LDisj (LVar "P") (LVar "Q"))) (LVar "P_Min"))) -> True
        _ -> False

    it "renders a negation assertion ¬P as P → P_Max" $ do
      doc <- buildStr [r|{ signature { P : ℙ; }, axioms { assertions { ¬P; } } }|]
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "P_Min") (LImpl (LVar "P") (LVar "P_Max"))) (LVar "P_Min"))) -> True
        _ -> False

    it "renders an implication assertion P → Q" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P → Q; } } }|]
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "P_Min") (LImpl (LVar "P") (LVar "Q"))) (LVar "P_Min"))) -> True
        _ -> False

  -- =========================================================================
  describe "theoryToLeanDoc – metafacts" $ do
  -- =========================================================================

    it "wraps a metafact with (U_Min ∧ body) ↔ U_Min" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A × B; } } }|]
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "U_Min") _) (LVar "U_Min"))) -> True
        _ -> False

    it "renders mereological difference A - B as B → A" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A - B; } } }|]
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "U_Min") (LImpl (LVar "B") (LVar "A"))) (LVar "U_Min"))) -> True
        _ -> False

    it "labels assertions and metafacts with a shared numbering sequence" $ do
      doc <- buildStr [r|{
        signature { P : ℙ; A : 𝕌; },
        axioms {
          assertions { P; },
          metafacts { 𝕌#min - 𝕌#max; }
        }
      }|]
      axiomNames doc `shouldSatisfy` elem "ax1"
      axiomNames doc `shouldSatisfy` elem "ax2"

  -- =========================================================================
  describe "theoryToLeanDoc – universal quantifier in assertions" $ do
  -- =========================================================================

    it "renders [X : ℙ] (X → ¬¬X) with bounded guard" $ do
      doc <- buildStr [r|{
        axioms { assertions { [X : ℙ] (X → ¬¬X); } }
      }|]
      let ax = findAxiom doc ""
      -- The body should contain a forall over Prop with a P-sorted guard
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "P_Min")
                (LForall "X" (LVar "Prop") _)) (LVar "P_Min"))) -> True
        _ -> False

    it "renders [X : 𝕌] (...) with U-sorted guard" $ do
      doc <- buildStr [r|{
        signature { A : 𝕌; },
        axioms { metafacts { [X : 𝕌] (A - (A - X)) - X; } }
      }|]
      let ax = findAxiom doc ""
      ax `shouldSatisfy` \case
        Just (LeanAxiom "" (LBicond (LConj (LVar "U_Min")
                (LForall "X" (LVar "Prop") _)) (LVar "U_Min"))) -> True
        _ -> False

  -- =========================================================================
  describe "theoryToLeanDoc – combined theory sanity check" $ do
  -- =========================================================================

    it "handles a theory with all sorts, sets, props and mereo objects" $ do
      doc <- buildStr [r|{
        signature {
          MySet4 ⊆ 𝔻;
          sort S;
          MySet1 ⊆ S;
          sort T;
          MySet3 ⊆ T;
          A : 𝕌;
          MP1 : 𝕌;
          P1 : ℙ;
          Q : ℙ;
        }
      }|]
      -- Built-ins
      hasAxiom doc "U_Min" LProp `shouldBe` True
      hasAxiom doc "D_Min" LProp `shouldBe` True
      -- User sorts
      hasAxiom doc "S_Min" LProp `shouldBe` True
      hasAxiom doc "T_Min" LProp `shouldBe` True
      -- Mereological
      hasAxiom doc "A" LProp `shouldBe` True
      hasAxiom doc "A_min" (LImpl (LVar "A") (LVar "U_Min")) `shouldBe` True
      -- Propositional
      hasAxiom doc "P1" LProp `shouldBe` True
      hasAxiom doc "P1_top" (LImpl (LVar "P1") (LVar "P_Min")) `shouldBe` True
      -- 𝔻 set
      hasAxiom doc "MySet4_top" (LImpl (LVar "MySet4") (LVar "D_Min")) `shouldBe` True
      -- User-sort set
      hasAxiom doc "MySet1_top" (LImpl (LVar "MySet1") (LVar "S_Min")) `shouldBe` True
      hasAxiom doc "MySet3_top" (LImpl (LVar "MySet3") (LVar "T_Min")) `shouldBe` True

    it "produces no duplicate axiom names" $ do
      doc <- buildStr [r|{
        signature {
          MySet4 ⊆ 𝔻; sort S; MySet1 ⊆ S;
          A : 𝕌; MP1 : 𝕌; P1 : ℙ; Q : ℙ;
        },
        axioms {
          assertions { P1 ∨ Q; },
          metafacts { A × MP1; }
        }
      }|]
      let names = axiomNames doc
      nub names `shouldBe` names