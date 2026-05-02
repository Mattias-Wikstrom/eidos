{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)
import Data.List (isInfixOf)
import Text.RawString.QQ (r)

import Eidos.Parser (parseString)
import Eidos.SubLanguage
import Eidos.ExternalRef (TheoryType(..))
import Eidos.AST

------------------------------------------------------------
-- Helpers
------------------------------------------------------------

check :: TheoryType -> String -> Either String ()
check tt input =
  case parseString input of
    Left err   -> Left (errorBundlePretty err)
    Right ast  -> checkTheoryBody [tt] (theoryBody ast)

shouldAccept :: Either String () -> Expectation
shouldAccept (Right ()) = return ()
shouldAccept (Left err) = fail ("Expected success but got error:\n" ++ err)

shouldReject :: String -> Either String () -> Expectation
shouldReject fragment (Left err)
  | fragment `isInfixOf` err = return ()
  | otherwise = fail ("Expected error containing " ++ show fragment
                   ++ "\nbut got:\n" ++ err)
shouldReject fragment (Right ()) =
  fail ("Expected rejection containing " ++ show fragment ++ " but succeeded")

------------------------------------------------------------
-- Main
------------------------------------------------------------

main :: IO ()
main = hspec $ do

  ------------------------------------------------------------
  describe "Equational (.eq) constraints" $ do

    it "accepts equational facts with ∀ and =" $
      shouldAccept $ check EquationalTheory [r|{
        signature { sort S; f : S, S → S; },
        axioms { facts {
          x : S, y : S, z : S,  f(f(x, y), z) = f(x, f(y, z));
        }}
      }|]

    it "rejects assertions section" $
      shouldReject "assertions section" $ check EquationalTheory [r|{
        signature { sort S; },
        axioms { assertions { x : S,  x =_S x; } }
      }|]

    it "rejects metafacts section" $
      shouldReject "metafacts section" $ check EquationalTheory [r|{
        signature { sort S; x : S; },
        axioms { metafacts { x =_S x; } }
      }|]

    it "rejects negation" $
      shouldReject "negation" $ check EquationalTheory [r|{
        signature { sort S; },
        axioms { facts { x : S,  ¬(x =_S x); } }
      }|]

    it "rejects disjunction" $
      shouldReject "disjunction" $ check EquationalTheory [r|{
        signature { sort S; x : S; y : S; },
        axioms { facts { x =_S x ∨ y =_S y; } }
      }|]

    it "rejects existential quantifier" $
      shouldReject "existential" $ check EquationalTheory [r|{
        signature { sort S; },
        axioms { facts { ∃x:S x =_S x; } }
      }|]

    it "rejects SOL function in signature" $
      shouldReject "SOL function" $ check EquationalTheory [r|{
        signature { sort S; F : S → S; },
        axioms { facts { } }
      }|]

    it "rejects ℙ-typed constant in signature" $
      shouldReject "sort ℙ" $ check EquationalTheory [r|{
        signature { P : ℙ; },
        axioms { facts { } }
      }|]

    it "rejects biconditional" $
      shouldReject "biconditional" $ check EquationalTheory [r|{
        signature { sort S; },
        axioms { facts { x : S,  (x =_S x) ↔ (x =_S x); } }
      }|]

  ------------------------------------------------------------
  describe "Regular (.reg) constraints" $ do

    it "accepts regular-logic formula with →" $
      shouldAccept $ check RegularTheory [r|{
        signature { sort S; LessThanOrEq ⊆ S, S; },
        axioms { assertions {
          x : S, y : S, z : S,
            (LessThanOrEq(x, y) ∧ LessThanOrEq(y, z)) → LessThanOrEq(x, z);
        }}
      }|]

    it "accepts ∃ in consequent" $
      shouldAccept $ check RegularTheory [r|{
        signature { sort S; R ⊆ S, S; },
        axioms { assertions {
          x : S,  R(x, x) → ∃y:S R(x, y);
        }}
      }|]

    it "rejects negation" $
      shouldReject "negation" $ check RegularTheory [r|{
        signature { sort S; },
        axioms { assertions { x : S,  ¬(x =_S x); } }
      }|]

    it "rejects disjunction" $
      shouldReject "disjunction" $ check RegularTheory [r|{
        signature { sort S; x : S; y : S; },
        axioms { assertions { x =_S x ∨ y =_S y; } }
      }|]

    it "rejects reverse implication" $
      shouldReject "reverse implication" $ check RegularTheory [r|{
        signature { sort S; x : S; },
        axioms { assertions { x =_S x ← x =_S x; } }
      }|]

    it "rejects SOL function" $
      shouldReject "SOL function" $ check RegularTheory [r|{
        signature { sort S; F : S → S; },
        axioms { assertions { } }
      }|]

  ------------------------------------------------------------
  describe "Coherent (.coh) constraints" $ do

    it "accepts coherent formula with ∃ and ∨" $
      shouldAccept $ check CoherentTheory [r|{
        signature { sort S; R ⊆ S, S; },
        axioms { assertions {
          x : S, y : S,  R(x, y) → (∃z:S R(x, z) ∨ ∃z:S R(z, y));
        }}
      }|]

    it "rejects negation" $
      shouldReject "negation" $ check CoherentTheory [r|{
        signature { sort S; },
        axioms { assertions { x : S,  ¬(x =_S x); } }
      }|]

    it "rejects reverse implication" $
      shouldReject "reverse implication" $ check CoherentTheory [r|{
        signature { sort S; x : S; },
        axioms { assertions { x =_S x ← x =_S x; } }
      }|]

    it "rejects biconditional" $
      shouldReject "biconditional" $ check CoherentTheory [r|{
        signature { sort S; x : S; },
        axioms { assertions { (x =_S x) ↔ (x =_S x); } }
      }|]

    it "rejects SOL function" $
      shouldReject "SOL function" $ check CoherentTheory [r|{
        signature { sort S; F : S → S; },
        axioms { assertions { } }
      }|]

  ------------------------------------------------------------
  describe "FOL (.fol) constraints" $ do

    it "accepts full first-order formula" $
      shouldAccept $ check FOLTheory [r|{
        signature { sort S; },
        axioms { assertions {
          x : S, y : S,  (x =_S y) ∨ ¬(x =_S y);
        }}
      }|]

    it "accepts ∃ in FOL" $
      shouldAccept $ check FOLTheory [r|{
        signature { sort S; },
        axioms { assertions { ∃x:S x =_S x; } }
      }|]

    it "rejects SOL function in signature" $
      shouldReject "SOL function" $ check FOLTheory [r|{
        signature { sort S; F : S → S; },
        axioms { assertions { } }
      }|]

    it "rejects SOL-style set quantifier ∀X⊆S" $
      shouldReject "SOL-style set quantifier" $ check FOLTheory [r|{
        signature { sort S; },
        axioms { assertions { ∀X⊆S X ⊆ X; } }
      }|]

    it "rejects SOL-style free set variable X⊆S" $
      shouldReject "SOL-style free set variable" $ check FOLTheory [r|{
        signature { sort S; },
        axioms { assertions { X ⊆ S,  X ⊆ X; } }
      }|]

  ------------------------------------------------------------
  describe "Propositional (.prop) constraints" $ do

    it "accepts propositional formula" $
      shouldAccept $ check PropositionalTheory [r|{
        signature { P : ℙ; Q : ℙ; },
        axioms { assertions { P → (Q ∧ ¬Q → ⊥); } }
      }|]

    it "rejects sort declaration" $
      shouldReject "Sort declaration" $ check PropositionalTheory [r|{
        signature { sort S; P : ℙ; },
        axioms { assertions { P; } }
      }|]

    it "rejects FOL function" $
      shouldReject "Function" $ check PropositionalTheory [r|{
        signature { f : ℙ → ℙ; },
        axioms { assertions { } }
      }|]

    it "rejects non-ℙ individual" $
      shouldReject "Individual" $ check PropositionalTheory [r|{
        signature { sort S; x : S; },
        axioms { assertions { } }
      }|]

    it "rejects quantifier" $
      shouldReject "quantifiers" $ check PropositionalTheory [r|{
        signature { P : ℙ; },
        axioms { assertions { ∀X:ℙ X → X; } }
      }|]

    it "rejects free variable declaration" $
      shouldReject "free variable declarations" $ check PropositionalTheory [r|{
        signature { P : ℙ; },
        axioms { assertions { X : ℙ,  X → X; } }
      }|]

  ------------------------------------------------------------
  describe "Mereological (.mereo) constraints" $ do

    it "accepts pure signature with sorts and 𝕌 objects" $
      shouldAccept $ check MereologicalTheory [r|{
        signature {
          sort A;
          sort B;
          A subsort B;
          MyObj : 𝕌;
        }
      }|]

    it "rejects any axioms" $
      shouldReject "axioms section" $ check MereologicalTheory [r|{
        signature { sort S; },
        axioms { facts { } }
      }|]

    it "rejects FOL function" $
      shouldReject "Function" $ check MereologicalTheory [r|{
        signature { f : 𝕌 → 𝕌; }
      }|]

    it "rejects set/relation" $
      shouldReject "Set/relation" $ check MereologicalTheory [r|{
        signature { sort S; R ⊆ S, S; }
      }|]

    it "rejects ℙ-typed constant" $
      shouldReject "sort ℙ" $ check MereologicalTheory [r|{
        signature { P : ℙ; }
      }|]

    it "rejects non-𝕌 individual" $
      shouldReject "must have sort 𝕌" $ check MereologicalTheory [r|{
        signature { sort S; x : S; }
      }|]

  ------------------------------------------------------------
  describe "Multiple constraints" $ do

    it "satisfies both .eq and .reg constraints simultaneously" $
      shouldAccept $ check EquationalTheory [r|{
        signature { sort S; f : S → S; },
        axioms { facts { x : S,  f(f(x)) = f(x); } }
      }|]

    it "reports violation of the most restrictive active constraint" $
      -- .eq forbids assertions; report should mention equational restriction
      shouldReject "equational" $
        checkTheoryBody [EquationalTheory, FOLTheory] $ theoryBody $
          case parseString "{ signature { sort S; }, axioms { assertions { x : S,  x =_S x; } } }" of
            Right ast -> ast
            Left _    -> error "parse failed"

    it "rejects disjunction under both .eq and .coh constraints" $
      shouldReject "disjunction" $
        checkTheoryBody [EquationalTheory, CoherentTheory] $ theoryBody $
          case parseString "{ signature { sort S; x : S; y : S; }, axioms { facts { x =_S x ∨ y =_S y; } } }" of
            Right ast -> ast
            Left _    -> error "parse failed"
