{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)
import Data.List (isInfixOf)
import Text.RawString.QQ (r)

import Eidos.Parser (parseString)
import Eidos.FromSyntax (buildTheory)
import Eidos.Pretty (prettyTheoryDecl)
import Eidos.AST
import qualified Eidos.AST as AST
import Eidos.IR
import qualified Eidos.IR as IR

------------------------------------------------------------
-- Test runner helpers (THIS is the key improvement)
------------------------------------------------------------

run :: String -> IO Theory
run input =
  case parseString input of
    Left err -> fail (errorBundlePretty err)
    Right ast ->
      case buildTheory ast of
        Left err -> fail ("Build failed: " ++ err)
        Right th -> return th

runExpectFail :: String -> IO String
runExpectFail input =
  case parseString input of
    Left err -> return (errorBundlePretty err)
    Right ast ->
      case buildTheory ast of
        Left err -> return err
        Right _  -> fail "Expected failure but succeeded"

shouldContainString :: String -> String -> Expectation
shouldContainString actual expected =
  actual `shouldSatisfy` isInfixOf expected

------------------------------------------------------------
-- Main
------------------------------------------------------------

main :: IO ()
main = hspec $ do

  describe "Type checking" $ do

    --------------------------------------------------------
    -- Level 1
    --------------------------------------------------------
    describe "Level 1 type checking" $ do

      it "accepts mereological operations on mereological objects" $ do
        _ <- run "{ signature { sort S; x : S; y : S; } axioms { facts { x + y = x; } } }"
        return ()

      it "rejects mereological operations on sorts" $ do
        err <- runExpectFail "{ signature { sort S; } axioms { facts { S + S = S; } } }"
        err `shouldContainString` "requires mereological operands"

      it "rejects function application with wrong arity" $ do
        err <- runExpectFail "{ signature { sort S; f : S → S; } axioms { facts { f(x, y) = x; } } }"
        err `shouldContainString` "Argument count mismatch"

    --------------------------------------------------------
    -- Level 2: Individuals vs Sets
    --------------------------------------------------------
    describe "Level 2 type checking - Individuals vs Sets" $ do

      it "accepts individual ∈ set" $ do
        _ <- run "{ signature { sort S; x : S; mySet ⊆ S; } axioms { facts { x ∈ mySet; } } }"
        return ()

      it "rejects set ∈ set" $ do
        err <- runExpectFail "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ∈ set2; } } }"
        err `shouldContainString` "Left operand of ∈ must be an individual"

      it "rejects individual ⊆ individual" $ do
        err <- runExpectFail "{ signature { sort S; x : S; y : S; } axioms { facts { x ⊆ y; } } }"
        err `shouldContainString` "Left operand of ⊆ must be a set"

      it "accepts set ⊆ set" $ do
        _ <- run "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ⊆ set2; } } }"
        return ()

      it "accepts set ∪ set" $ do
        _ <- run "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ∪ set2 = set1; } } }"
        return ()

      it "rejects individual ∪ individual" $ do
        err <- runExpectFail "{ signature { sort S; x : S; y : S; } axioms { facts { x ∪ y = x; } } }"
        err `shouldContainString` "Left operand of ∪ must be a set"

      it "accepts set ∩ set" $ do
        _ <- run "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ∩ set2 = set1; } } }"
        return ()

    --------------------------------------------------------
    -- Propositions
    --------------------------------------------------------
    describe "Level 2 type checking - Propositions" $ do

      it "accepts proposition → proposition" $ do
        _ <- run "{ signature { P : ℙ; Q : ℙ; } axioms { assertions { P → Q; } } }"
        return ()

      it "rejects set → proposition" $ do
        err <- runExpectFail "{ signature { sort S; mySet ⊆ S; Q : ℙ; } axioms { assertions { mySet → Q; } } }"
        err `shouldContainString` "Left operand of → must be a proposition"

      it "rejects proposition → set" $ do
        err <- runExpectFail "{ signature { sort S; P : ℙ; mySet ⊆ S; } axioms { assertions { P → mySet; } } }"
        err `shouldContainString` "Right operand of → must be a proposition"

      it "accepts proposition ∧ proposition" $ do
        _ <- run "{ signature { P : ℙ; Q : ℙ; } axioms { assertions { P ∧ Q; } } }"
        return ()

      it "accepts proposition ∨ proposition" $ do
        _ <- run "{ signature { P : ℙ; Q : ℙ; } axioms { assertions { P ∨ Q; } } }"
        return ()

      it "accepts ¬proposition" $ do
        _ <- run "{ signature { P : ℙ; } axioms { assertions { ¬P; } } }"
        return ()

      it "rejects ¬set" $ do
        err <- runExpectFail "{ signature { sort S; mySet ⊆ S; } axioms { assertions { ¬mySet; } } }"
        err `shouldContainString` "Operand of ¬ must be a proposition"

    --------------------------------------------------------
    -- Type conversions
    --------------------------------------------------------
    describe "Type conversions" $ do

      it "accepts individual#set as set" $ do
        _ <- run "{ signature { sort S; x : S; } axioms { facts { x#set ⊆ S#max; } } }"
        return ()

      it "accepts set#individual as individual" $ do
        _ <- run "{ signature { sort S; mySet ⊆ S; } axioms { facts { mySet#individual ∈ mySet; } } }"
        return ()

      it "accepts individual#proposition as proposition" $ do
        _ <- run "{ signature { sort S; x : S; } axioms { assertions { x#proposition → x#proposition; } } }"
        return ()

      it "accepts proposition#set as set" $ do
        _ <- run "{ signature { P : ℙ; } axioms { facts { P#set ⊆ ℙ#max; } } }"
        return ()

    --------------------------------------------------------
    -- Singleton sets
    --------------------------------------------------------
    describe "Singleton sets" $ do

      it "accepts {individual} as set" $ do
        _ <- run "{ signature { sort S; x : S; mySet ⊆ S; } axioms { facts { {x} ⊆ mySet; } } }"
        return ()

      it "rejects {individual} ∈ set" $ do
        err <- runExpectFail "{ signature { sort S; x : S; mySet ⊆ S; } axioms { facts { {x} ∈ mySet; } } }"
        err `shouldContainString` "Left operand of ∈ must be an individual"

    --------------------------------------------------------
    -- Variables
    --------------------------------------------------------
    describe "Variable declarations" $ do

      it "accepts variable with valid sort" $ do
        _ <- run "{ signature { sort S; } axioms { assertions { [x:S] x =_S x; } } }"
        return ()

      it "accepts variable with set declaration" $ do
        _ <- run "{ signature { sort S; } axioms { assertions { [x⊆S] x =_S x; } } }"
        return ()

    --------------------------------------------------------
    -- Quantifiers
    --------------------------------------------------------
    describe "Quantified formulas" $ do

      it "accepts ∀ over individual" $ do
        _ <- run "{ signature { sort S; } axioms { assertions { ∀x:S x =_S x; } } }"
        return ()

      it "accepts ∀ over set" $ do
        _ <- run "{ signature { sort S; } axioms { assertions { ∀x⊆S x ⊆ x; } } }"
        return ()

      it "accepts ∃ over proposition" $ do
        _ <- run "{ axioms { assertions { ∃X:ℙ X ∨ ¬X; } } }"
        return ()

    --------------------------------------------------------
    -- Complex
    --------------------------------------------------------
    describe "Complex mixed expressions" $ do

      it "accepts well-typed complex formula" $ do
        _ <- run [r|{
          signature { 
            sort S; 
            a : S; 
            b : S; 
            P : ℙ; 
            Q : ℙ; 
            mySet ⊆ S; 
          }
          axioms { 
            assertions { 
              [x:S][y:S] (x ∈ mySet) ∧ (y ∈ mySet) → (x =_S y);
              P ∨ Q → ¬(P ∧ Q);
              (a ∈ mySet) ↔ (b ∈ mySet);
            } 
          } 
        }|]
        return ()

      it "rejects mixed type comparison" $ do
        err <- runExpectFail "{ signature { sort S; x : S; mySet ⊆ S; } axioms { assertions { x ⊆ mySet; } } }"
        err `shouldContainString` "Left operand of ⊆ must be a set"