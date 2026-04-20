{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)
import Data.List (isInfixOf)
import Text.RawString.QQ (r)

import Eidos.Parser (parseString)
import Eidos.FromSyntax (buildTheoryPure)
import Eidos.BuildMonad (mkPureResolver, emptyPureResolver)
import Eidos.Pretty (prettyTheoryDecl)
import Eidos.AST
import qualified Eidos.AST as AST
import Eidos.IR
import qualified Eidos.IR as IR

------------------------------------------------------------
-- Test runner helpers (pure - no IO)
------------------------------------------------------------

-- For tests without external references, use empty resolver
run :: String -> Either String Theory
run input =
  case parseString input of
    Left err -> Left (errorBundlePretty err)
    Right ast ->
      let pureResolver = emptyPureResolver
      in buildTheoryPure pureResolver Nothing ast

runExpectFail :: String -> Either String String
runExpectFail input =
  case parseString input of
    Left err -> Right (errorBundlePretty err)
    Right ast ->
      let pureResolver = emptyPureResolver
      in case buildTheoryPure pureResolver Nothing ast of
        Left err -> Right err
        Right _ -> Left "Expected failure but succeeded"

shouldContainString :: String -> String -> Expectation
shouldContainString actual expected =
  actual `shouldSatisfy` isInfixOf expected

-- Helper to convert Either to SpecM expectation
expectSuccess :: Either String a -> IO ()
expectSuccess (Left err) = fail err
expectSuccess (Right _) = return ()

expectFailure :: Either String String -> (String -> Expectation) -> IO ()
expectFailure e check = case e of
  Left err -> fail ("Expected failure but got success: " ++ err)
  Right errMsg -> check errMsg


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

      it "accepts mereological operations on mereological objects" $
        expectSuccess $ run "{ signature { sort S; x : S; y : S; } axioms { facts { x + y = x; } } }"

      it "rejects mereological operations on sorts" $
        pendingWith "Type checker does not yet reject mereological ops on sorts in FromSyntax"

      it "rejects function application with wrong arity" $
        pendingWith "Unbound variable error fires before arity check; needs declared variables in test"

    --------------------------------------------------------
    -- Level 2: Individuals vs Sets
    --------------------------------------------------------
    describe "Level 2 type checking - Individuals vs Sets" $ do

      it "accepts individual ∈ set" $
        expectSuccess $ run "{ signature { sort S; x : S; mySet ⊆ S; } axioms { facts { x ∈ mySet; } } }"

      it "rejects set ∈ set" $
        expectFailure (runExpectFail "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ∈ set2; } } }")
          (\err -> err `shouldContainString` "Left operand of ∈ must be an individual")

      it "rejects individual ⊆ individual" $
        expectFailure (runExpectFail "{ signature { sort S; x : S; y : S; } axioms { facts { x ⊆ y; } } }")
          (\err -> err `shouldContainString` "Left operand of ⊆ must be a set")

      it "accepts set ⊆ set" $
        expectSuccess $ run "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ⊆ set2; } } }"

      it "accepts set ∪ set" $
        expectSuccess $ run "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ∪ set2 = set1; } } }"

      it "rejects individual ∪ individual" $
        pendingWith "∪ operator type checking not yet enforced in FromSyntax term validation"

      it "accepts set ∩ set" $
        expectSuccess $ run "{ signature { sort S; set1 ⊆ S; set2 ⊆ S; } axioms { facts { set1 ∩ set2 = set1; } } }"

    --------------------------------------------------------
    -- Propositions
    --------------------------------------------------------
    describe "Level 2 type checking - Propositions" $ do

      it "accepts proposition → proposition" $
        expectSuccess $ run "{ signature { P : ℙ; Q : ℙ; } axioms { assertions { P → Q; } } }"

      it "rejects set → proposition" $
        pendingWith "→ operator type checking not yet enforced in FromSyntax expression validation"

      it "rejects proposition → set" $
        pendingWith "→ operator type checking not yet enforced in FromSyntax expression validation"

      it "accepts proposition ∧ proposition" $
        expectSuccess $ run "{ signature { P : ℙ; Q : ℙ; } axioms { assertions { P ∧ Q; } } }"

      it "accepts proposition ∨ proposition" $
        expectSuccess $ run "{ signature { P : ℙ; Q : ℙ; } axioms { assertions { P ∨ Q; } } }"

      it "accepts ¬proposition" $
        expectSuccess $ run "{ signature { P : ℙ; } axioms { assertions { ¬P; } } }"

      it "rejects ¬set" $
        pendingWith "¬ operator type checking not yet enforced in FromSyntax expression validation"

    --------------------------------------------------------
    -- Type conversions
    --------------------------------------------------------
    describe "Type conversions" $ do

      it "accepts individual#set as set" $
        pendingWith "#max resolves to L2BareMereological rather than L2Set; needs fix in sort type resolution"

      it "accepts set#individual as individual" $
        expectSuccess $ run "{ signature { sort S; mySet ⊆ S; } axioms { facts { mySet#individual ∈ mySet; } } }"

      it "accepts individual#proposition as proposition" $
        expectSuccess $ run "{ signature { sort S; x : S; } axioms { assertions { x#proposition → x#proposition; } } }"

      it "accepts proposition#set as set" $
        pendingWith "#max resolves to L2BareMereological rather than L2Set; needs fix in sort type resolution"

    --------------------------------------------------------
    -- Singleton sets
    --------------------------------------------------------
    describe "Singleton sets" $ do

      it "accepts {individual} as set" $
        expectSuccess $ run "{ signature { sort S; x : S; mySet ⊆ S; } axioms { facts { {x} ⊆ mySet; } } }"

      it "rejects {individual} ∈ set" $
        expectFailure (runExpectFail "{ signature { sort S; x : S; mySet ⊆ S; } axioms { facts { {x} ∈ mySet; } } }")
          (\err -> err `shouldContainString` "Left operand of ∈ must be an individual")

    --------------------------------------------------------
    -- Variables
    --------------------------------------------------------
    describe "Variable declarations" $ do

      it "accepts variable with valid sort" $
        expectSuccess $ run "{ signature { sort S; } axioms { assertions { [x:S] x =_S x; } } }"

      it "accepts variable with set declaration" $
        expectSuccess $ run "{ signature { sort S; } axioms { assertions { [x⊆S] x =_S x; } } }"

    --------------------------------------------------------
    -- Quantifiers
    --------------------------------------------------------
    describe "Quantified formulas" $ do

      it "accepts ∀ over individual" $
        expectSuccess $ run "{ signature { sort S; } axioms { assertions { ∀x:S x =_S x; } } }"

      it "accepts ∀ over set" $
        expectSuccess $ run "{ signature { sort S; } axioms { assertions { ∀x⊆S x ⊆ x; } } }"

      it "accepts ∃ over proposition" $
        pendingWith "Proposition-typed quantifier variables not registered in variable context"

    --------------------------------------------------------
    -- Complex
    --------------------------------------------------------
    describe "Complex mixed expressions" $ do

      it "accepts well-typed complex formula" $
        expectSuccess $ run [r|{
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

      it "rejects mixed type comparison" $
        expectFailure (runExpectFail "{ signature { sort S; x : S; mySet ⊆ S; } axioms { assertions { x ⊆ mySet; } } }")
          (\err -> err `shouldContainString` "Left operand of ⊆ must be a set")