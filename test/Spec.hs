{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)
import Data.List (isInfixOf)
import Text.RawString.QQ (r)

import Eidos.Parse.Parser (parseString)
import Eidos.FromSyntax (buildTheoryPure)
import Eidos.Resolution.BuildMonad (mkPureResolver, emptyPureResolver)
import Eidos.Print.Pretty (prettyTheoryDecl)
import Eidos.Parse.AST
import qualified Eidos.Parse.AST as AST
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
        expectSuccess $ run "{ signature { sort S; x : S; y : S; }, axioms { facts { x + y = x; } } }"

      it "rejects mereological operations on sorts" $
        pendingWith "Type checker does not yet reject mereological ops on sorts in FromSyntax"

      it "rejects function application with wrong arity" $
        pendingWith "Unbound variable error fires before arity check; needs declared variables in test"

    --------------------------------------------------------
    -- Level 2: Individuals vs Sets
    --------------------------------------------------------
    describe "Level 2 type checking - Individuals vs Sets" $ do

      it "accepts individual ∈ Set" $
        expectSuccess $ run "{ signature { sort S; x : S; MySet ⊆ S; }, axioms { facts { x ∈ MySet; } } }"

      it "rejects Set ∈ Set" $
        expectFailure (runExpectFail "{ signature { sort S; Set1 ⊆ S; Set2 ⊆ S; }, axioms { facts { Set1 ∈ Set2; } } }")
          (\err -> err `shouldContainString` "Left operand of ∈ must be an individual")

      it "rejects individual ⊆ individual" $
        expectFailure (runExpectFail "{ signature { sort S; x : S; y : S; }, axioms { facts { x ⊆ y; } } }")
          (\err -> err `shouldContainString` "Left operand of ⊆ must be a set")

      it "accepts Set ⊆ Set" $
        expectSuccess $ run "{ signature { sort S; Set1 ⊆ S; Set2 ⊆ S; }, axioms { facts { Set1 ⊆ Set2; } } }"

      it "accepts Set ∪ Set" $
        expectSuccess $ run "{ signature { sort S; Set1 ⊆ S; Set2 ⊆ S; }, axioms { facts { Set1 ∪ Set2 = Set1; } } }"

      it "rejects individual ∪ individual" $
        pendingWith "∪ operator type checking not yet enforced in FromSyntax term validation"

      it "accepts Set ∩ Set" $
        expectSuccess $ run "{ signature { sort S; Set1 ⊆ S; Set2 ⊆ S; }, axioms { facts { Set1 ∩ Set2 = Set1; } } }"

    --------------------------------------------------------
    -- Propositions
    --------------------------------------------------------
    describe "Level 2 type checking - Propositions" $ do

      it "accepts proposition → proposition" $
        expectSuccess $ run "{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P → Q; } } }"

      it "rejects set → proposition" $
        pendingWith "→ operator type checking not yet enforced in FromSyntax expression validation"

      it "rejects proposition → set" $
        pendingWith "→ operator type checking not yet enforced in FromSyntax expression validation"

      it "accepts proposition ∧ proposition" $
        expectSuccess $ run "{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P ∧ Q; } } }"

      it "accepts proposition ∨ proposition" $
        expectSuccess $ run "{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P ∨ Q; } } }"

      it "accepts ¬proposition" $
        expectSuccess $ run "{ signature { P : ℙ; }, axioms { assertions { ¬P; } } }"

      it "rejects ¬set" $
        pendingWith "¬ operator type checking not yet enforced in FromSyntax expression validation"

    --------------------------------------------------------
    -- Type conversions
    --------------------------------------------------------
    describe "Type conversions" $ do

      it "accepts individual#set as set" $
        pendingWith "#max resolves to L2BareMereological rather than L2Set; needs fix in sort type resolution"

      it "accepts set#individual as individual" $
        expectSuccess $ run "{ signature { sort S; MySet ⊆ S; }, axioms { facts { MySet#individual ∈ MySet; } } }"

      it "accepts individual#proposition as proposition" $
        expectSuccess $ run "{ signature { sort S; x : S; }, axioms { assertions { x#proposition → x#proposition; } } }"

      it "accepts proposition#set as set" $
        pendingWith "#max resolves to L2BareMereological rather than L2Set; needs fix in sort type resolution"

    --------------------------------------------------------
    -- Singleton sets
    --------------------------------------------------------
    describe "Singleton sets" $ do

      it "accepts {individual} as set" $
        expectSuccess $ run "{ signature { sort S; x : S; MySet ⊆ S; }, axioms { facts { {x} ⊆ MySet; } } }"

      it "rejects {individual} ∈ Set" $
        expectFailure (runExpectFail "{ signature { sort S; x : S; MySet ⊆ S; }, axioms { facts { {x} ∈ MySet; } } }")
          (\err -> err `shouldContainString` "Left operand of ∈ must be an individual")

    --------------------------------------------------------
    -- Signature naming rules
    --------------------------------------------------------
    describe "Signature naming rules" $ do

      it "rejects lowercase bare mereological object in signature" $
        expectFailure (runExpectFail "{ signature { i2 : 𝕌; } }")
          (\err -> err `shouldContainString` "Bare mereological object names must start with uppercase")

      it "accepts uppercase bare mereological object in signature" $
        expectSuccess $ run "{ signature { MyObj : 𝕌; } }"

    --------------------------------------------------------
    -- Variables
    --------------------------------------------------------
    describe "Variable declarations" $ do

      it "accepts variable with valid sort" $
        expectSuccess $ run "{ signature { sort S; }, axioms { assertions { x : S,  x =_S x; } } }"

      it "accepts variable with set declaration" $
        expectSuccess $ run "{ signature { sort S; }, axioms { assertions { X ⊆ S,  X ⊆ X; } } }"

      it "rejects uppercase individual free variable" $
        expectFailure (runExpectFail "{ signature { sort S; }, axioms { assertions { X : S,  X =_S X; } } }")
          (\err -> err `shouldContainString` "Free individual variable must start with lowercase")

      it "rejects lowercase set free variable" $
        expectFailure (runExpectFail "{ signature { sort S; }, axioms { assertions { x ⊆ S,  x ⊆ x; } } }")
          (\err -> err `shouldContainString` "Free set variable must start with uppercase")

    --------------------------------------------------------
    -- Quantifiers
    --------------------------------------------------------
    describe "Quantified formulas" $ do

      it "accepts ∀ over individual" $
        expectSuccess $ run "{ signature { sort S; }, axioms { assertions { ∀x:S x =_S x; } } }"

      it "accepts ∀ over set" $
        expectSuccess $ run "{ signature { sort S; }, axioms { assertions { ∀X⊆S X ⊆ X; } } }"

      it "rejects ∀ with uppercase individual variable" $
        expectFailure (runExpectFail "{ signature { sort S; }, axioms { assertions { ∀X:S X =_S X; } } }")
          (\err -> err `shouldContainString` "Individual variable must start with lowercase")

      it "rejects ∀ with lowercase set variable" $
        expectFailure (runExpectFail "{ signature { sort S; }, axioms { assertions { ∀x⊆S x ⊆ x; } } }")
          (\err -> err `shouldContainString` "Set/relation variable must start with uppercase")

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
            MySet ⊆ S; 
          }, axioms { 
            assertions { 
              x : S, y : S,  (x ∈ MySet) ∧ (y ∈ MySet) → (x =_S y);
              P ∨ Q → ¬(P ∧ Q);
              (a ∈ MySet) ↔ (b ∈ MySet);
            } 
          } 
        }|]

      it "rejects mixed type comparison" $
        expectFailure (runExpectFail "{ signature { sort S; x : S; MySet ⊆ S; }, axioms { assertions { x ⊆ MySet; } } }")
          (\err -> err `shouldContainString` "Left operand of ⊆ must be a set")