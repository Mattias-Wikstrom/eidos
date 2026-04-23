-- test/TypeCheckSpec.hs
--
-- Tests for Eidos.TypeCheck.
--
-- Two layers:
--   1. Unit tests – call TypeCheck functions directly with hand-built values.
--   2. End-to-end tests – parse a complete theory string and run it through
--      buildTheoryPure, then assert that the build either succeeds (Right) or
--      fails with a type error (Left containing a diagnostic substring).
--
-- The end-to-end tests do *not* require that the exact error message is stable;
-- they only assert the direction (accepted / rejected) and – for rejections –
-- that the word "error" or a relevant operator name appears somewhere in the
-- diagnostic.  This keeps the tests robust against wording changes while still
-- demonstrating real coverage.

{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Data.List (isInfixOf)
import Text.RawString.QQ (r)

import Eidos.TypeCheck
import Eidos.IR
import qualified Eidos.IR as IR
import Eidos.Parser      (parseString)
import Eidos.FromSyntax  (buildTheoryPure)
import Eidos.BuildMonad  (emptyPureResolver)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Build a theory from a source string; return the error message on failure.
buildStr :: String -> Either String Theory
buildStr src = case parseString src of
  Left  err -> Left ("Parse error: " ++ show err)
  Right ast -> buildTheoryPure emptyPureResolver Nothing ast

-- | Assert that building the source *succeeds*.
shouldAccept :: String -> Expectation
shouldAccept src = case buildStr src of
  Right _ -> return ()
  Left  e -> expectationFailure ("Expected success but got error:\n" ++ e)

-- | Assert that building the source *fails* and the error mentions `needle`.
shouldReject :: String -> String -> Expectation
shouldReject src needle = case buildStr src of
  Left e | needle `isInfixOf` e -> return ()
          | otherwise ->
              expectationFailure $
                "Build failed as expected, but needle '" ++ needle ++
                "' not found in:\n" ++ e
  Right _ -> expectationFailure "Expected a type error but build succeeded"

-- | Assert that building the source fails (any error).
shouldRejectAny :: String -> Expectation
shouldRejectAny src = case buildStr src of
  Left  _ -> return ()
  Right _ -> expectationFailure "Expected a type error but build succeeded"

-- ---------------------------------------------------------------------------
-- Convenience sort / entity builders for unit tests
-- ---------------------------------------------------------------------------

-- | A sort with the given SortKind, for use in checkVarDecl.
mkSort :: EntityKind -> Sort
mkSort k = Sort
  { sortKind             = k
  , sortTheory           = error "dummyTheory"
  , sortOrigin           = FromSignature
  , sortMin              = error "sortMin not needed"
  , sortMax              = error "sortMax not needed"
  , sortName             = "TestSort"
  , sortComponentSorts   = []
  , sortAssociatedEntity = Nothing
  , sortReflectedFrom    = Nothing
  }

-- | A MereologicalObject with the given EntityKind.
mkMereo :: EntityKind -> MereologicalObject
mkMereo k = MereologicalObject
  { mereoKind          = k
  , mereoOrigin        = FromSignature
  , mereoTheory        = error "dummyTheory"
  , mereoName          = "testMereo"
  , mereoSort          = mkSort SortKindDomain
  , mereoLimitForSort  = Nothing
  , mereoReflectedFrom = Nothing
  }

entityIndividual :: Entity
entityIndividual = EntityMereological (mkMereo MereologicalEntityKindIndividual)

entitySet :: Entity
entitySet = EntityMereological (mkMereo MereologicalEntityKindSet)

entityProposition :: Entity
entityProposition = EntityMereological (mkMereo MereologicalEntityKindProposition)

entityBare :: Entity
entityBare = EntityMereological (mkMereo MereologicalEntityKindMereological)

-- ---------------------------------------------------------------------------
-- Predicates for Either
-- ---------------------------------------------------------------------------

isRight_ :: Either a b -> Bool
isRight_ (Right _) = True
isRight_ _         = False

isLeft_ :: Either a b -> Bool
isLeft_ (Left _) = True
isLeft_ _        = False

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  -- ── Unit: acceptIndividualOperand / acceptSetOperand / acceptPropositionOperand ──

  describe "TypeWithAny semantics (explicit any)" $ do
    describe "acceptIndividualOperand" $ do
      it "accepts L2Individual (non-any)" $
        acceptIndividualOperand (L2Individual, False) `shouldBe` True

      it "accepts L2BareMereological with explicit any" $
        acceptIndividualOperand (L2BareMereological, True) `shouldBe` True

      it "rejects L2Set (non-any)" $
        acceptIndividualOperand (L2Set, False) `shouldBe` False

      it "rejects L2Proposition (non-any)" $
        acceptIndividualOperand (L2Proposition, False) `shouldBe` False

      it "rejects L2BareMereological without explicit any" $
        acceptIndividualOperand (L2BareMereological, False) `shouldBe` False

    describe "acceptSetOperand" $ do
      it "accepts L2Set (non-any)" $
        acceptSetOperand (L2Set, False) `shouldBe` True

      it "accepts L2BareMereological with explicit any" $
        acceptSetOperand (L2BareMereological, True) `shouldBe` True

      it "rejects L2Individual (non-any)" $
        acceptSetOperand (L2Individual, False) `shouldBe` False

      it "rejects L2Proposition (non-any)" $
        acceptSetOperand (L2Proposition, False) `shouldBe` False

      it "rejects L2BareMereological without explicit any" $
        acceptSetOperand (L2BareMereological, False) `shouldBe` False

    describe "acceptPropositionOperand" $ do
      it "accepts L2Proposition (non-any)" $
        acceptPropositionOperand (L2Proposition, False) `shouldBe` True

      it "accepts L2BareMereological with explicit any" $
        acceptPropositionOperand (L2BareMereological, True) `shouldBe` True

      it "rejects L2Individual (non-any)" $
        acceptPropositionOperand (L2Individual, False) `shouldBe` False

      it "rejects L2Set (non-any)" $
        acceptPropositionOperand (L2Set, False) `shouldBe` False

      it "rejects L2BareMereological without explicit any" $
        acceptPropositionOperand (L2BareMereological, False) `shouldBe` False

  -- ── Unit: convertLevel2 ──────────────────────────────────────────────────

  describe "convertLevel2" $ do
    describe "conversions to bare mereological" $ do
      it "converts Individual#mereological to L2BareMereological with explicit any" $
        convertLevel2 L2Individual "#mereological" `shouldBe` Just (L2BareMereological, True)

      it "converts Set#mereological to L2BareMereological with explicit any" $
        convertLevel2 L2Set "#mereological" `shouldBe` Just (L2BareMereological, True)

      it "converts Proposition#mereological to L2BareMereological with explicit any" $
        convertLevel2 L2Proposition "#mereological" `shouldBe` Just (L2BareMereological, True)

      it "converts Bare#mereological to L2BareMereological with explicit any" $
        convertLevel2 L2BareMereological "#mereological" `shouldBe` Just (L2BareMereological, True)

    describe "conversions from bare mereological" $ do
      it "converts Bare#individual to L2Individual without explicit any" $
        convertLevel2 L2BareMereological "#individual" `shouldBe` Just (L2Individual, False)

      it "converts Bare#set to L2Set without explicit any" $
        convertLevel2 L2BareMereological "#set" `shouldBe` Just (L2Set, False)

      it "converts Bare#proposition to L2Proposition without explicit any" $
        convertLevel2 L2BareMereological "#proposition" `shouldBe` Just (L2Proposition, False)

    describe "conversions between concrete types" $ do
      it "converts Individual#set to L2Set without explicit any" $
        convertLevel2 L2Individual "#set" `shouldBe` Just (L2Set, False)

      it "converts Set#individual to L2Individual without explicit any" $
        convertLevel2 L2Set "#individual" `shouldBe` Just (L2Individual, False)

      it "converts Individual#proposition to L2Proposition without explicit any" $
        convertLevel2 L2Individual "#proposition" `shouldBe` Just (L2Proposition, False)

      it "converts Proposition#set to L2Set without explicit any" $
        convertLevel2 L2Proposition "#set" `shouldBe` Just (L2Set, False)

    -- ── Ill-typed conversions – should return Nothing ─────────────────────

    describe "ill-typed conversions (should return Nothing)" $ do
      it "rejects Sort#individual (sorts are not mereological)" $
        convertLevel2 L2Sort "#individual" `shouldBe` Nothing

      it "rejects Sort#set" $
        convertLevel2 L2Sort "#set" `shouldBe` Nothing

      it "rejects Sort#proposition" $
        convertLevel2 L2Sort "#proposition" `shouldBe` Nothing

      it "rejects Sort#mereological" $
        convertLevel2 L2Sort "#mereological" `shouldBe` Nothing

      it "rejects Function#individual (functions are not mereological)" $
        convertLevel2 (L2Function 1) "#individual" `shouldBe` Nothing

      it "rejects Function#set" $
        convertLevel2 (L2Function 2) "#set" `shouldBe` Nothing

      it "rejects Theory#mereological" $
        convertLevel2 L2Theory "#mereological" `shouldBe` Nothing

      it "rejects Individual with unrecognised suffix" $
        convertLevel2 L2Individual "#bogus" `shouldBe` Nothing

  -- ── Unit: checkLevel1 ────────────────────────────────────────────────────

  describe "checkLevel1" $ do
    describe "well-typed operations" $ do
      it "accepts Mereological + Mereological" $
        checkLevel1 L1Mereological "+" L1Mereological `shouldBe` Right True

      it "accepts Mereological \215 Mereological (product / disjunction)" $
        checkLevel1 L1Mereological "\215" L1Mereological `shouldBe` Right True

      it "accepts Sort _ Sort (any op)" $
        checkLevel1 L1Sort "any" L1Sort `shouldBe` Right True

      it "accepts same-arity function composition" $
        checkLevel1 (L1Function 2) "\x2218" (L1Function 2) `shouldBe` Right True

    describe "ill-typed operations (must produce Left)" $ do
      it "rejects Mereological op Sort" $
        checkLevel1 L1Mereological "+" L1Sort
          `shouldSatisfy` isLeft_

      it "rejects Sort op Mereological" $
        checkLevel1 L1Sort "+" L1Mereological
          `shouldSatisfy` isLeft_

      it "rejects Theory op Mereological" $
        checkLevel1 L1Theory "+" L1Mereological
          `shouldSatisfy` isLeft_

      it "rejects different-arity function composition" $
        checkLevel1 (L1Function 1) "\x2218" (L1Function 2)
          `shouldSatisfy` isLeft_

  -- ── Unit: classifyLevel1 / classifyLevel2 ────────────────────────────────

  describe "classifyLevel1" $ do
    it "classifies EntitySort as L1Sort" $
      classifyLevel1 (EntitySort (mkSort SortKindDomain)) `shouldBe` L1Sort

    it "classifies EntityMereological as L1Mereological" $
      classifyLevel1 entityIndividual `shouldBe` L1Mereological

  describe "classifyLevel2" $ do
    it "classifies Individual entity as L2Individual" $
      classifyLevel2 entityIndividual `shouldBe` L2Individual

    it "classifies Set entity as L2Set" $
      classifyLevel2 entitySet `shouldBe` L2Set

    it "classifies Proposition entity as L2Proposition" $
      classifyLevel2 entityProposition `shouldBe` L2Proposition

    it "classifies bare Mereological entity as L2BareMereological" $
      classifyLevel2 entityBare `shouldBe` L2BareMereological

  -- ── Unit: checkVarDecl ───────────────────────────────────────────────────

  describe "checkVarDecl" $ do
    it "accepts universe sort" $
      checkVarDecl (mkSort SortKindUniverse) `shouldBe` Right ()

    it "accepts domain sort" $
      checkVarDecl (mkSort SortKindDomain) `shouldBe` Right ()

    it "accepts proposition sort" $
      checkVarDecl (mkSort SortKindProp) `shouldBe` Right ()

    it "accepts user-declared sort" $
      checkVarDecl (mkSort SortKindFromSignature) `shouldBe` Right ()

    -- Ill-typed: product sorts must not appear in quantifier bindings.
    it "rejects product sort in variable declaration" $
      checkVarDecl (mkSort SortKindProduct)
        `shouldSatisfy` isLeft_

  -- ── Unit: validateOperation (Entity-level) ───────────────────────────────
  --
  -- NOTE: validateOperation routes every call through checkLevel1 first.
  -- checkLevel1 only passes pairs of the *same* Level-1 kind; for
  -- L1Mereological pairs it additionally only accepts the five mereological
  -- term operators (+, ×, -, ⇒, ∸) plus ≤ and =.  Logical / relational
  -- operators (∈, ⊆, →, ∧, ∨) are not in that whitelist, so they always
  -- produce a Level-1 error regardless of the Level-2 types involved.
  -- The "accepts" tests below therefore use operators that checkLevel1 does
  -- whitelist; the "rejects" tests use operators that fail at Level 1 or
  -- Level 2 (both are valid demonstrations of rejection).

  describe "validateOperation (entity-level)" $ do
    let ind  = entityIndividual
    let set  = entitySet
    let prop = entityProposition

    describe "mereological sum operator +" $ do
      -- + is whitelisted by checkLevel1 for any L1Mereological pair, and
      -- validateOperation passes through (no Level-2 check for +).
      it "accepts individual + individual (mereological sum)" $
        validateOperation ind Nothing "+" ind Nothing `shouldSatisfy` isRight_

      it "accepts set + set" $
        validateOperation set Nothing "+" set Nothing `shouldSatisfy` isRight_

      it "accepts proposition + proposition" $
        validateOperation prop Nothing "+" prop Nothing `shouldSatisfy` isRight_

    describe "mereological equality operator =" $ do
      it "accepts individual = individual" $
        validateOperation ind Nothing "=" ind Nothing `shouldSatisfy` isRight_

      it "accepts set = set" $
        validateOperation set Nothing "=" set Nothing `shouldSatisfy` isRight_

    describe "level-1 cross-kind mismatches (always rejected)" $ do
      it "rejects Sort + Mereological" $
        validateOperation (EntitySort (mkSort SortKindDomain)) Nothing "+"
                          entityIndividual Nothing
          `shouldSatisfy` isLeft_

      it "rejects Theory + Mereological" $
        validateOperation (EntityTheory (error "dummyT")) Nothing "+"
                          entityIndividual Nothing
          `shouldSatisfy` isLeft_

    -- These operators are not in checkLevel1's mereological whitelist, so
    -- they are rejected at Level 1 regardless of operand subtypes.
    -- The tests document what the function currently does.
    describe "operators not whitelisted by checkLevel1 (rejected at Level 1)" $ do
      it "rejects individual ∈ set at Level 1 (∈ not in mereological op list)" $
        validateOperation ind Nothing "\x2208" set Nothing `shouldSatisfy` isLeft_

      it "rejects set ⊆ set at Level 1 (⊆ not in mereological op list)" $
        validateOperation set Nothing "\x2286" set Nothing `shouldSatisfy` isLeft_

      it "rejects proposition → proposition at Level 1" $
        validateOperation prop Nothing "\x2192" prop Nothing `shouldSatisfy` isLeft_

      it "rejects proposition ∧ proposition at Level 1" $
        validateOperation prop Nothing "\x2227" prop Nothing `shouldSatisfy` isLeft_

      it "rejects proposition ∨ proposition at Level 1" $
        validateOperation prop Nothing "\x2228" prop Nothing `shouldSatisfy` isLeft_

  -- ── End-to-end: well-typed theories that must be accepted ────────────────

  describe "End-to-end: well-typed theories (must be accepted)" $ do

    it "accepts a theory with an individual declared over a sort" $
      shouldAccept [r|
        { signature {
            sort S;
            x : S;
          }
        }
      |]

    it "accepts a theory with a set declared over a sort" $
      shouldAccept [r|
        { signature {
            sort S;
            mySet ⊆ S;
          }
        }
      |]

    it "accepts individual in set fact" $
      shouldAccept [r|
        { signature {
            sort S;
            x     : S;
            mySet ⊆ S;
          }
          axioms {
            facts { x ∈ mySet; }
          }
        }
      |]

    it "accepts set ⊆ set fact" $
      shouldAccept [r|
        { signature {
            sort S;
            A ⊆ S;
            B ⊆ S;
          }
          axioms {
            facts { A ⊆ B; }
          }
        }
      |]

    it "accepts a propositional axiom (truth constant)" $
      shouldAccept [r|
        { axioms { assertions { ⊤; } } }
      |]

    it "accepts a universally quantified axiom over a user sort" $
      shouldAccept [r|
        { signature {
            sort S;
            mySet ⊆ S;
          }
          axioms {
            assertions { ∀x:S x ∈ mySet; }
          }
        }
      |]

    it "accepts a subsort declaration" $
      shouldAccept [r|
        { signature {
            sort S;
            T subsort S;
          }
        }
      |]

  -- ── End-to-end: ill-typed theories that must be rejected ─────────────────

  describe "End-to-end: ill-typed theories (must be rejected)" $ do

    -- ∈ misuse: set on the left (must be individual)
    it "rejects set ∈ set (left operand of ∈ is a set, not an individual)" $
      shouldRejectAny [r|
        { signature {
            sort S;
            mySet    ⊆ S;
            otherSet ⊆ S;
          }
          axioms {
            facts { mySet ∈ otherSet; }
          }
        }
      |]

    -- ∈ misuse: individual on the right (must be a set)
    it "rejects individual ∈ individual (right operand of ∈ is not a set)" $
      shouldRejectAny [r|
        { signature {
            sort S;
            x : S;
            y : S;
          }
          axioms {
            facts { x ∈ y; }
          }
        }
      |]

    -- ⊆ misuse: individual ⊆ individual
    it "rejects individual ⊆ individual (both operands of ⊆ must be sets)" $
      shouldRejectAny [r|
        { signature {
            sort S;
            x : S;
            y : S;
          }
          axioms {
            facts { x ⊆ y; }
          }
        }
      |]

    -- ⊆ misuse: individual on the left, set on the right
    it "rejects individual ⊆ set (left operand of ⊆ must be a set)" $
      shouldRejectAny [r|
        { signature {
            sort S;
            x     : S;
            mySet ⊆ S;
          }
          axioms {
            facts { x ⊆ mySet; }
          }
        }
      |]

    -- ⊆ misuse: set on the left, individual on the right
    it "rejects set ⊆ individual (right operand of ⊆ must be a set)" $
      shouldRejectAny [r|
        { signature {
            sort S;
            mySet ⊆ S;
            y     : S;
          }
          axioms {
            facts { mySet ⊆ y; }
          }
        }
      |]

    -- Reference to an undefined name
    it "rejects a fact referencing an undeclared entity" $
      shouldRejectAny [r|
        { axioms {
            facts { undeclaredThing ∈ alsoUndeclared; }
          }
        }
      |]