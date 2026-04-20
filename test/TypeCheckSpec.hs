-- test/TypeCheckSpec.hs
{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Data.List (isInfixOf)

import Eidos.TypeCheck
import Eidos.IR
import qualified Eidos.IR as IR

main :: IO ()
main = hspec $ do
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

  describe "Binary operation validation" $ do
    let individual = (L2Individual, False)
    let set = (L2Set, False)
    let proposition = (L2Proposition, False)
    let bareAny = (L2BareMereological, True)
    let bareNoAny = (L2BareMereological, False)
    
    describe "∈ operator" $ do
      it "accepts individual ∈ set" $ do
        acceptIndividualOperand individual `shouldBe` True
        acceptSetOperand set `shouldBe` True
      
      it "rejects set ∈ set" $
        acceptIndividualOperand set `shouldBe` False
      
      it "accepts bareAny ∈ set" $ do
        acceptIndividualOperand bareAny `shouldBe` True
        acceptSetOperand set `shouldBe` True
      
      it "accepts individual ∈ bareAny" $ do
        acceptIndividualOperand individual `shouldBe` True
        acceptSetOperand bareAny `shouldBe` True
      
      it "rejects bareNoAny ∈ set" $
        acceptIndividualOperand bareNoAny `shouldBe` False
    
    describe "⊆ operator" $ do
      it "accepts set ⊆ set" $ do
        acceptSetOperand set `shouldBe` True
        acceptSetOperand set `shouldBe` True
      
      it "rejects individual ⊆ individual" $
        acceptSetOperand individual `shouldBe` False
      
      it "accepts bareAny ⊆ set" $ do
        acceptSetOperand bareAny `shouldBe` True
        acceptSetOperand set `shouldBe` True
      
      it "rejects bareNoAny ⊆ set" $
        acceptSetOperand bareNoAny `shouldBe` False
    
    describe "∪ and ∩ operators" $ do
      it "accepts set ∪ set" $ do
        acceptSetOperand set `shouldBe` True
        acceptSetOperand set `shouldBe` True
      
      it "rejects individual ∪ individual" $
        acceptSetOperand individual `shouldBe` False
      
      it "accepts bareAny ∪ set" $ do
        acceptSetOperand bareAny `shouldBe` True
        acceptSetOperand set `shouldBe` True
    
    describe "→, ∧, ∨ operators" $ do
      it "accepts proposition → proposition" $ do
        acceptPropositionOperand proposition `shouldBe` True
        acceptPropositionOperand proposition `shouldBe` True
      
      it "rejects set → proposition" $
        acceptPropositionOperand set `shouldBe` False
      
      it "rejects proposition → set" $
        acceptPropositionOperand set `shouldBe` False
      
      it "accepts bareAny → proposition" $ do
        acceptPropositionOperand bareAny `shouldBe` True
        acceptPropositionOperand proposition `shouldBe` True
    
    describe "¬ operator" $ do
      it "accepts ¬proposition" $
        acceptPropositionOperand proposition `shouldBe` True
      
      it "rejects ¬set" $
        acceptPropositionOperand set `shouldBe` False
      
      it "accepts ¬bareAny" $
        acceptPropositionOperand bareAny `shouldBe` True
      
      it "rejects ¬bareNoAny" $
        acceptPropositionOperand bareNoAny `shouldBe` False

  describe "Edge cases" $ do
    describe "Explicit any propagation" $ do
      it "#mereological creates explicit any" $
        convertLevel2 L2Individual "#mereological" `shouldBe` Just (L2BareMereological, True)
      
      it "converting from bare loses explicit any flag" $
        convertLevel2 L2BareMereological "#set" `shouldBe` Just (L2Set, False)
      
      it "multiple conversions preserve explicit any appropriately" $ do
        let step1 = convertLevel2 L2Individual "#mereological"
        step1 `shouldBe` Just (L2BareMereological, True)
        case step1 of
          Just (ty, _) -> do
            convertLevel2 ty "#set" `shouldBe` Just (L2Set, False)
          Nothing -> fail "Conversion failed"

  describe "checkExpression" $ do
    -- These tests will need mock Entity objects
    -- For now, we'll skip them with a note
    it "needs mock Entity objects to test properly" $
      pendingWith "Will implement when mock entities are available"

  describe "validateOperation" $ do
    it "needs mock Entity objects to test properly" $
      pendingWith "Will implement when mock entities are available"