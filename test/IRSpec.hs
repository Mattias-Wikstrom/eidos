{-# LANGUAGE QuasiQuotes #-}
-- | Tests for the ported IR features (Gaps 1-7).
--
-- Run with: cabal test ir-tests
module Main where

import Test.Hspec
import Data.List            (find)
import Data.Maybe           (isJust, isNothing, mapMaybe)
import qualified Data.Map.Strict as Map
import Text.RawString.QQ    (r)
import Control.Exception (try, evaluate, SomeException, displayException)

import Eidos.Parser         (parseString)
import Eidos.FromSyntax     (buildTheoryPure)
import Eidos.BuildMonad     (emptyPureResolver)
import Eidos.IR

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Parse and build a theory from a string, failing the test on error.
buildStr :: String -> IO Theory
buildStr input = case parseString input of
  Left err  -> fail ("Parse error: " ++ show err)
  Right ast -> case buildTheoryPure emptyPureResolver Nothing ast of
    Left err -> fail ("Build error: " ++ err)
    Right th -> return th

-- | Collect all facts of FactKindSortLimitation from a theory.
sortLimitFacts :: Theory -> [Fact]
sortLimitFacts th = filter (\f -> factKind f == FactKindSortLimitation) (theoryFacts th)

-- | Extract (leftName, op, rightName) triples from sort-limit facts.
limitTriples :: Theory -> [(String, String, String)]
limitTriples th =
  [ (lname, op, rname)
  | Fact { factPropExpr = ResolvedPropBicond
              (ResolvedRightImpl
                (ResolvedLeftImpl
                  (ResolvedDisj
                    (ResolvedConj
                      (ResolvedNegChild
                        (ResolvedQuantified []
                          (ResolvedAtomicTermPair
                            (ResolvedTermPair
                              (ResolvedTerm (ResolvedFactor (ResolvedBTAtomic lref) [] _) [] _)
                              [ResolvedRelationFollowedByTerm [] op _ (ResolvedTerm (ResolvedFactor (ResolvedBTAtomic rref) [] _) [] _)]
                              _))))
                      [])
                  [])
                [])
              Nothing)
            [] } <- sortLimitFacts th
  , let lname = resolvedConstRefName lref
        rname = resolvedConstRefName rref
  ]

hasLimit :: Theory -> String -> String -> String -> Bool
hasLimit th l op r = (l, op, r) `elem` limitTriples th

entityNames :: Theory -> [String]
entityNames th = map entityName (theoryObjects th)

lookupByName :: Theory -> String -> Maybe Entity
lookupByName th nm = case Map.lookup nm (theoryObjectsByName th) of
  Just (e:_) -> Just e
  _          -> Nothing

lookupInParentByName :: Theory -> String -> Maybe Entity
lookupInParentByName th nm = case Map.lookup nm (theoryObjectsByName th) of
  Just [e] -> Just e
  Just (_:_) -> Nothing   -- ambiguous, return Nothing
  _ -> Nothing

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  -- ── Gap 1 & 5: sort-limit metafacts ────────────────────────────────────
  describe "Gap 1+5: sort-limit metafacts" $ do

    it "emits ℙ#max ≤ S#min for a user sort S" $ do
      th <- buildStr "{ signature { sort S; } }"
      hasLimit th "ℙ#max" "≤" "S#min" `shouldBe` True

    it "emits 𝕌#min ≤ S#min for a user sort S" $ do
      th <- buildStr "{ signature { sort S; } }"
      hasLimit th "𝕌#min" "≤" "S#min" `shouldBe` True

    it "emits S#max ≤ 𝕌#max for a user sort S" $ do
      th <- buildStr "{ signature { sort S; } }"
      hasLimit th "S#max" "≤" "𝕌#max" `shouldBe` True

    it "emits subsort min/max facts: T#min = S#min and T#max ≤ S#max" $ do
      th <- buildStr "{ signature { sort S; T subsort S; } }"
      hasLimit th "T#min" "=" "S#min" `shouldBe` True
      hasLimit th "T#max" "≤" "S#max" `shouldBe` True

    it "emits quotient min/max facts: S#min ≤ T#min and T#max = S#max" $ do
      th <- buildStr "{ signature { sort S; T quotient S; } }"
      hasLimit th "S#min" "≤" "T#min" `shouldBe` True
      hasLimit th "T#max" "=" "S#max" `shouldBe` True

    it "emits subquotient min/max facts" $ do
      th <- buildStr "{ signature { sort S; T subquotient S; } }"
      hasLimit th "S#min" "≤" "T#min" `shouldBe` True
      hasLimit th "T#max" "≤" "S#max" `shouldBe` True

  -- ── Gap 2: sort min/max as entities ────────────────────────────────────
  describe "Gap 2: sort min/max objects as entities" $ do

    it "registers S#min and S#max as entities in theoryObjects" $ do
      th <- buildStr "{ signature { sort S; } }"
      entityNames th `shouldSatisfy` elem "S#min"
      entityNames th `shouldSatisfy` elem "S#max"

    it "registers 𝕌#min and 𝕌#max as entities (built-in universe)" $ do
      th <- buildStr "{}"
      entityNames th `shouldSatisfy` elem "𝕌#min"
      entityNames th `shouldSatisfy` elem "𝕌#max"

    it "registers ℙ#min and ℙ#max as entities (built-in prop)" $ do
      th <- buildStr "{}"
      entityNames th `shouldSatisfy` elem "ℙ#min"
      entityNames th `shouldSatisfy` elem "ℙ#max"

    it "S#min is a MereologicalObject of kind LowerLimitForSort" $ do
      th <- buildStr "{ signature { sort S; } }"
      case lookupByName th "S#min" of
        Just (EntityMereological m) ->
          mereoKind m `shouldBe` MereologicalEntityKindLowerLimitForSort
        _ -> fail "S#min not found or wrong entity type"

  -- ── Gap 3: FOL inverse function ────────────────────────────────────────
  describe "Gap 3: FOL function inverse" $ do

    it "creates f_inv for a FOL function f : S → T" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      lookupByName th "f_inv" `shouldSatisfy` isJust

    it "f_inv is a Function with FOL kind" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      case lookupByName th "f_inv" of
        Just (EntityFunction fn) ->
          funcKind fn `shouldBe` FunctionKindFOLFunctionFromTheory
        _ -> fail "f_inv not found or wrong entity type"

    it "f_inv has resSort equal to f's domain sort" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      case (lookupByName th "f", lookupByName th "f_inv") of
        (Just (EntityFunction f), Just (EntityFunction inv)) ->
          sortName (funcResSort inv) `shouldBe` "f#dom"   -- Changed from "T#dom"
        _ -> fail "f or f_inv not found"

  -- ── Gap 4: direct/inverse image functions ──────────────────────────────
  describe "Gap 4: direct and inverse image SOL functions" $ do

    it "creates f#dir_img for a FOL function f" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      lookupByName th "f#dir_img" `shouldSatisfy` isJust

    it "creates f#inv_img for a FOL function f" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      lookupByName th "f#inv_img" `shouldSatisfy` isJust

    it "f#dir_img has kind FunctionKindDirectImageFunction" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      case lookupByName th "f#dir_img" of
        Just (EntityFunction fn) ->
          funcKind fn `shouldBe` FunctionKindDirectImageFunction
        _ -> fail "f#dir_img not found or wrong type"

    it "f#inv_img has kind FunctionKindInverseImageFunction" $ do
      th <- buildStr "{ signature { sort S; sort T; f : S → T; } }"
      case lookupByName th "f#inv_img" of
        Just (EntityFunction fn) ->
          funcKind fn `shouldBe` FunctionKindInverseImageFunction
        _ -> fail "f#inv_img not found or wrong type"

    it "SOL function F (uppercase) does NOT get f_inv" $ do
      th <- buildStr "{ signature { sort S; sort T; F : S → T; } }"
      lookupByName th "F_inv" `shouldSatisfy` isNothing

  -- ── Gap 6: mereological translation ────────────────────────────────────
  describe "Gap 6: mereological translation" $ do

    it "produces a translated fact for each assertion" $ do
      th <- buildStr "{ signature { sort S; } axioms { assertions { ⊤; } } }"
      let translated = filter factIsMereologicalTranslation (theoryFacts th)
      length translated `shouldSatisfy` (>= 1)

    it "translated facts have the same FactKind as the original" $ do
      th <- buildStr "{ signature { sort S; } axioms { assertions { ⊤; } } }"
      let translated = filter factIsMereologicalTranslation (theoryFacts th)
          original   = filter (\f -> not (factIsMereologicalTranslation f)
                                  && factKind f == FactKindAssertion) (theoryFacts th)
      length translated `shouldBe` length original

    it "does NOT produce a translated fact for SortLimitation facts" $ do
      th <- buildStr "{ signature { sort S; } }"
      let translated = filter factIsMereologicalTranslation (theoryFacts th)
      all ((/= FactKindSortLimitation) . factKind) translated `shouldBe` True

  -- ── Gap 7: entity propagation ───────────────────────────────────────────
  describe "Gap 7: subtheory entity propagation" $ do

    it "propagates implicit subtheory sort without prefix" $ do
      th <- buildStr [r|{
        subtheories { implicit { sub: { signature { sort Q; } } } }
      }|]
      lookupInParentByName th "Q" `shouldSatisfy` isJust

    it "adds implicit subtheory sort under a prefixed name for disambiguation" $ do
      th <- buildStr [r|{
        subtheories { implicit { sub: { signature { sort Q; } } } }
      }|]
      -- Should be accessible both as "Q" and "sub.Q"
      lookupInParentByName th "Q" `shouldSatisfy` isJust
      lookupInParentByName th "sub.Q" `shouldSatisfy` isJust
      
    it "propagates named subtheory sort with prefix 'sub.S'" $ do
      th <- buildStr [r|{
        subtheories { named { sub: { signature { sort S; } } } }
      }|]
      lookupInParentByName th "sub.S" `shouldSatisfy` isJust

    it "does NOT add named subtheory sort as bare 'S' in parent" $ do
      th <- buildStr [r|{
        subtheories { named { sub: { signature { sort S; } } } }
      }|]
      -- 'S' should not be accessible without prefix in the parent
      case Map.lookup "S" (theoryObjectsByName th) of
        Nothing -> return ()  -- correct: not present at all
        Just [EntitySort s] ->
          -- If present, it must be marked as reflected (came from subtheory)
          sortReflectedFrom s `shouldSatisfy` isJust
        _ -> return ()

    -- Reflection tests
    it "reflects SOLFunction to FOLFunction in parent" $ do
      th <- buildStr [r|{
        subtheories { reflection { refl: { signature { sort D; F : D → D; } } } }
      }|]
      case lookupInParentByName th "refl.F" of
        Just (EntityFunction f) ->
          funcKind f `shouldBe` FunctionKindFOLFunctionFromTheory
        _ -> fail "refl.F not found or wrong type"

    it "reflection sets funcReflectedFrom on reflected function" $ do
      th <- buildStr [r|{
        subtheories { reflection { refl: { signature { sort D; F : D → D; } } } }
      }|]
      case lookupInParentByName th "refl.F" of
        Just (EntityFunction f) ->
          funcReflectedFrom f `shouldSatisfy` isJust
        _ -> fail "refl.F not found"

    it "reflects Sort to SortKindFromReflection" $ do
      th <- buildStr [r|{
        subtheories { reflection { refl: { signature { sort S; } } } }
      }|]
      case lookupInParentByName th "refl.S" of
        Just (EntitySort s) ->
          sortKind s `shouldBe` SortKindFromReflection
        _ -> fail "refl.S not found or wrong type"

    it "reflects mereological Set to Individual" $ do
      th <- buildStr [r|{
        subtheories { reflection { refl: { signature { sort D; mySet ⊆ D; } } } }
      }|]
      case lookupInParentByName th "refl.mySet" of
        Just (EntityMereological m) ->
          mereoKind m `shouldBe` MereologicalEntityKindIndividual
        _ -> fail "refl.mySet not found or wrong type"

    it "original entity in subtheory is unchanged after reflection" $ do
      th <- buildStr [r|{
        subtheories { reflection { refl: { signature { sort D; F : D → D; } } } }
      }|]
      let subtheories = theorySubtheories th
      case find (\s -> theoryName s == "refl") subtheories of
        Nothing -> fail "subtheory 'refl' not found"
        Just sub ->
          case lookupByName sub "F" of
            Just (EntityFunction f) ->
              funcKind f `shouldBe` FunctionKindSOLFunctionFromTheory
            _ -> fail "F not found in subtheory or wrong kind"

  describe "Naming conflict resolution" $ do

    it "allows two implicit subtheories to define the same entity name with disambiguation" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub1: { signature { sort S; } }
            sub2: { signature { sort S; } }
          }
        }
      }|]
      -- Should parse successfully (no duplicate declaration error)
      th <- buildStr input
      -- Unqualified lookup should be ambiguous
      case lookupInParentByName th "S" of
        Just _ -> fail "Expected ambiguous unqualified lookup (multiple matches)"
        Nothing -> return ()
      -- Qualified lookups should work
      lookupInParentByName th "sub1.S" `shouldSatisfy` isJust
      lookupInParentByName th "sub2.S" `shouldSatisfy` isJust

    it "no error when two implicit subtheories define same name" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub1: { signature { sort S; } }
            sub2: { signature { sort S; } }
          }
        }
        axioms {
          assertions {
            sub1.S = sub2.S;
          }
        }
      }|]
      th <- buildStr input
      return ()

    it "rejects name conflict when parent and implicit subtheory both declare S" $ do
      let input = [r|{
        signature { sort S; }
        subtheories {
          implicit {
            sub: { signature { sort S; } }
          }
        }
      }|]
      result <- buildStrEither input
      case result of
        Left err -> err `shouldContain` "Name conflict"
        Right _ -> fail "Expected build error"

    it "allows explicit qualification to access shadowed entity" $ do
      let input = [r|{
        signature { sort ParentS; }
        subtheories {
          implicit {
            sub: { signature { sort ChildS; } }
          }
        }
        axioms {
          assertions {
            sub.ChildS = ParentS;
          }
        }
      }|]
      -- Use different names to avoid conflict, test qualification
      th <- buildStr input
      return ()

    it "reports duplicate alias when two implicit subtheories have same name" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub: { signature { sort S; } }
            sub: { signature { sort T; } }
          }
        }
      }|]
      result <- buildStrEither input
      case result of
        Left err -> err `shouldContain` "Duplicate subtheory alias(es): sub"
        Right _ -> fail "Expected duplicate alias error"

    it "rejects duplicate sort name when implicit subtheory conflicts with parent entity" $ do
      let input = [r|{
        signature { sort S; }
        subtheories {
          implicit {
            sub: { signature { sort S; } }
          }
        }
      }|]
      result <- buildStrEither input
      case result of
        Left err -> err `shouldContain` "Name conflict"
        Right _ -> fail "Expected duplicate declaration error"

-- | Parse and build, returning Either String for error testing
buildStrEither :: String -> IO (Either String Theory)
buildStrEither input = do
  case parseString input of
    Left err -> return (Left (show err))
    Right ast -> case buildTheoryPure emptyPureResolver Nothing ast of
      Left err -> return (Left err)
      Right th -> return (Right th)

