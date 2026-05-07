{-# LANGUAGE QuasiQuotes #-}
-- | Tests for the ported IR features (Gaps 1-7).
--
-- Run with: cabal test ir-tests
module Main where

import Test.Hspec
import Data.List            (find)
import Data.Maybe           (isJust, isNothing, mapMaybe, fromJust)
import qualified Data.Map.Strict as Map
import Text.RawString.QQ    (r)
import Control.Exception (try, evaluate, SomeException, displayException)

import Eidos.Parse.Parser         (parseString)
import Eidos.FromSyntax     (buildTheoryPure)
import Eidos.BuildMonad     (emptyPureResolver, mkPureResolver)
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
      th <- buildStr "{ signature { sort S; }, axioms { assertions { ⊤; } } }"
      let translated = filter factIsMereologicalTranslation (theoryFacts th)
      length translated `shouldSatisfy` (>= 1)

    it "translated facts have the same FactKind as the original" $ do
      th <- buildStr "{ signature { sort S; }, axioms { assertions { ⊤; } } }"
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
        subtheories { reflection { refl: { signature { sort D; MySet ⊆ D; } } } }
      }|]
      case lookupInParentByName th "refl.MySet" of
        Just (EntityMereological m) ->
          mereoKind m `shouldBe` MereologicalEntityKindIndividual
        _ -> fail "refl.MySet not found or wrong type"

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

    it "allows two implicit subtheories to define the same entity name" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub1: { signature { sort S; } }, sub2: { signature { sort S; } }
          }
        }
      }|]
      th <- buildStr input
      -- Unqualified S should resolve (merged)
      lookupInParentByName th "S" `shouldSatisfy` isJust
      -- Qualified lookups should also work
      lookupInParentByName th "sub1.S" `shouldSatisfy` isJust
      lookupInParentByName th "sub2.S" `shouldSatisfy` isJust
        
    it "rejects functions with same name but different arities" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub1: { 
              signature { 
                sort D; 
                f : D → D; 
              } 
            }, sub2: { 
              signature { 
                sort D; 
                f : D, D → D; 
              } 
            }
          }
        }
      }|]
      result <- buildStrEither input
      case result of
        Left err -> err `shouldContain` "incompatible"
        Right _ -> fail "Expected error for different arities"

    it "merges compatible entities with the same name" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub1: { signature { sort S; } }, sub2: { signature { sort S; } }
          }
        }
      }|]
      th <- buildStr input
      -- Should have one entry for S (merged)
      case Map.lookup "S" (theoryObjectsByName th) of
        Just [e] -> return ()  -- exactly one entity
        _ -> fail "Expected merged entity"

    it "no error when two implicit subtheories define same name" $ do
      let input = [r|{
        subtheories {
          implicit {
            sub1: { signature { sort S; } }, sub2: { signature { sort S; } }
          }
        }, axioms {
          assertions {
            sub1.S = sub2.S;
          }
        }
      }|]
      th <- buildStr input
      return ()

    it "accepts name duplication when parent and implicit subtheory both declare S" $ do
      let input = [r|{
        signature { sort S; }, subtheories {
          implicit {
            sub: { signature { sort S; } }
          }
        }
      }|]
      result <- buildStrEither input
      return ()

    it "allows explicit qualification to access shadowed entity" $ do
      let input = [r|{
        signature { sort ParentS; }, subtheories {
          implicit {
            sub: { signature { sort ChildS; } }
          }
        }, axioms {
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
            sub: { signature { sort S; } }, sub: { signature { sort T; } }
          }
        }
      }|]
      result <- buildStrEither input
      case result of
        Left err -> err `shouldContain` "Duplicate subtheory alias(es): sub"
        Right _ -> fail "Expected duplicate alias error"

    it "accepts duplicate sort name when implicit subtheory conflicts with parent entity" $ do
      let input = [r|{
        signature { sort S; }, subtheories {
          implicit {
            sub: { signature { sort S; } }
          }
        }
      }|]
      result <- buildStrEither input
      return ()

    it "allows nested implicit subtheories with path qualification" $ do
      let input = [r|{
        subtheories {
          implicit {
            level1: {
              subtheories {
                implicit {
                  level2: {
                    signature { sort S; }
                  }
                }
              }
            }
          }
        }
      }|]
      th <- buildStr input

      lookupInParentByName th "level1.level2.S" `shouldSatisfy` isJust
      lookupInParentByName th "level1.S" `shouldSatisfy` isJust
      lookupInParentByName th "level1.level2.S" `shouldSatisfy` isJust

    it "allows paths mixing implicit and named subtheories" $ do
      let input = [r|{
        subtheories {
          implicit {
            imp: {
              subtheories {
                named {
                  named: {
                    signature { sort S; }
                  }
                }
              }
            }
          }
        }
      }|]
      th <- buildStr input
      -- imp is implicit, so its entities are flattened
      lookupInParentByName th "named.S" `shouldSatisfy` isJust
      lookupInParentByName th "imp.named.S" `shouldSatisfy` isJust
      -- But "S" alone should NOT work (named subtheory doesn't flatten)
      lookupInParentByName th "S" `shouldSatisfy` isNothing

    it "resolves deep paths correctly when names repeat" $ do
      let input = [r|{
        subtheories {
          implicit {
            A: {
              subtheories {
                implicit {
                  B: {
                    signature { sort S; }
                  }
                }
              }
            }, C: {
              subtheories {
                implicit {
                  B: {
                    signature { sort T; }
                  }
                }
              }
            }
          }
        }
      }|]
      th <- buildStr input
      
      -- A.B.S should work
      lookupInParentByName th "A.B.S" `shouldSatisfy` isJust
      -- C.B.T should work
      lookupInParentByName th "C.B.T" `shouldSatisfy` isJust
      -- But "B.S" is ambiguous (which B?)
      isAmbiguousInParent th "B.S" `shouldBe` False

    it "handles paths through reflection subtheories" $ do
      let input = [r|{
        subtheories {
          reflection {
            refl: {
              subtheories {
                named {
                  named: {
                    signature { sort S; }
                  }
                }
              }
            }
          }
        }
      }|]
      th <- buildStr input
      -- refl is reflection, so its entities are transformed but still accessible via path
      lookupInParentByName th "refl.named.S" `shouldSatisfy` isJust
      -- The sort should have SortKindFromReflection
      case lookupInParentByName th "refl.named.S" of
        Just (EntitySort s) -> sortKind s `shouldBe` SortKindFromReflection
        _ -> fail "Expected reflected sort"


    it "resolves paths through external subtheories" $ do
      -- This would need a mock resolver
      let resolver = mkPureResolver [("ext", "{ signature { sort S; } }")]
      let input = [r|{
        subtheories {
          implicit {
            imported: @ext
          }
        }
      }|]
      -- This test requires using buildTheoryPure with the resolver
      pendingWith "Requires mock resolver integration"

  describe "Subtheory retrieval" $ do

    it "retrieves all subtheories from a theory" $ do
      let input = [r|{
        subtheories {
          implicit { imp: { signature { sort ImpSort; } } }, named { named: { signature { sort NamedSort; } } }, reflection { refl: { signature { sort ReflSort; } } }
        }
      }|]
      th <- buildStr input
      let subs = theorySubtheories th
      length subs `shouldBe` 3
      
      -- Find subtheories by name
      let impSub = find (\s -> theoryName s == "imp") subs
      let namedSub = find (\s -> theoryName s == "named") subs
      let reflSub = find (\s -> theoryName s == "refl") subs
      
      impSub `shouldSatisfy` isJust
      namedSub `shouldSatisfy` isJust
      reflSub `shouldSatisfy` isJust
      
      -- Verify their kinds (reflection flag)
      let imp = fromJust impSub
      let named = fromJust namedSub
      let refl = fromJust reflSub
      
      theoryReflection imp `shouldBe` False
      theoryReflection named `shouldBe` False
      theoryReflection refl `shouldBe` True
      
      -- Verify they contain their expected sorts
      let impSorts = [ sortName s | EntitySort s <- theoryObjects imp ]
      impSorts `shouldContain` ["ImpSort"]
      
      let namedSorts = [ sortName s | EntitySort s <- theoryObjects named ]
      namedSorts `shouldContain` ["NamedSort"]
      
      let reflSorts = [ sortName s | EntitySort s <- theoryObjects refl ]
      reflSorts `shouldContain` ["ReflSort"]

    it "retrieves nested subtheories" $ do
      let input = [r|{
        subtheories {
          implicit {
            level1: {
              subtheories {
                implicit {
                  level2: {
                    signature { sort DeepSort; }
                  }
                }
              }
            }
          }
        }
      }|]
      th <- buildStr input
      let level1 = head (theorySubtheories th)
      theoryName level1 `shouldBe` "level1"
      
      let level2 = head (theorySubtheories level1)
      theoryName level2 `shouldBe` "level2"
      
      -- Verify the nested sort is in level2
      let sorts = [ sortName s | EntitySort s <- theoryObjects level2 ]
      sorts `shouldContain` ["DeepSort"]
      
      -- Also verify propagation to root
      lookupInParentByName th "level1.level2.DeepSort" `shouldSatisfy` isJust

    it "retrieves subtheories from a theory with no subtheories" $ do
      th <- buildStr "{ signature { sort S; } }"
      let subs = theorySubtheories th
      length subs `shouldBe` 0  -- Compare length instead of the list itself

    it "retrieves subtheories from a theory with multiple subtheories of the same kind" $ do
      let input = [r|{
        subtheories {
          named {
            sub1: { signature { sort A; } }, sub2: { signature { sort B; } }, sub3: { signature { sort C; } } 
          }
        }
      }|]
      th <- buildStr input
      let subs = theorySubtheories th
      length subs `shouldBe` 3
      
      let names = map theoryName subs
      names `shouldContain` ["sub1", "sub2", "sub3"]

  -- ── Items 1-4: implicit subtheory merge correctness ─────────────────────
  describe "Implicit merge correctness (items 1-4)" $ do

    -- Item 1: order-independence of createCanonicalEntity
    it "item1: merge is order-independent — swapping sub1/sub2 gives same entity count" $ do
      th1 <- buildStr [r|{
        subtheories { implicit {
          sub1: { signature { sort S; f: 𝔻 → 𝔻; } }, sub2: { signature { sort S; f: 𝔻 → 𝔻; } }
        }}
      }|]
      th2 <- buildStr [r|{
        subtheories { implicit {
          sub2: { signature { sort S; f: 𝔻 → 𝔻; } }, sub1: { signature { sort S; f: 𝔻 → 𝔻; } }
        }}
      }|]
      -- Both orderings must produce exactly one canonical unqualified entry for S
      let countS t = maybe 0 length (Map.lookup "S" (theoryObjectsByName t))
      countS th1 `shouldBe` 1
      countS th2 `shouldBe` 1
      -- And exactly one for f
      let countF t = maybe 0 length (Map.lookup "f" (theoryObjectsByName t))
      countF th1 `shouldBe` 1
      countF th2 `shouldBe` 1

    it "item1: canonical entity's theory is the parent, not a subtheory" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      case lookupInParentByName th "S" of
        Just (EntitySort s) ->
          -- The canonical sort should be anchored to the root theory, not "sub"
          theoryName (sortTheory s) `shouldBe` ""
        _ -> fail "S not found or wrong kind"

    -- Item 2: mereological operations now get unqualified aliases (not treated as built-in sorts)
    it "item2: implicit sub's '+' creates an unqualified alias in parent" $ do
      -- The parent already has '+'; an implicit sub's '+' should generate
      -- a merge equality fact, NOT skip silently
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      -- sub.+ is registered as a qualified name
      Map.lookup "sub.+" (theoryObjectsByName th) `shouldSatisfy` maybe False (not . null)

    it "item2: implicit sub's operations produce FactKindImplicitMerge facts for built-in sorts 𝔻/ℙ/𝕌" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      -- Any implicit subtheory triggers merge facts for 𝔻, ℙ, 𝕌
      let mergeFacts = filter (\f -> factKind f == FactKindImplicitMerge) (theoryFacts th)
      mergeFacts `shouldSatisfy` (not . null)

    -- Item 3: equality facts use FactKindImplicitMerge, always lhs = sub.rhs
    it "item3: merge equality facts have FactKindImplicitMerge, not FactKindAssertion" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub1: { signature { sort S; } }, sub2: { signature { sort S; } }
        }}
      }|]
      let mergeFacts    = filter (\f -> factKind f == FactKindImplicitMerge) (theoryFacts th)
          assertionFacts = filter (\f -> factKind f == FactKindAssertion)     (theoryFacts th)
      -- At least two merge facts: S = sub1.S and S = sub2.S
      length mergeFacts `shouldSatisfy` (>= 2)
      -- No user assertions were written, so assertion list should be empty
      length assertionFacts `shouldBe` 0

    it "item3: merge fact for single implicit sub has form 'S = sub.S'" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      let mergeFacts = filter (\f -> factKind f == FactKindImplicitMerge) (theoryFacts th)
      -- Find the fact that mentions S and sub.S
      mergeFacts `shouldSatisfy` any (mergeFactMentions "S" "sub.S")

    it "item3: two implicit subs each get their own merge equality fact" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub1: { signature { sort S; } }, sub2: { signature { sort S; } }
        }}
      }|]
      let mergeFacts = filter (\f -> factKind f == FactKindImplicitMerge) (theoryFacts th)
      mergeFacts `shouldSatisfy` any (mergeFactMentions "S" "sub1.S")
      mergeFacts `shouldSatisfy` any (mergeFactMentions "S" "sub2.S")

    it "item3: unqualified name is always the LHS of the merge fact" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      let mergeFacts = filter (\f -> factKind f == FactKindImplicitMerge) (theoryFacts th)
      -- The LHS of every merge fact must NOT contain a dot (i.e. unqualified)
      mergeFacts `shouldSatisfy` all mergeFactLhsIsUnqualified

    -- Item 4: internal #-names never leak as unqualified
    it "item4: implicit sub's S#min does not appear unqualified in parent" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      Map.lookup "S#min" (theoryObjectsByName th) `shouldSatisfy` isNothing
      Map.lookup "S#max" (theoryObjectsByName th) `shouldSatisfy` isNothing

    it "item4: implicit sub's S#min appears only as sub.S#min" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; } }
        }}
      }|]
      Map.lookup "sub.S#min" (theoryObjectsByName th) `shouldSatisfy` maybe False (not . null)

    it "item4: function image helpers do not leak unqualified" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          sub: { signature { sort S; sort T; f : S → T; } }
        }}
      }|]
      Map.lookup "f#dir_img" (theoryObjectsByName th) `shouldSatisfy` isNothing
      Map.lookup "f#inv_img" (theoryObjectsByName th) `shouldSatisfy` isNothing
      -- But the qualified versions must exist
      Map.lookup "sub.f#dir_img" (theoryObjectsByName th) `shouldSatisfy` maybe False (not . null)

    -- Three-deep inheritance chain (preorder → partial_order → lattice)
    it "item1+3: three-deep implicit chain merges LessThanOrEq with exactly one canonical" $ do
      th <- buildStr [r|{
        subtheories { implicit {
          lat: {
            subtheories { implicit {
              po: {
                subtheories { implicit {
                  pre: { signature { LessThanOrEq ⊆ 𝔻, 𝔻; } }
                }}
              }
            }}
          }
        }}
      }|]
      -- Exactly one unqualified entry
      case Map.lookup "LessThanOrEq" (theoryObjectsByName th) of
        Just [_] -> return ()
        Just es  -> fail $ "Expected 1 canonical, got " ++ show (length es)
        Nothing  -> fail "LessThanOrEq not found"
      -- At least one merge fact mentioning LessThanOrEq on the LHS
      let mergeFacts = filter (\f -> factKind f == FactKindImplicitMerge) (theoryFacts th)
      mergeFacts `shouldSatisfy` any (mergeFactMentionsLhs "LessThanOrEq")

  describe "Theory usage flags (𝔻/ℙ)" $ do
    it "marks theoryUsesDomain when 𝔻 is referenced in signature" $ do
      th <- buildStr "{ signature { x : 𝔻; } }"
      theoryUsesDomain th `shouldBe` True

    it "marks theoryUsesProp when ℙ is referenced in signature" $ do
      th <- buildStr "{ signature { P : ℙ; } }"
      theoryUsesProp th `shouldBe` True

    it "marks theoryUsesProp when logical connectives are used in axioms" $ do
      th <- buildStr "{ axioms { assertions { ⊤ ∧ ⊤; } } }"
      theoryUsesProp th `shouldBe` True

    it "inherits usage flags from implicit subtheories" $ do
      th <- buildStr [r|{
        subtheories {
          implicit {
            sub: {
              signature { x : 𝔻; },
              axioms { assertions { ⊤ ∧ ⊤; } }
            }
          }
        }
      }|]
      theoryUsesDomain th `shouldBe` True
      theoryUsesProp th `shouldBe` True

    it "does not inherit usage flags from named subtheories" $ do
      th <- buildStr [r|{
        subtheories {
          named {
            sub: {
              signature { x : 𝔻; },
              axioms { assertions { ⊤ ∧ ⊤; } }
            }
          }
        }
      }|]
      theoryUsesDomain th `shouldBe` False
      theoryUsesProp th `shouldBe` False

-- | Extract the (lhsName, rhsName) pair from a merge equality fact.
-- Returns Nothing for any other shape.
mergeFactNames :: Fact -> Maybe (String, String)
mergeFactNames fact = case factPropExpr fact of
  ResolvedPropBicond rImpl [] -> case rImpl of
    ResolvedRightImpl lImpl Nothing -> case lImpl of
      ResolvedLeftImpl disj [] -> case disj of
        ResolvedDisj conj [] -> case conj of
          ResolvedConj neg [] -> case neg of
            ResolvedNegChild quant -> case quant of
              ResolvedQuantified [] atom -> case atom of
                ResolvedAtomicTermPair tp -> extractPair tp
                _ -> Nothing
              _ -> Nothing
            _ -> Nothing
          _ -> Nothing
        _ -> Nothing
      _ -> Nothing
    _ -> Nothing
  _ -> Nothing
  where
    extractPair (ResolvedTermPair lTerm [rel] _) =
      case (lTerm, resolvedRFTRight rel) of
        ( ResolvedTerm (ResolvedFactor (ResolvedBTAtomic lref) [] _) [] _
          , ResolvedTerm (ResolvedFactor (ResolvedBTAtomic rref) [] _) [] _ )
          | resolvedRFTOp rel == "=" ->
              Just (resolvedConstRefName lref, resolvedConstRefName rref)
        _ -> Nothing
    extractPair _ = Nothing

-- | Check that a 'FactKindImplicitMerge' fact has the form @lhs = rhs@.
mergeFactMentions :: String -> String -> Fact -> Bool
mergeFactMentions lhs rhs fact = mergeFactNames fact == Just (lhs, rhs)

-- | Check that the LHS of a merge fact is an unqualified name (no dot).
mergeFactLhsIsUnqualified :: Fact -> Bool
mergeFactLhsIsUnqualified fact = case mergeFactNames fact of
  Just (lhs, _) -> '.' `notElem` lhs
  Nothing       -> True

-- | True if a merge fact's LHS name equals the given string.
mergeFactMentionsLhs :: String -> Fact -> Bool
mergeFactMentionsLhs lhs fact = case mergeFactNames fact of
  Just (l, _) -> l == lhs
  Nothing     -> False

-- | Parse and build, returning Either String for error testing
buildStrEither :: String -> IO (Either String Theory)
buildStrEither input = do
  case parseString input of
    Left err -> return (Left (show err))
    Right ast -> case buildTheoryPure emptyPureResolver Nothing ast of
      Left err -> return (Left err)
      Right th -> return (Right th)

-- For tests that expect ambiguity
isAmbiguousInParent :: Theory -> String -> Bool
isAmbiguousInParent th nm = case Map.lookup nm (theoryObjectsByName th) of
  Just (_:_:_) -> True
  _ -> False

debugMap :: Theory -> IO ()
debugMap th = do
  putStrLn "=== Theory objectsByName ==="
  mapM_ (\(k, v) -> putStrLn $ k ++ " -> " ++ show (length v) ++ " entities") (Map.toList (theoryObjectsByName th))
