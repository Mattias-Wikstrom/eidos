{-# LANGUAGE QuasiQuotes #-}
-- | Tests for implicit subtheory merge facts in Lean 4 output.
--
-- Verifies that:
--   1. Merge facts are emitted for direct implicit children only (not transitive)
--   2. Sorts are expanded into D_Min/D_Max pairs
--   3. Functions use plain equality, propositions use metafact wrapper
--   4. Built-in sorts (𝕌, ℙ, 𝔻) are properly handled with Unicode names
--   5. No duplicate merge facts
--   6. Theories with multiple implicit children get merge facts for each
module Main where

import Test.Hspec
import Text.RawString.QQ (r)
import Data.List (nub, isInfixOf)

import Eidos.Parse.Parser            (parseString)
import Eidos.FromSyntax        (buildTheoryPure)
import qualified Eidos.Pipeline as PL
import Eidos.Pipeline.MkAxiomSets (mkAxiomSets)
import Eidos.Backend.LeanProps.LeanExpr   (LeanDoc(..), LeanBlock(..), LeanDecl(..), LeanAxiom(..),
                                LeanExpr(..), renderLeanExpr, renderLeanDoc)
import Eidos.Backend.LeanProps.LeanProps (renderAxiomSetsToDecls, defaultLeanPropsOptions)
import Eidos.Backend.LeanProps.LeanAxiomSet (AxiomSet(..), Tag(..))

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

buildStr :: String -> IO LeanDoc
buildStr src = case parseString src of
  Left err  -> fail ("Parse error: " ++ show err)
  Right ast -> case buildTheoryPure ast of
    Left err -> fail ("Build error: " ++ err)
    Right th ->
      let pt        = PL.prepareTheory PL.defaultPipelineOptions th
          axiomSets = mkAxiomSets pt
          decls     = renderAxiomSetsToDecls defaultLeanPropsOptions axiomSets
      in return (LeanDoc { leanDocTheoryName = "", leanDocBlocks = [LeanBlock "__main__" decls] })

-- | All axioms in a doc.
axioms :: LeanDoc -> [LeanAxiom]
axioms doc = [ ax | LeanBlock _ decls <- leanDocBlocks doc, DeclAxiom ax <- decls ]

-- | All type expressions declared in the doc.
allTypes :: LeanDoc -> [LeanExpr]
allTypes = map axiomType . axioms

-- | All axiom names in the doc.
allNames :: LeanDoc -> [String]
allNames = map axiomName . axioms

-- | True when some axiom has exactly this name.
hasAxiomNamed :: LeanDoc -> String -> Bool
hasAxiomNamed doc name = name `elem` allNames doc

-- | True when there is an axiom 'name' with exactly this type.
hasAxiom :: LeanDoc -> String -> LeanExpr -> Bool
hasAxiom doc name ty = any (\ax -> axiomName ax == name && axiomType ax == ty) (axioms doc)

-- | True when the doc contains an implicit merge fact for the given entity.
hasMergeFact :: LeanDoc -> String -> String -> Bool
hasMergeFact doc lhs rhs =
  let mergeName = lhs ++ "_from_" ++ rhs
  in hasAxiomNamed doc mergeName

-- | True when the doc contains a D_Min merge fact.
hasDMinMerge :: LeanDoc -> String -> Bool
hasDMinMerge doc rhs = hasMergeFact doc "D_Min" rhs

-- | True when the doc contains a D_Max merge fact.
hasDMaxMerge :: LeanDoc -> String -> Bool
hasDMaxMerge doc rhs = hasMergeFact doc "D_Max" rhs

-- | True when a merge fact uses the metafact wrapper.
mergeIsMetafactWrapped :: LeanDoc -> String -> String -> Bool
mergeIsMetafactWrapped doc lhs rhs =
  let mergeName = lhs ++ "_from_" ++ rhs
  in any (\ax -> axiomName ax == mergeName && isMetafactWrapped (axiomType ax)) (axioms doc)
  where
    isMetafactWrapped (LApp (LVar "WrapMetafact") _) = True
    isMetafactWrapped _ = False

-- | True when a merge fact is a plain equality (for functions).
mergeIsPlainEquality :: LeanDoc -> String -> String -> Bool
mergeIsPlainEquality doc lhs rhs =
  let mergeName = lhs ++ "_from_" ++ rhs
  in any (\ax -> axiomName ax == mergeName && isPlainEq (axiomType ax)) (axioms doc)
  where
    isPlainEq (LEq _ _) = True
    isPlainEq _ = False

-- | True when the doc declares no duplicate axiom names.
noDuplicates :: LeanDoc -> Bool
noDuplicates doc = nub (allNames doc) == allNames doc

-- | Render the doc to text for searching.
renderedDoc :: LeanDoc -> String
renderedDoc doc = renderLeanDoc doc

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  describe "Implicit subtheory merge facts" $ do

    describe "Single implicit child" $ do

      it "generates D_Min and D_Max merge facts for sort D" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            magma: { signature { sort D; op : D, D → D; } }
          }}
        }|]
        hasDMinMerge doc "magma" `shouldBe` True
        hasDMaxMerge doc "magma" `shouldBe` True

      it "generates op merge fact as plain equality" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            magma: { signature { sort D; op : D, D → D; } }
          }}
        }|]
        hasMergeFact doc "op" "magma" `shouldBe` True
        mergeIsPlainEquality doc "op" "magma" `shouldBe` True

      it "generates ℙ_Min and ℙ_Max merge facts" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; } }
          }}
        }|]
        hasMergeFact doc "ℙ_Min" "sub" `shouldBe` True
        hasMergeFact doc "ℙ_Max" "sub" `shouldBe` True

      it "generates 𝕌_Min and 𝕌_Max merge facts" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; } }
          }}
        }|]
        hasMergeFact doc "𝕌_Min" "sub" `shouldBe` True
        hasMergeFact doc "𝕌_Max" "sub" `shouldBe` True

      it "generates 𝔻_Min and 𝔻_Max merge facts when 𝔻 is used" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { MySet ⊆ 𝔻; } }
          }}
        }|]
        hasMergeFact doc "𝔻_Min" "sub" `shouldBe` True
        hasMergeFact doc "𝔻_Max" "sub" `shouldBe` True

      it "sort merge facts are metafact-wrapped" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; } }
          }}
        }|]
        mergeIsMetafactWrapped doc "D_Min" "sub" `shouldBe` True
        mergeIsMetafactWrapped doc "D_Max" "sub" `shouldBe` True

      it "mereological operations get merge facts" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; } }
          }}
        }|]
        hasMergeFact doc "plus" "sub" `shouldBe` True
        hasMergeFact doc "times" "sub" `shouldBe` True
        hasMergeFact doc "sub" "sub" `shouldBe` True

    describe "Two implicit children" $ do

      it "generates merge facts for each child independently" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub1: { signature { sort D; op : D, D → D; } },
            sub2: { signature { sort D; } }
          }}
        }|]
        hasDMinMerge doc "sub1" `shouldBe` True
        hasDMaxMerge doc "sub1" `shouldBe` True
        hasDMinMerge doc "sub2" `shouldBe` True
        hasDMaxMerge doc "sub2" `shouldBe` True
        hasMergeFact doc "op" "sub1" `shouldBe` True

    describe "Nested implicit subtheories" $ do

      it "does NOT generate transitive merge facts in grandparent" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            lattice: {
              subtheories { implicit {
                partial_order: {
                  subtheories { implicit {
                    preorder: { signature { LessThanOrEq ⊆ 𝔻, 𝔻; } }
                  }}
                }
              }}
            }
          }}
        }|]
        -- lattice should have merge facts for partial_order's entities
        hasDMinMerge doc "partial_order" `shouldBe` False
        -- But should NOT have merge facts for preorder directly
        hasDMinMerge doc "preorder" `shouldBe` False
        hasMergeFact doc "LessThanOrEq" "preorder" `shouldBe` False

    describe "No duplicate merge facts" $ do

      it "produces no duplicate axiom names with single implicit child" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; } }
          }}
        }|]
        noDuplicates doc `shouldBe` True

      it "produces no duplicate axiom names with two implicit children" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub1: { signature { sort D; } },
            sub2: { signature { sort D; } }
          }}
        }|]
        noDuplicates doc `shouldBe` True

    describe "User-declared entities" $ do

      it "generates merge fact for user-declared individual" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; n : D; } }
          }}
        }|]
        hasMergeFact doc "n" "sub" `shouldBe` True

      it "generates merge fact for user-declared relation" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; LessThanOrEq ⊆ D, D; } }
          }}
        }|]
        hasMergeFact doc "LessThanOrEq" "sub" `shouldBe` True

    describe "Merge fact structure in rendered output" $ do

      it "D_Min merge uses metafact wrapper in render" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; } }
          }}
        }|]
        let rendered = renderedDoc doc
        rendered `shouldSatisfy` ("D_Min_from_sub" `isInfixOf`)
        rendered `shouldSatisfy` ("𝕌_Min ∧ D_Min = sub.D_Min" `isInfixOf`)

      it "op merge uses plain equality in render" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            sub: { signature { sort D; op : D, D → D; } }
          }}
        }|]
        let rendered = renderedDoc doc
        rendered `shouldSatisfy` ("op_from_sub" `isInfixOf`)
        rendered `shouldSatisfy` ("op = sub.op" `isInfixOf`)

      it "merge facts use _from_ naming convention" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            magma: { signature { sort D; } }
          }}
        }|]
        let rendered = renderedDoc doc
        rendered `shouldSatisfy` ("D_Min_from_magma" `isInfixOf`)
        rendered `shouldSatisfy` ("D_Max_from_magma" `isInfixOf`)

    describe "Real-world scenario: lattice theory" $ do

      it "lattice has merge facts for both lower_semi_lattice and upper_semi_lattice" $ do
        doc <- buildStr [r|{
          subtheories { implicit {
            lower_semi_lattice: {
              subtheories { implicit {
                partial_order: {
                  subtheories { implicit {
                    preorder: { signature { sort D; LessThanOrEq ⊆ D, D; } }
                  }}
                }
              }},
              signature { meet : D, D → D; }
            },
            upper_semi_lattice: {
              subtheories { implicit {
                partial_order: {
                  subtheories { implicit {
                    preorder: { signature { sort D; LessThanOrEq ⊆ D, D; } }
                  }}
                }
              }},
              signature { join : D, D → D; }
            }
          }}
        }|]
        -- Direct children: lower_semi_lattice and upper_semi_lattice
        hasDMinMerge doc "lower_semi_lattice" `shouldBe` True
        hasDMaxMerge doc "lower_semi_lattice" `shouldBe` True
        hasDMinMerge doc "upper_semi_lattice" `shouldBe` True
        hasDMaxMerge doc "upper_semi_lattice" `shouldBe` True
        hasMergeFact doc "meet" "lower_semi_lattice" `shouldBe` True
        hasMergeFact doc "join" "upper_semi_lattice" `shouldBe` True
        -- Grandchildren: should NOT appear directly
        hasDMinMerge doc "partial_order" `shouldBe` False
        hasDMinMerge doc "preorder" `shouldBe` False

  describe "Unicode sort names" $ do

    it "uses 𝕌_Min/𝕌_Max for universe sort bounds" $ do
      doc <- buildStr "{ }"
      hasAxiomNamed doc "𝕌_Min" `shouldBe` True
      hasAxiomNamed doc "𝕌_Max" `shouldBe` True

    it "uses ℙ_Min/ℙ_Max for proposition sort bounds" $ do
      doc <- buildStr "{ }"
      hasAxiomNamed doc "ℙ_Min" `shouldBe` True
      hasAxiomNamed doc "ℙ_Max" `shouldBe` True

    it "uses 𝔻_Min/𝔻_Max for domain sort bounds when 𝔻 is used" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasAxiomNamed doc "𝔻_Min" `shouldBe` True
      hasAxiomNamed doc "𝔻_Max" `shouldBe` True

    it "user-declared D uses D_Min/D_Max (no clash)" $ do
      doc <- buildStr "{ signature { sort D; } }"
      hasAxiomNamed doc "D_Min" `shouldBe` True
      hasAxiomNamed doc "D_Max" `shouldBe` True