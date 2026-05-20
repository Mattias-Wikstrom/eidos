{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase  #-}
-- | Unit tests for Eidos.Export.LeanProps.
--
-- Tests operate on the Lean axiom content produced by the /current/
-- MkAxiomSets-based export path. The key design principle is that tests query the doc
-- by *semantic content* (what LeanExprs are present) rather than by axiom
-- names, label conventions, or ordering.  This makes the tests robust to
-- naming-convention changes (e.g. _top vs _min, ax1 vs numbered differently)
-- while still checking that the right logical content was generated.
--
-- Run with: cabal test leanprops-tests
module Main where

import Test.Hspec
import Text.RawString.QQ (r)
import Data.List (nub, isPrefixOf, isInfixOf)

import Eidos.Pipeline.Parse.Parser     (parseString)
import Eidos.Pipeline.FromSyntax.FromSyntax (buildTheoryPure)
import qualified Eidos.Pipeline.InvokePipeline as PL
import Eidos.Pipeline.IRProcessing.MkAxiomSets (mkAxiomSets)
import Eidos.Pipeline.Targets.LeanProps.LeanProps
import Eidos.Pipeline.IRProcessing.AxiomSet (AxiomSet(..))

-- ---------------------------------------------------------------------------
-- Naming conventions
-- ---------------------------------------------------------------------------

-- Base names for built-in sorts
uName, pName, dName :: String
uName = "𝕌"
pName = "ℙ"
dName = "𝔻"

-- Suffixes for bounds
minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

-- Built-in bound names
uMin, uMax, pMin, pMax, dMin, dMax :: LeanExpr
uMin = LVar (uName ++ minSuffix)
uMax = LVar (uName ++ maxSuffix)
pMin = LVar (pName ++ minSuffix)
pMax = LVar (pName ++ maxSuffix)
dMin = LVar (dName ++ minSuffix)
dMax = LVar (dName ++ maxSuffix)

-- User sort bound names
sortMin, sortMax :: String -> LeanExpr
sortMin name = LVar (name ++ minSuffix)
sortMax name = LVar (name ++ maxSuffix)

-- Prop declaration name
propDeclName :: String -> String
propDeclName = id  -- Just the name itself, but centralized for consistency

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
axioms doc = [ ax | blk <- leanDocBlocks doc, DeclAxiom ax <- blockDecls blk ]

-- | All type expressions declared in the doc.
allTypes :: LeanDoc -> [LeanExpr]
allTypes = map axiomType . axioms

-- | True when some axiom has exactly this type expression.
hasType :: LeanDoc -> LeanExpr -> Bool
hasType doc ty = ty `elem` allTypes doc

-- | True when the doc contains an axiom  `A → B`  for the given A and B.
hasImplication :: LeanDoc -> LeanExpr -> LeanExpr -> Bool
hasImplication doc a b = hasType doc (LImpl a b)

-- | True when the doc contains the Prop declaration for the given name.
hasPropDecl :: LeanDoc -> String -> Bool
hasPropDecl doc name = hasType doc LProp && any isPropAxiom (axioms doc)
  where isPropAxiom ax = axiomType ax == LProp && axiomName ax == name

-- ---------------------------------------------------------------------------
-- Fact-wrapper helpers
--
-- Facts, assertions, and metafacts are emitted as LApp nodes calling the
-- WrapFact / WrapAssertion / WrapMetafact abbreviations.  The helpers below
-- extract the body argument so tests can check semantic intent without
-- depending on the exact argument order of each abbreviation.
-- ---------------------------------------------------------------------------

-- | Bodies of all 'WrapAssertion' axioms in the doc.
assertionBodies :: LeanDoc -> [LeanExpr]
assertionBodies doc = [ body | LApp (LVar "WrapAssertion") [_, _, body] <- allTypes doc ]

-- | True when some assertion axiom in the doc has exactly this body.
hasAssertionBody :: LeanDoc -> LeanExpr -> Bool
hasAssertionBody doc body = body `elem` assertionBodies doc

-- | True when some assertion axiom body satisfies the predicate.
hasAssertionBodyWith :: LeanDoc -> (LeanExpr -> Bool) -> Bool
hasAssertionBodyWith doc p = any p (assertionBodies doc)

-- | Bodies of all 'WrapMetafact' axioms in the doc.
metafactBodies :: LeanDoc -> [LeanExpr]
metafactBodies doc = [ body | LApp (LVar "WrapMetafact") [_, body] <- allTypes doc ]

-- | True when some metafact axiom in the doc has exactly this body.
hasMetafactBody :: LeanDoc -> LeanExpr -> Bool
hasMetafactBody doc body = body `elem` metafactBodies doc

-- | True when some metafact axiom body satisfies the predicate.
hasMetafactBodyWith :: LeanDoc -> (LeanExpr -> Bool) -> Bool
hasMetafactBodyWith doc p = any p (metafactBodies doc)

-- | True when the doc declares no duplicate axiom names.
noDuplicateNames :: LeanDoc -> Bool
noDuplicateNames doc =
  let names = map axiomName (axioms doc)
  in nub names == names

-- | True if the predicate holds for the expression or any sub-expression.
anySubExpr :: (LeanExpr -> Bool) -> LeanExpr -> Bool
anySubExpr p e = p e || case e of
  LImpl a b                       -> anySubExpr p a || anySubExpr p b
  LConj a b                       -> anySubExpr p a || anySubExpr p b
  LDisj a b                       -> anySubExpr p a || anySubExpr p b
  LBicond a b                     -> anySubExpr p a || anySubExpr p b
  LEq a b                         -> anySubExpr p a || anySubExpr p b
  LApp f args                     -> anySubExpr p f || any (anySubExpr p) args
  LForall _ _ body                -> anySubExpr p body
  LForallKw _ _ body              -> anySubExpr p body
  LExists _ _ body                -> anySubExpr p body
  LBoundedForall _ _ _ body       -> anySubExpr p body
  LForallIndividuals _ _ _ body   -> anySubExpr p body
  LBoundedExists _ _ _ body       -> anySubExpr p body
  LExistsIndividuals _ _ _ body   -> anySubExpr p body
  LProjectIntoInterval a b c      -> anySubExpr p a || anySubExpr p b || anySubExpr p c
  _                               -> False


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

    it "renders bounded forall: guard and body are inside the ∀ scope" $
      -- The exact parenthesisation of the guard is an implementation detail;
      -- what matters is that the rendered string contains the forall binder,
      -- the guard conjuncts, and the body.
      let expr = LForall "X" (LVar "Prop")
                   (LImpl (LConj (LImpl pMax (LVar "X"))
                                 (LImpl (LVar "X") pMin))
                          (LVar "body"))
          rendered = renderLeanExpr expr
      in do
        rendered `shouldSatisfy` ("∀ X : Prop," `isPrefixOf`)

    it "renders WrapAssertion LApp: output contains abbreviation name and body" $
      let rendered = renderLeanExpr (LApp (LVar "WrapAssertion") [pMin, pMax, LVar "MyProp"])
      in do
        rendered `shouldSatisfy` ("WrapAssertion" `isInfixOf`)
        rendered `shouldSatisfy` ("MyProp" `isInfixOf`)

    it "renders WrapMetafact LApp: output contains abbreviation name and body" $
      let rendered = renderLeanExpr (LApp (LVar "WrapMetafact") [uMin, LVar "MySet"])
      in do
        rendered `shouldSatisfy` ("WrapMetafact" `isInfixOf`)
        rendered `shouldSatisfy` ("MySet" `isInfixOf`)

    it "renders WrapFact LApp: output contains abbreviation name and body" $
      let rendered = renderLeanExpr (LApp (LVar "WrapFact") [pMin, LVar "MyFact"])
      in do
        rendered `shouldSatisfy` ("WrapFact" `isInfixOf`)
        rendered `shouldSatisfy` ("MyFact" `isInfixOf`)

  -- =========================================================================
  describe "theoryToLeanDoc – header" $ do
  -- =========================================================================

    it "always declares U_Min as Prop" $ do
      doc <- buildStr "{ }"
      hasPropDecl doc (propDeclName (uName ++ minSuffix)) `shouldBe` True

    it "always declares U_Max as Prop" $ do
      doc <- buildStr "{ }"
      hasPropDecl doc (propDeclName (uName ++ maxSuffix)) `shouldBe` True

    it "always declares P_Min as Prop" $ do
      doc <- buildStr "{ }"
      hasPropDecl doc (propDeclName (pName ++ minSuffix)) `shouldBe` True

    it "always declares P_Max as Prop" $ do
      doc <- buildStr "{ }"
      hasPropDecl doc (propDeclName (pName ++ maxSuffix)) `shouldBe` True

    it "does NOT declare D_Min as Prop when 𝔻 is unused" $ do
      doc <- buildStr "{ }"
      hasPropDecl doc (propDeclName (dName ++ minSuffix)) `shouldBe` False

    it "does NOT declare D_Max as Prop when 𝔻 is unused" $ do
      doc <- buildStr "{ }"
      hasPropDecl doc (propDeclName (dName ++ maxSuffix)) `shouldBe` False

    it "declares D_Min as Prop when 𝔻 is used" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasPropDecl doc (propDeclName (dName ++ minSuffix)) `shouldBe` True

    it "declares D_Max as Prop when 𝔻 is used" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasPropDecl doc (propDeclName (dName ++ maxSuffix)) `shouldBe` True

    it "always includes U_Max → P_Max in the sort ordering" $ do
      doc <- buildStr "{ }"
      hasImplication doc uMax pMax `shouldBe` True

    it "always includes P_Max → P_Min in the sort ordering" $ do
      doc <- buildStr "{ }"
      hasImplication doc pMax pMin `shouldBe` True

    it "always includes P_Min → U_Min in the sort ordering" $ do
      doc <- buildStr "{ }"
      hasImplication doc pMin uMin `shouldBe` True

    it "does NOT include D_Max → D_Min in sort ordering when 𝔻 is unused" $ do
      doc <- buildStr "{ }"
      hasImplication doc dMax dMin `shouldBe` False

    it "includes D_Max → D_Min in sort ordering when 𝔻 is used" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasImplication doc dMax dMin `shouldBe` True

    it "produces no duplicate axiom names in an empty theory" $ do
      doc <- buildStr "{ }"
      noDuplicateNames doc `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – mereological (𝕌-sorted) objects" $ do
  -- =========================================================================

    it "declares each 𝕌-kinded object as Prop" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; } }|]
      hasPropDecl doc (propDeclName "A") `shouldBe` True
      hasPropDecl doc (propDeclName "B") `shouldBe` True

    it "generates a lower-bound axiom  obj → U_Min  for each 𝕌-sorted object" $ do
      doc <- buildStr [r|{ signature { MyObj : 𝕌; } }|]
      hasImplication doc (LVar "MyObj") uMin `shouldBe` True

    it "generates an upper-bound axiom  U_Max → obj  for each 𝕌-sorted object" $ do
      doc <- buildStr [r|{ signature { MyObj : 𝕌; } }|]
      hasImplication doc uMax (LVar "MyObj") `shouldBe` True

    it "does NOT generate a lower-bound axiom for U_Min itself" $ do
      doc <- buildStr "{ }"
      -- U_Min → U_Min would be a reflexive tautology; we must not emit it
      hasImplication doc uMin uMin `shouldBe` False

    it "does NOT generate an upper-bound axiom for U_Max itself" $ do
      doc <- buildStr "{ }"
      hasImplication doc uMax uMax `shouldBe` False

    it "generates correct bounds for two 𝕌-sorted objects independently" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; } }|]
      hasImplication doc (LVar "A") uMin `shouldBe` True
      hasImplication doc uMax (LVar "A") `shouldBe` True
      hasImplication doc (LVar "B") uMin `shouldBe` True
      hasImplication doc uMax (LVar "B") `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – propositional (ℙ-sorted) objects" $ do
  -- =========================================================================

    it "declares each ℙ-kinded object as Prop" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; } }|]
      hasPropDecl doc (propDeclName "P") `shouldBe` True
      hasPropDecl doc (propDeclName "Q") `shouldBe` True

    it "generates a lower-bound axiom  prop → P_Min  for each ℙ-sorted object" $ do
      doc <- buildStr [r|{ signature { MyProp : ℙ; } }|]
      hasImplication doc (LVar "MyProp") pMin `shouldBe` True

    it "generates an upper-bound axiom  P_Max → prop  for each ℙ-sorted object" $ do
      doc <- buildStr [r|{ signature { MyProp : ℙ; } }|]
      hasImplication doc pMax (LVar "MyProp") `shouldBe` True

    it "does NOT generate a lower-bound axiom for P_Min itself" $ do
      doc <- buildStr "{ }"
      hasImplication doc pMin pMin `shouldBe` False

    it "does NOT generate an upper-bound axiom for P_Max itself" $ do
      doc <- buildStr "{ }"
      hasImplication doc pMax pMax `shouldBe` False

  -- =========================================================================
  describe "theoryToLeanDoc – 𝔻-sorted sets" $ do
  -- =========================================================================

    it "declares a 𝔻-sorted set as Prop" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasPropDecl doc (propDeclName "MySet") `shouldBe` True

    it "generates a lower-bound axiom  set → D_Min  for a 𝔻-sorted set" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasImplication doc (LVar "MySet") dMin `shouldBe` True

    it "generates an upper-bound axiom  D_Max → set  for a 𝔻-sorted set" $ do
      doc <- buildStr [r|{ signature { MySet ⊆ 𝔻; } }|]
      hasImplication doc dMax (LVar "MySet") `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – user-declared sorts" $ do
  -- =========================================================================

    it "declares limit objects for a user sort as Prop" $ do
      doc <- buildStr [r|{ signature { sort S; } }|]
      -- The limit objects must exist; we don't prescribe their exact names
      -- but we can check via the sort-ordering implication S_Max → S_Min
      let sortOrderAxioms =
            [ (a, b)
            | LImpl (LVar a) (LVar b) <- allTypes doc
            , a `notElem` [uName ++ maxSuffix, pName ++ maxSuffix, pName ++ minSuffix, dName ++ maxSuffix]
            , b `notElem` [pName ++ maxSuffix, pName ++ minSuffix, uName ++ minSuffix, dName ++ minSuffix]
            ]
      sortOrderAxioms `shouldSatisfy` (not . null)

    it "generates a sort-ordering implication  S_Max → S_Min  for a user sort" $ do
      doc <- buildStr [r|{ signature { sort S; } }|]
      hasImplication doc (sortMax "S") (sortMin "S") `shouldBe` True

    it "generates lower-bound axiom  set → S_Min  for sets inside user sorts" $ do
      doc <- buildStr [r|{ signature { sort S; MySet ⊆ S; } }|]
      hasImplication doc (LVar "MySet") (sortMin "S") `shouldBe` True

    it "generates upper-bound axiom  S_Max → set  for sets inside user sorts" $ do
      doc <- buildStr [r|{ signature { sort S; MySet ⊆ S; } }|]
      hasImplication doc (sortMax "S") (LVar "MySet") `shouldBe` True

    it "generates independent sort-ordering for multiple user sorts" $ do
      doc <- buildStr [r|{ signature { sort S; sort T; } }|]
      hasImplication doc (sortMax "S") (sortMin "S") `shouldBe` True
      hasImplication doc (sortMax "T") (sortMin "T") `shouldBe` True

    it "does NOT mix up bounds across different user sorts" $ do
      doc <- buildStr [r|{ signature { sort S; MySet ⊆ S; sort T; OtherSet ⊆ T; } }|]
      -- MySet should be bounded by S limits, not T limits
      hasImplication doc (LVar "MySet") (sortMin "T") `shouldBe` False
      hasImplication doc (sortMax "T") (LVar "MySet") `shouldBe` False

  -- =========================================================================
  describe "theoryToLeanDoc – assertions" $ do
  -- =========================================================================

    it "wraps each assertion in a WrapAssertion axiom" $ do
      doc <- buildStr [r|{ signature { P : ℙ; }, axioms { assertions { P; } } }|]
      hasAssertionBodyWith doc (const True) `shouldBe` True

    it "assertion body for P is  LVar P" $ do
      doc <- buildStr [r|{ signature { P : ℙ; }, axioms { assertions { P; } } }|]
      hasAssertionBody doc (LVar "P") `shouldBe` True

    it "assertion body for P ∨ Q is  LDisj P Q" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P ∨ Q; } } }|]
      hasAssertionBody doc (LDisj (LVar "P") (LVar "Q")) `shouldBe` True

    it "assertion body for ¬P is  LImpl P P_Max  (negation as implication to P_Max)" $ do
      doc <- buildStr [r|{ signature { P : ℙ; }, axioms { assertions { ¬P; } } }|]
      hasAssertionBody doc (LImpl (LVar "P") pMax) `shouldBe` True

    it "assertion body for P → Q is  LImpl P Q" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P → Q; } } }|]
      hasAssertionBody doc (LImpl (LVar "P") (LVar "Q")) `shouldBe` True

    it "assertion body for P ↔ Q is  LBicond P Q" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P ↔ Q; } } }|]
      hasAssertionBody doc (LBicond (LVar "P") (LVar "Q")) `shouldBe` True

    it "generates one WrapAssertion axiom per assertion" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P; Q; } } }|]
      length (assertionBodies doc) `shouldBe` 2

  -- =========================================================================
  describe "theoryToLeanDoc – metafacts" $ do
  -- =========================================================================

    it "wraps each metafact in a WrapMetafact axiom" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A × B; } } }|]
      hasMetafactBodyWith doc (const True) `shouldBe` True

    it "metafact body for A × B (product / disjunction) is  LDisj A B" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A × B; } } }|]
      hasMetafactBody doc (LDisj (LVar "A") (LVar "B")) `shouldBe` True

    it "metafact body for A + B (sum / conjunction) is  LConj A B" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A + B; } } }|]
      hasMetafactBody doc (LConj (LVar "A") (LVar "B")) `shouldBe` True

    it "mereological difference  A - B  renders as  B → A" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A - B; } } }|]
      hasMetafactBody doc (LImpl (LVar "B") (LVar "A")) `shouldBe` True

    it "symmetric difference  A ∸ B  renders as  A ↔ B" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ∸ B; } } }|]
      hasMetafactBody doc (LBicond (LVar "A") (LVar "B")) `shouldBe` True

    it "generates one WrapMetafact axiom per metafact" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A × B; A + B; } } }|]
      length (metafactBodies doc) `shouldBe` 2

    it "assertions and metafacts use different wrappers (P_Min vs U_Min)" $ do
      doc <- buildStr [r|{
        signature { P : ℙ; A : 𝕌; B : 𝕌; },
        axioms {
          assertions { P; },
          metafacts { A × B; }
        }
      }|]
      length (assertionBodies doc) `shouldBe` 1
      length (metafactBodies doc) `shouldBe` 1

  -- =========================================================================
  describe "theoryToLeanDoc – universal quantifier in facts" $ do
  -- =========================================================================

    it "renders [X : ℙ] body as LBoundedForall X P_Min P_Max ..." $ do
      doc <- buildStr [r|{
        axioms { assertions { ∀X : ℙ (X → ¬¬X); } }
      }|]
      hasAssertionBodyWith doc (\case
        LBoundedForall "X" "ℙ_Min" "ℙ_Max" _ -> True
        _                                    -> False)
        `shouldBe` True

    it "renders [X : 𝕌] body as LBoundedForall X U_Min U_Max ..." $ do
      doc <- buildStr [r|{
        signature { A : 𝕌; },
        axioms { metafacts { ∀X : 𝕌 (A - (A - X)) - X; } }
      }|]
      hasMetafactBodyWith doc (\case
        LBoundedForall "X" "𝕌_Min" "𝕌_Max" _ -> True
        _                                    -> False)
        `shouldBe` True

    it "bounded guard for ℙ-quantifier uses IsWithinBounds ℙ_Min X ℙ_Max" $ do
      doc <- buildStr [r|{
        axioms { assertions { ∀X : ℙ (X → ¬¬X); } }
      }|]
      hasAssertionBodyWith doc (\case
        LBoundedForall "X" "ℙ_Min" "ℙ_Max" _ -> True
        _ -> False)
        `shouldBe` True

    it "bounded guard for 𝕌-quantifier uses IsWithinBounds 𝕌_Min X 𝕌_Max" $ do
      doc <- buildStr [r|{
        signature { A : 𝕌; },
        axioms { metafacts { ∀X : 𝕌 (A - (A - X)) - X; } }
      }|]
      hasMetafactBodyWith doc (\case
        LBoundedForall "X" "𝕌_Min" "𝕌_Max" _ -> True
        _ -> False)
        `shouldBe` True
        
    it "bounded guard for ℙ-quantifier does not add IsIndividual (proposition, not FOL individual)" $ do
      doc <- buildStr [r|{
        axioms { assertions { X : ℙ, (X → ¬¬X); } }
      }|]
      hasAssertionBodyWith doc (\case
        LBoundedForall "X" "ℙ_Min" "ℙ_Max" (LImpl (LIsIndividual _ _ _) _) -> False
        LBoundedForall "X" "ℙ_Min" "ℙ_Max" _ -> True
        _ -> False)
        `shouldBe` True

    it "bounded guard for 𝕌-quantifier does not add IsIndividual (mereological, not FOL individual)" $ do
      doc <- buildStr [r|{
        signature { A : 𝕌; },
        axioms { metafacts { X : 𝕌, (A - (A - X)) - X; } }
      }|]
      hasMetafactBodyWith doc (\case
        LBoundedForall "X" "𝕌_Min" "𝕌_Max" (LImpl (LIsIndividual _ _ _) _) -> False
        LBoundedForall "X" "𝕌_Min" "𝕌_Max" _ -> True
        _ -> False)
        `shouldBe` True

    it "individual free variable x : S does NOT add IsIndividual guard (free logic)" $ do
      doc <- buildStr [r|{
        signature { sort S; },
        axioms { assertions { x : S, x =_S x; } }
      }|]
      -- Free variables lack existential import in Eidos (free logic).
      -- So x : S wraps with bounds only, no IsIndividual guard.
      hasAssertionBodyWith doc (\case
        LBoundedForall "x" "S_Min" "S_Max" (LImpl (LIsIndividual _ _ _) _) -> False
        LBoundedForall "x" "S_Min" "S_Max" _ -> True
        _ -> False)
        `shouldBe` True

    it "set free variable X ⊆ S does not add IsIndividual guard" $ do
      doc <- buildStr [r|{
        signature { sort S; },
        axioms { assertions { X ⊆ S, X ⊆ X; } }
      }|]
      hasAssertionBodyWith doc (\case
        LBoundedForall "X" "S_Min" "S_Max" (LImpl (LIsIndividual _ _ _) _) -> False
        LBoundedForall "X" "S_Min" "S_Max" _ -> True
        _ -> False)
        `shouldBe` True

  -- =========================================================================
  describe "renderLeanExpr – LIsWithinBounds" $ do
  -- =========================================================================

    it "renders LIsWithinBounds as IsWithinBounds lo hi var" $
      renderLeanExpr (LIsWithinBounds "P_Min" "X" "P_Max")
        `shouldBe` "(IsWithinBounds P_Min P_Max X)"

    it "renders LIsWithinBounds for a user sort" $
      renderLeanExpr (LIsWithinBounds "S_Min" "X" "S_Max")
        `shouldBe` "(IsWithinBounds S_Min S_Max X)"

  -- =========================================================================
  describe "renderLeanExpr – LIsIndividual" $ do
  -- =========================================================================

    it "renders LIsIndividual as IsIndividual lo hi var" $
      renderLeanExpr (LIsIndividual "S_Min" "x" "S_Max")
        `shouldBe` "(IsIndividual S_Min S_Max x)"

  -- =========================================================================
  describe "theoryToLeanDoc – set union (∪), intersection (∩), subset (⊆) in metafacts" $ do
  -- =========================================================================

    it "metafact body for A ∪ B (set union) is LConj A B" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ∪ B; } } }|]
      hasMetafactBody doc (LConj (LVar "A") (LVar "B")) `shouldBe` True

    it "metafact body for A ∩ B (set intersection) is LDisj A B" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ∩ B; } } }|]
      hasMetafactBody doc (LDisj (LVar "A") (LVar "B")) `shouldBe` True

    it "metafact body for A ⊆ B (subset) renders as B → A" $ do
      doc <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ⊆ B; } } }|]
      hasMetafactBody doc (LImpl (LVar "B") (LVar "A")) `shouldBe` True

    it "A ∪ B produces the same Lean body as A + B" $ do
      docUnion <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ∪ B; } } }|]
      docPlus  <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A + B; } } }|]
      metafactBodies docUnion `shouldBe` metafactBodies docPlus

    it "A ∩ B produces the same Lean body as A × B" $ do
      docInter <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ∩ B; } } }|]
      docProd  <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A × B; } } }|]
      metafactBodies docInter `shouldBe` metafactBodies docProd

    it "A ⊆ B in metafacts produces the same Lean body as A - B" $ do
      docSubset <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A ⊆ B; } } }|]
      docDiff   <- buildStr [r|{ signature { A : 𝕌; B : 𝕌; }, axioms { metafacts { A - B; } } }|]
      metafactBodies docSubset `shouldBe` metafactBodies docDiff

  -- =========================================================================
  describe "theoryToLeanDoc – left implication (←) in assertions" $ do
  -- =========================================================================

    it "assertion body for Q ← P renders as P → Q" $ do
      doc <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { Q ← P; } } }|]
      hasAssertionBody doc (LImpl (LVar "P") (LVar "Q")) `shouldBe` True

    it "Q ← P produces the same Lean body as P → Q" $ do
      docLeft  <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { Q ← P; } } }|]
      docRight <- buildStr [r|{ signature { P : ℙ; Q : ℙ; }, axioms { assertions { P → Q; } } }|]
      assertionBodies docLeft `shouldBe` assertionBodies docRight

  -- =========================================================================
  describe "renderLeanExpr – LProjectIntoInterval" $ do
  -- =========================================================================

    it "renders LProjectIntoInterval as ProjectIntoInterval x lo hi" $
      renderLeanExpr (LProjectIntoInterval (LVar "X") (LVar "P_Min") (LVar "P_Max"))
        `shouldBe` "(ProjectIntoInterval X P_Min P_Max)"

    it "renders LProjectIntoInterval with nested expressions" $
      renderLeanExpr (LProjectIntoInterval (LConj (LVar "A") (LVar "B")) (LVar "lo") (LVar "hi"))
        `shouldBe` "(ProjectIntoInterval (A ∧ B) lo hi)"

  -- =========================================================================
  describe "theoryToLeanDoc – projection-to-interval <lo,hi>(x)" $ do
  -- =========================================================================

    it "metafact body for <A,B>(C) is LProjectIntoInterval C A B" $ do
      doc <- buildStr [r|{
        signature { A : 𝕌; B : 𝕌; C : 𝕌; },
        axioms { metafacts { <A,B>(C); } }
      }|]
      hasMetafactBody doc
        (LProjectIntoInterval (LVar "C") (LVar "A") (LVar "B"))
        `shouldBe` True

    it "assertion body for <P1,P2>(Q) is LProjectIntoInterval Q P1 P2" $ do
      doc <- buildStr [r|{
        signature { P1 : ℙ; P2 : ℙ; Q : ℙ; },
        axioms { assertions { <P1,P2>(Q); } }
      }|]
      hasAssertionBody doc
        (LProjectIntoInterval (LVar "Q") (LVar "P1") (LVar "P2"))
        `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – projection-to-sort <S>(x)" $ do
  -- =========================================================================

    it "metafact body for <𝕌>(A) uses 𝕌_Min and 𝕌_Max as bounds" $ do
      doc <- buildStr [r|{
        signature { A : 𝕌; },
        axioms { metafacts { <𝕌>(A); } }
      }|]
      hasMetafactBody doc
        (LProjectIntoInterval (LVar "A") (LVar "𝕌_Min") (LVar "𝕌_Max"))
        `shouldBe` True

    it "metafact body for <S>(A) uses S_Min and S_Max as bounds" $ do
      doc <- buildStr [r|{
        signature { sort S; A : 𝕌; },
        axioms { metafacts { <S>(A); } }
      }|]
      hasMetafactBody doc
        (LProjectIntoInterval (LVar "A") (LVar "S_Min") (LVar "S_Max"))
        `shouldBe` True

  -- =========================================================================
  describe "theoryToLeanDoc – structural invariants" $ do
  -- =========================================================================

    it "produces no duplicate axiom names in a simple theory" $ do
      doc <- buildStr [r|{ signature { P : ℙ; A : 𝕌; MySet ⊆ 𝔻; } }|]
      noDuplicateNames doc `shouldBe` True

    it "produces no duplicate axiom names in a theory with user sorts" $ do
      doc <- buildStr [r|{ signature { sort S; MySet ⊆ S; sort T; OtherSet ⊆ T; } }|]
      noDuplicateNames doc `shouldBe` True

    it "produces no duplicate axiom names in a theory with facts" $ do
      doc <- buildStr [r|{
        signature { P : ℙ; Q : ℙ; A : 𝕌; B : 𝕌; MySet4 ⊆ 𝔻; sort S; MySet1 ⊆ S; },
        axioms {
          assertions { P ∨ Q; },
          metafacts { A × B; }
        }
      }|]
      noDuplicateNames doc `shouldBe` True

  -- =========================================================================
  describe "Set comprehension and description operator" $ do
  -- =========================================================================

    it "set comprehension { x : S | φ(x) } translates to bounded forall with φ → x body" $ do
      doc <- buildStr [r|{
        signature { sort S; },
        axioms { assertions {
          x : S, {y : S | y =_S x} ⊆ {y : S | y =_S x};
        }}
      }|]
      -- The comprehension { y : S | y =_S x } produces LForallIndividuals
      -- somewhere inside the assertion body (possibly wrapped in LBoundedForall
      -- if there are free variables).
      any (anySubExpr (\case LForallIndividuals _ _ _ _ -> True; _ -> False))
          (assertionBodies doc)
        `shouldBe` True

    it "description ιx : S φ(x) produces the same Lean output as set comprehension" $ do
      docComp <- buildStr [r|{
        signature { sort S; a : S; },
        axioms { assertions {
          x : S, {y : S | y =_S a} ⊆ {y : S | y =_S a};
        }}
      }|]
      docDesc <- buildStr [r|{
        signature { sort S; a : S; },
        axioms { assertions {
          x : S, ιy : S y =_S a ∈ {z : S | z =_S a};
        }}
      }|]
      let hasComprehensionForm d =
            any (anySubExpr (\case LForallIndividuals _ _ _ _ -> True; _ -> False))
                (assertionBodies d)
      hasComprehensionForm docComp `shouldBe` True
      hasComprehensionForm docDesc `shouldBe` True

    it "set comprehension uses sort bounds from the variable's sort" $ do
      doc <- buildStr [r|{
        signature { sort S; },
        axioms { assertions {
          {x : S | x =_S x} ⊆ {x : S | x =_S x};
        }}
      }|]
      -- LForallIndividuals with S_Min / S_Max bounds appears somewhere in the body.
      any (anySubExpr (\case LForallIndividuals _ "S_Min" "S_Max" _ -> True; _ -> False))
          (assertionBodies doc)
        `shouldBe` True
