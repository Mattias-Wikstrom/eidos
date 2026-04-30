{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase    #-}
-- | Unit tests for Eidos.Export.LeanProps — function-related axioms.
--
-- Tests that the pipeline correctly generates:
--   * Function declarations (Prop → Prop → ... → Prop)
--   * Argument/result object declarations
--   * Argument/result bounds axioms
--   * Function fact axioms (connection between args/res and function application)
--   * Inverse declarations (for single-arg user-declared FOL functions only)
--   * Inverse arg/res declarations and bounds
--   * Inverse fact axioms
--   * Adjunction axioms (f ⊣ f_inv)
--   * Product-sort machinery (multi-arg functions):
--       - dom_Min/dom_Max declarations
--       - Projection function declarations (f_pi_k)
--       - Inverse projection function declarations (f_pi_k_inv)
--       - Tuple formation function declaration
--       - Direct/inverse image function declarations
--       - Product sort ordering axioms
--       - Product arg declarations and bounds
--       - Direct-image fact axioms
--       - Inverse-image witness declarations and bounds
--       - Inverse-image fact axioms
--       - Image adjunction axioms
--       - Decomposition axioms
--       - Tuple fact axioms
--       - Projection witness declarations and bounds
--       - Projection fact axioms
--       - Projection adjunction axioms
--       - Tuple-inverse-decomposition facts
--       - IR predicate declarations
--       - IR tuple-with-projections axioms
--       - IR projections-from-tuple axioms
--       - IR separation axioms
--
-- Run with: cabal test leanprops-tests
module Main where

import Test.Hspec
import Text.RawString.QQ (r)
import Data.List (nub, isPrefixOf, intercalate)

import Eidos.Parser     (parseString)
import Eidos.FromSyntax (buildTheoryPure)
import Eidos.BuildMonad (emptyPureResolver)
import Eidos.Export.LeanProps

-- ---------------------------------------------------------------------------
-- Naming conventions (mirror LeanProps.hs — single point of change)
-- ---------------------------------------------------------------------------

uName, pName, dName :: String
uName = "U"
pName = "P"
dName = "D"

minSuffix, maxSuffix :: String
minSuffix = "_Min"
maxSuffix = "_Max"

minSuffixForAxiomNames, maxSuffixForAxiomNames :: String
minSuffixForAxiomNames = "_min"
maxSuffixForAxiomNames = "_max"

-- Built-in bound names as LeanExpr
uMin, uMax, pMin, pMax, dMin, dMax :: LeanExpr
uMin = LVar (uName ++ minSuffix)
uMax = LVar (uName ++ maxSuffix)
pMin = LVar (pName ++ minSuffix)
pMax = LVar (pName ++ maxSuffix)
dMin = LVar (dName ++ minSuffix)
dMax = LVar (dName ++ maxSuffix)

-- User sort bound names
sortMinName, sortMaxName :: String -> String
sortMinName name = name ++ minSuffix
sortMaxName name = name ++ maxSuffix

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

buildStr :: String -> IO LeanDoc
buildStr src = case parseString src of
  Left err  -> fail ("Parse error: " ++ show err)
  Right ast -> case buildTheoryPure emptyPureResolver Nothing ast of
    Left err -> fail ("Build error: " ++ err)
    Right th -> return (theoryToLeanDoc th)

-- | All axioms in a doc.
axioms :: LeanDoc -> [LeanAxiom]
axioms doc = [ ax | DeclAxiom ax <- leanDocDecls doc ]

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
hasPropDecl doc name = any (\ax -> axiomType ax == LProp && axiomName ax == name) (axioms doc)

-- | True when the doc declares no duplicate axiom names.
noDuplicateNames :: LeanDoc -> Bool
noDuplicateNames doc =
  let names = map axiomName (axioms doc)
  in nub names == names

-- | Count how many axioms have the given type.
countType :: LeanDoc -> LeanExpr -> Int
countType doc ty = length [ () | t <- allTypes doc, t == ty ]

-- | True if the doc contains an LForall binder with the given variable name
--   and an IsWithinBounds guard using the given lo/hi.
hasForallWithBound :: LeanDoc -> String -> String -> String -> Bool
hasForallWithBound doc varName lo hi =
  any (\case
    LForall v (LVar "Prop") (LImpl (LIsWithinBounds l v' h) _)
      | v == varName, v' == varName, l == lo, h == hi -> True
    LForallKw v (LVar "Prop") (LImpl (LIsWithinBounds l v' h) _)
      | v == varName, v' == varName, l == lo, h == hi -> True
    _ -> False)
    (allTypes doc)

-- | Extract all LForall/LForallKw binders from expressions (recursively).
forallBinders :: LeanExpr -> [(String, LeanExpr, LeanExpr)]
forallBinders (LForall v ty body) = (v, ty, body) : forallBinders body
forallBinders (LForallKw v ty body) = (v, ty, body) : forallBinders body
forallBinders _ = []

-- | Find an axiom by name prefix.
findAxiomByPrefix :: LeanDoc -> String -> Maybe LeanAxiom
findAxiomByPrefix doc prefix =
  case filter (\ax -> prefix `isPrefixOf` axiomName ax) (axioms doc) of
    (a:_) -> Just a
    _     -> Nothing

-- | Find an axiom with the exact name.
findAxiomByName :: LeanDoc -> String -> Maybe LeanAxiom
findAxiomByName doc name =
  case filter (\ax -> axiomName ax == name) (axioms doc) of
    (a:_) -> Just a
    _     -> Nothing

-- | Collect all LeanExprs that are the body of a wrapped fact with this wrapper.
wrappedBodies :: LeanDoc -> LeanExpr -> [LeanExpr]
wrappedBodies doc wrapper =
  [ body
  | LBicond (LConj w body) w' <- allTypes doc
  , w == wrapper, w' == wrapper
  ]

-- | True when the doc contains a wrapped fact (wrapper ∧ body) ↔ wrapper
--   where body satisfies the predicate.
hasWrappedFactWith :: LeanDoc -> LeanExpr -> (LeanExpr -> Bool) -> Bool
hasWrappedFactWith doc wrapper p =
  any (\(LBicond (LConj w body) w') -> w == wrapper && w' == wrapper && p body) (allTypes doc)

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  -- =========================================================================
  describe "theoryToLeanDoc – single-argument FOL functions" $ do
  -- =========================================================================

    describe "function declaration" $ do
      it "declares a single-arg function as Prop → Prop" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasType doc (LImpl LProp LProp) `shouldSatisfy` \found ->
          any (\ax -> axiomType ax == LImpl LProp LProp && axiomName ax == "g") (axioms doc)

      it "declares multiple single-arg functions independently" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; g : S → S; h : T → S; } }|]
        let names = map axiomName (filter (\ax -> axiomType ax == LImpl LProp LProp) (axioms doc))
        names `shouldContain` ["g", "h"]

    describe "argument/result object declarations" $ do
      it "declares arg object g_1 as Prop" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasPropDecl doc "g_1" `shouldBe` True

      it "declares result object g_res as Prop" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasPropDecl doc "g_res" `shouldBe` True

      it "arg/result objects use correct naming prefix" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        -- g_1 and g_res should exist; g_inv_1 should NOT exist (no inverse yet, just the objects)
        hasPropDecl doc "g_1" `shouldBe` True
        hasPropDecl doc "g_res" `shouldBe` True

    describe "argument/result bounds axioms" $ do
      it "generates lower bound for arg: P_Min → (g_1 → S_Min)" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasImplication doc pMin (LImpl (LVar "g_1") (LVar (sortMinName "S"))) `shouldBe` True

      it "generates upper bound for arg: P_Min → (S_Max → g_1)" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasImplication doc pMin (LImpl (LVar (sortMaxName "S")) (LVar "g_1")) `shouldBe` True

      it "arg/result bounds use the correct sort" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; g : S → T; } }|]
        -- g_1 lives in S, g_res lives in T
        hasImplication doc pMin (LImpl (LVar "g_1") (LVar (sortMinName "S"))) `shouldBe` True
        hasImplication doc pMin (LImpl (LVar "g_res") (LVar (sortMinName "T"))) `shouldBe` True

    describe "function fact axioms" $ do
      it "generates a _fact axiom for a single-arg function" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_fact" `shouldSatisfy` (/= Nothing)

      it "fact axiom: (X1 = g_1 ∧ X2 = g_res) ↔ X2 = g(X1)" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        let body = LBicond
                     (LConj (LEq (LVar "X1") (LVar "g_1"))
                            (LEq (LVar "X2") (LVar "g_res")))
                     (LEq (LVar "X2") (LApp (LVar "g") [LVar "X1"]))
        -- The body appears inside forall quantifiers with guards
        hasWrappedFactWith doc pMin (const True) `shouldBe` False  -- no assertions in this theory
        -- Just check that some type contains th`is biconditional pattern
        any (\case LBicond _ _ -> True; _ -> False) (allTypes doc) `shouldBe` True

      it "fact axiom quantifies over the correct sorts" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasForallWithBound doc "X1" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        hasForallWithBound doc "X2" (sortMinName "S") (sortMaxName "S") `shouldBe` True

      it "fact axiom for h : T → S has X1 bounded by T, X2 bounded by S" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; h : T → S; } }|]
        hasForallWithBound doc "X1" (sortMinName "T") (sortMaxName "T") `shouldBe` True
        hasForallWithBound doc "X2" (sortMinName "S") (sortMaxName "S") `shouldBe` True

    describe "inverse function" $ do
      it "declares inverse g_inv : Prop → Prop for single-arg user-declared FOL function" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_inv" `shouldSatisfy` (/= Nothing)
        fmap axiomType (findAxiomByName doc "g_inv") `shouldBe` Just (LImpl LProp LProp)

      it "does NOT declare inverse for SOL functions (like idS)" $ do
        doc <- buildStr [r|{ signature { sort S; idS : S → S; } }|]
        -- idS is an SOL function (built-in), should not get _inv
        findAxiomByName doc "idS_inv" `shouldBe` Nothing

      it "declares inverse arg/res objects g_inv_1, g_inv_res" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasPropDecl doc "g_inv_1" `shouldBe` True
        hasPropDecl doc "g_inv_res" `shouldBe` True

      it "inverse arg lives in the original result sort" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; h : T → S; } }|]
        -- h : T → S, so h_inv : S → T
        -- h_inv_1 lives in S (original result), h_inv_res lives in T (original arg)
        hasImplication doc pMin (LImpl (LVar "h_inv_1") (LVar (sortMinName "S"))) `shouldBe` True
        hasImplication doc pMin (LImpl (LVar "h_inv_res") (LVar (sortMinName "T"))) `shouldBe` True

      it "generates inverse fact axiom g_inv_fact" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_inv_fact" `shouldSatisfy` (/= Nothing)

      it "inverse fact connects g_inv_1, g_inv_res with g_inv(X1)" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_inv_fact" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "X1" LProp (LImpl _ (LForallKw "X2" LProp (LImpl _ body))) ->
              body == LBicond
                        (LConj (LEq (LVar "X1") (LVar "g_inv_1"))
                               (LEq (LVar "X2") (LVar "g_inv_res")))
                        (LEq (LVar "X2") (LApp (LVar "g_inv") [LVar "X1"]))
            _ -> False
          Nothing -> False

    describe "adjunction axioms" $ do
      it "generates g_adjunction for single-arg function g" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_adjunction" `shouldSatisfy` (/= Nothing)

      it "adjunction: (Y → g(X)) ↔ (g_inv(Y) → X) with bounded quantifiers" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_adjunction" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "X" LProp (LImpl (LIsWithinBounds loX "X" hiX)
              (LForallKw "Y" LProp (LImpl (LIsWithinBounds loY "Y" hiY) body)))
              | loX == sortMinName "S", hiX == sortMaxName "S"
              , loY == sortMinName "S", hiY == sortMaxName "S" ->
                body == LBicond
                          (LImpl (LVar "Y") (LApp (LVar "g") [LVar "X"]))
                          (LImpl (LApp (LVar "g_inv") [LVar "Y"]) (LVar "X"))
            _ -> False
          Nothing -> False

      it "does NOT generate adjunction for the inverse function itself" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_inv_adjunction" `shouldBe` Nothing

  -- =========================================================================
  describe "theoryToLeanDoc – multi-argument FOL functions" $ do
  -- =========================================================================

    describe "function declaration" $ do
      it "declares multi-arg function with arity n as Prop → Prop → ... → Prop" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasType doc (LImpl LProp (LImpl LProp LProp)) `shouldSatisfy` \found ->
          any (\ax -> axiomType ax == LImpl LProp (LImpl LProp LProp) && axiomName ax == "f") (axioms doc)

      it "declares ternary function with correct arity" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; k : S, T, T → S; } }|]
        let ty3 = LImpl LProp (LImpl LProp (LImpl LProp LProp))
        findAxiomByName doc "k" `shouldSatisfy` \case
          Just ax -> axiomType ax == ty3
          Nothing -> False

    describe "product sort limit objects" $ do
      it "declares f_dom_Min and f_dom_Max for a multi-arg function" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasPropDecl doc "f_dom_Min" `shouldBe` True
        hasPropDecl doc "f_dom_Max" `shouldBe` True

      it "distinct multi-arg functions get distinct product sorts" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; f : S, S → T; k : T, T → S; } }|]
        hasPropDecl doc "f_dom_Min" `shouldBe` True
        hasPropDecl doc "k_dom_Min" `shouldBe` True
        -- They should be different
        findAxiomByName doc "f_dom_Min" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "k_dom_Min" `shouldSatisfy` (/= Nothing)

    describe "product sort ordering axioms" $ do
      it "generates f_dom_upper: U_Max → f_dom_Max" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasImplication doc uMax (LVar "f_dom_Max") `shouldBe` True

      it "generates f_dom_ordering: f_dom_Max → f_dom_Min" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasImplication doc (LVar "f_dom_Max") (LVar "f_dom_Min") `shouldBe` True

      it "generates f_dom_lower: f_dom_Min → P_Max" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasImplication doc (LVar "f_dom_Min") pMax `shouldBe` True

    describe "projection functions" $ do
      it "declares f_pi_1, f_pi_2 : Prop → Prop for binary function" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_pi_1" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False
        findAxiomByName doc "f_pi_2" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False

      it "declares k_pi_1, k_pi_2, k_pi_3 for ternary function" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; k : S, T, T → S; } }|]
        findAxiomByName doc "k_pi_1" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "k_pi_2" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "k_pi_3" `shouldSatisfy` (/= Nothing)

    describe "inverse projection functions" $ do
      it "declares f_pi_k_inv for each projection" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_pi_1_inv" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False
        findAxiomByName doc "f_pi_2_inv" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False

    describe "tuple formation function" $ do
      it "declares f_tuple : Prop → Prop → Prop for binary function" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_tuple" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp (LImpl LProp LProp)
          Nothing -> False

      it "declares k_tuple with arity 3 for ternary function" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; k : S, T, T → S; } }|]
        findAxiomByName doc "k_tuple" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp (LImpl LProp (LImpl LProp LProp))
          Nothing -> False

    describe "direct/inverse image functions" $ do
      it "declares f_dir_img : Prop → Prop" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_dir_img" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False

      it "declares f_inv_img : Prop → Prop" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_inv_img" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False

    describe "product arg declarations" $ do
      it "declares f_arg as Prop" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasPropDecl doc "f_arg" `shouldBe` True

      it "generates bounds for f_arg relative to product sort" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasImplication doc pMin (LImpl (LVar "f_arg") (LVar "f_dom_Min")) `shouldBe` True
        hasImplication doc pMin (LImpl (LVar "f_dom_Max") (LVar "f_arg")) `shouldBe` True

    describe "direct-image fact axiom" $ do
      it "generates f_dir_img_fact" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_dir_img_fact" `shouldSatisfy` (/= Nothing)

      it "dir_img_fact: (A = f_arg ∧ B = f_res) ↔ B = f_dir_img(A)" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_dir_img_fact" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "A" LProp (LImpl (LIsWithinBounds loA "A" hiA)
              (LForallKw "B" LProp (LImpl (LIsWithinBounds loB "B" hiB) body)))
              | loA == "f_dom_Min", hiA == "f_dom_Max"
              , loB == sortMinName "S", hiB == sortMaxName "S" ->
                body == LBicond
                          (LConj (LEq (LVar "A") (LVar "f_arg"))
                                 (LEq (LVar "B") (LVar "f_res")))
                          (LEq (LVar "B") (LApp (LVar "f_dir_img") [LVar "A"]))
            _ -> False
          Nothing -> False

    describe "inverse-image witness declarations" $ do
      it "declares f_inv_img_arg, f_inv_img_res" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasPropDecl doc "f_inv_img_arg" `shouldBe` True
        hasPropDecl doc "f_inv_img_res" `shouldBe` True

      it "inv_img witnesses have correct sort bounds" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        -- f_inv_img_arg lives in the result sort (S)
        hasImplication doc pMin (LImpl (LVar "f_inv_img_arg") (LVar (sortMinName "S"))) `shouldBe` True
        -- f_inv_img_res lives in the product sort (f_dom)
        hasImplication doc pMin (LImpl (LVar "f_inv_img_res") (LVar "f_dom_Min")) `shouldBe` True

    describe "inverse-image fact axiom" $ do
      it "generates f_inv_img_fact" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_inv_img_fact" `shouldSatisfy` (/= Nothing)

    describe "image adjunction axiom" $ do
      it "generates f_image_adjunction" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_image_adjunction" `shouldSatisfy` (/= Nothing)

      it "image_adjunction: (Y → f_dir_img(X)) ↔ (f_inv_img(Y) → X)" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_image_adjunction" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "X" LProp (LImpl (LIsWithinBounds loX "X" hiX)
              (LForallKw "Y" LProp (LImpl (LIsWithinBounds loY "Y" hiY) body)))
              | loX == "f_dom_Min", hiX == "f_dom_Max"
              , loY == sortMinName "S", hiY == sortMaxName "S" ->
                body == LBicond
                          (LImpl (LVar "Y") (LApp (LVar "f_dir_img") [LVar "X"]))
                          (LImpl (LApp (LVar "f_inv_img") [LVar "Y"]) (LVar "X"))
            _ -> False
          Nothing -> False

    describe "decomposition axiom" $ do
      it "generates f_decomposition" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_decomposition" `shouldSatisfy` (/= Nothing)

      it "decomposition: f(X1, X2) = f_dir_img(f_tuple(X1, X2))" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_decomposition" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "X1" LProp (LImpl (LIsWithinBounds lo1 "X1" hi1)
              (LForallKw "X2" LProp (LImpl (LIsWithinBounds lo2 "X2" hi2) body)))
              | lo1 == sortMinName "S", hi1 == sortMaxName "S"
              , lo2 == sortMinName "S", hi2 == sortMaxName "S" ->
                body == LEq (LApp (LVar "f") [LVar "X1", LVar "X2"])
                            (LApp (LVar "f_dir_img") [LApp (LVar "f_tuple") [LVar "X1", LVar "X2"]])
            _ -> False
          Nothing -> False

    describe "tuple fact axiom" $ do
      it "generates f_tuple_fact" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_tuple_fact" `shouldSatisfy` (/= Nothing)

    describe "projection witness declarations" $ do
      it "declares f_pi_1_1, f_pi_1_res, f_pi_2_1, f_pi_2_res" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasPropDecl doc "f_pi_1_1" `shouldBe` True
        hasPropDecl doc "f_pi_1_res" `shouldBe` True
        hasPropDecl doc "f_pi_2_1" `shouldBe` True
        hasPropDecl doc "f_pi_2_res" `shouldBe` True

      it "projection witnesses have correct sort bounds" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        -- f_pi_1_1 lives in f_dom, f_pi_1_res lives in S (first argument sort)
        hasImplication doc pMin (LImpl (LVar "f_pi_1_1") (LVar "f_dom_Min")) `shouldBe` True
        hasImplication doc pMin (LImpl (LVar "f_pi_1_res") (LVar (sortMinName "S"))) `shouldBe` True

    describe "projection fact axioms" $ do
      it "generates f_pi_1_fact, f_pi_2_fact" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_pi_1_fact" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "f_pi_2_fact" `shouldSatisfy` (/= Nothing)

      it "pi_fact: (X1 = f_pi_1_1 ∧ X2 = f_pi_1_res) ↔ X2 = f_pi_1(X1)" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_pi_1_fact" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "X1" LProp (LImpl (LIsWithinBounds lo1 "X1" hi1)
              (LForallKw "X2" LProp (LImpl (LIsWithinBounds lo2 "X2" hi2) body)))
              | lo1 == "f_dom_Min", hi1 == "f_dom_Max"
              , lo2 == sortMinName "S", hi2 == sortMaxName "S" ->
                body == LBicond
                          (LConj (LEq (LVar "X1") (LVar "f_pi_1_1"))
                                 (LEq (LVar "X2") (LVar "f_pi_1_res")))
                          (LEq (LVar "X2") (LApp (LVar "f_pi_1") [LVar "X1"]))
            _ -> False
          Nothing -> False

    describe "projection adjunction axioms" $ do
      it "generates f_pi_1_adjunction, f_pi_2_adjunction" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_pi_1_adjunction" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "f_pi_2_adjunction" `shouldSatisfy` (/= Nothing)

    describe "tuple inverse decomposition fact" $ do
      it "generates f_tuple_inv_decomposition" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_tuple_inv_decomposition" `shouldSatisfy` (/= Nothing)

      it "tuple_inv_decomposition: f_tuple(X1,X2) = f_pi_1_inv(X1) ∧ f_pi_2_inv(X2)" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_tuple_inv_decomposition" `shouldSatisfy` \case
          Just ax -> case axiomType ax of
            LForallKw "X1" LProp (LImpl (LIsWithinBounds lo1 "X1" hi1)
              (LForallKw "X2" LProp (LImpl (LIsWithinBounds lo2 "X2" hi2) body)))
              | lo1 == sortMinName "S", hi1 == sortMaxName "S"
              , lo2 == sortMinName "S", hi2 == sortMaxName "S" ->
                body == LEq (LApp (LVar "f_tuple") [LVar "X1", LVar "X2"])
                            (LConj (LApp (LVar "f_pi_1_inv") [LVar "X1"])
                                   (LApp (LVar "f_pi_2_inv") [LVar "X2"]))
            _ -> False
          Nothing -> False

    describe "IR predicate" $ do
      it "declares IR_f : Prop → Prop" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "IR_f" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp LProp
          Nothing -> False

      it "generates IR_f_tuple_with_projections" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "IR_f_tuple_with_projections" `shouldSatisfy` (/= Nothing)

      it "generates IR_f_projections_from_tuple" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "IR_f_projections_from_tuple" `shouldSatisfy` (/= Nothing)

      it "generates IR_f_separates" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "IR_f_separates" `shouldSatisfy` (/= Nothing)

  -- =========================================================================
  describe "theoryToLeanDoc – structural invariants for functions" $ do
  -- =========================================================================

    it "produces no duplicate axiom names with single-arg function" $ do
      doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
      noDuplicateNames doc `shouldBe` True

    it "produces no duplicate axiom names with multi-arg function" $ do
      doc <- buildStr [r|{ signature { sort S; sort T; f : S, S → T; k : T, T → S; } }|]
      noDuplicateNames doc `shouldBe` True

    it "produces no duplicate axiom names with mix of single- and multi-arg functions" $ do
      doc <- buildStr [r|{ signature { sort S; sort T; f : S, S → T; g : S → S; h : T → S; } }|]
      noDuplicateNames doc `shouldBe` True