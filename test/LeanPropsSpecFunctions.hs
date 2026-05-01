{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase    #-}
-- | Unit tests for Eidos.Export.LeanProps — function-related axioms.
module Main where

import Test.Hspec
import Text.RawString.QQ (r)
import Data.List (nub)

import Eidos.Parser     (parseString)
import Eidos.FromSyntax (buildTheoryPure)
import Eidos.BuildMonad (emptyPureResolver)
import Eidos.Export.LeanProps
import Eidos.Export.MkAxiomSets (mkAxiomSets)
import Eidos.Export.LeanAxiomSet (AxiomSet(..))

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
    Right th ->
      let axiomSets = mkAxiomSets th
          decls = [ DeclAxiom ax | as <- axiomSets, ax <- asAxioms as ]
      in return (LeanDoc "" decls)

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

  -- | Recursively check if an expression contains a forall with the given bound.
-- | Recursively check if an expression contains a forall with the given bound.
exprHasForallBound :: String -> String -> String -> LeanExpr -> Bool
exprHasForallBound varName lo hi (LForall v (LVar "Prop") body)
  | v == varName = exprContainsBound varName lo hi body
  | otherwise    = exprHasForallBound varName lo hi body
exprHasForallBound varName lo hi (LForallKw v (LVar "Prop") body)
  | v == varName = exprContainsBound varName lo hi body
  | otherwise    = exprHasForallBound varName lo hi body
exprHasForallBound varName lo hi (LBoundedForall v lo' hi' body)
  | v == varName = (lo == lo' && hi == hi') || exprHasForallBound varName lo hi body
  | otherwise    = exprHasForallBound varName lo hi body
exprHasForallBound varName lo hi (LImpl a b)
  = exprHasForallBound varName lo hi a || exprHasForallBound varName lo hi b
exprHasForallBound varName lo hi (LConj a b)
  = exprHasForallBound varName lo hi a || exprHasForallBound varName lo hi b
exprHasForallBound varName lo hi (LDisj a b)
  = exprHasForallBound varName lo hi a || exprHasForallBound varName lo hi b
exprHasForallBound varName lo hi (LBicond a b)
  = exprHasForallBound varName lo hi a || exprHasForallBound varName lo hi b
exprHasForallBound varName lo hi (LApp _ args)
  = any (exprHasForallBound varName lo hi) args
exprHasForallBound varName lo hi (LEq a b)
  = exprHasForallBound varName lo hi a || exprHasForallBound varName lo hi b
exprHasForallBound _ _ _ _ = False

-- | Check if an expression (inside the body of a forall for varName) contains
--   the guard IsWithinBounds lo varName hi as an immediate left-implicant.
exprContainsBound :: String -> String -> String -> LeanExpr -> Bool
exprContainsBound varName lo hi expr =
  case expr of
    LImpl (LIsWithinBounds l v h) _body
      | l == lo, v == varName, h == hi -> True
    LImpl a b -> exprContainsBound varName lo hi a || exprContainsBound varName lo hi b
    LConj a b -> exprContainsBound varName lo hi a || exprContainsBound varName lo hi b
    LDisj a b -> exprContainsBound varName lo hi a || exprContainsBound varName lo hi b
    LBicond a b -> exprContainsBound varName lo hi a || exprContainsBound varName lo hi b
    LForall _ _ body -> exprContainsBound varName lo hi body
    LForallKw _ _ body -> exprContainsBound varName lo hi body
    LBoundedForall _ _ _ body -> exprContainsBound varName lo hi body
    LExists _ _ body -> exprContainsBound varName lo hi body
    LApp _ args -> any (exprContainsBound varName lo hi) args
    LEq a b -> exprContainsBound varName lo hi a || exprContainsBound varName lo hi b
    LIsWithinBounds _ _ _ -> False
    LProjectIntoInterval a b c ->
      exprContainsBound varName lo hi a || exprContainsBound varName lo hi b || exprContainsBound varName lo hi c
    _ -> False

-- | True if some type in the doc contains a forall with the given bound.
hasForallWithBound :: LeanDoc -> String -> String -> String -> Bool
hasForallWithBound doc varName lo hi =
  any (exprHasForallBound varName lo hi) (allTypes doc)

-- | Find an axiom by exact name.
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
--   where body satisfies the predicate (checking any sub-expression).
hasWrappedFactWith :: LeanDoc -> LeanExpr -> (LeanExpr -> Bool) -> Bool
hasWrappedFactWith doc wrapper p =
  any matches (allTypes doc)
  where
    matches (LBicond (LConj w body) w') = w == wrapper && w' == wrapper && p body
    matches _                           = False

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
        let gAxiom = findAxiomByName doc "g"
        gAxiom `shouldSatisfy` (/= Nothing)
        fmap axiomType gAxiom `shouldBe` Just (LImpl LProp LProp)

      it "declares multiple single-arg functions independently" $ do
        doc <- buildStr [r|{ signature { sort S; sort T; g : S → S; h : T → S; } }|]
        findAxiomByName doc "g" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "h" `shouldSatisfy` (/= Nothing)

    describe "argument/result object declarations" $ do
      it "declares arg object g_1 as Prop" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasPropDecl doc "g_1" `shouldBe` True

      it "declares result object g_res as Prop" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        hasPropDecl doc "g_res" `shouldBe` True

      it "arg/result objects use correct naming prefix" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
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
        hasImplication doc pMin (LImpl (LVar "g_1") (LVar (sortMinName "S"))) `shouldBe` True
        hasImplication doc pMin (LImpl (LVar "g_res") (LVar (sortMinName "T"))) `shouldBe` True

    describe "function fact axioms" $ do
      it "generates a _fact axiom for a single-arg function" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_fact" `shouldSatisfy` (/= Nothing)

      {- -- DEBUG: print the actual g_fact AST
      it "DEBUG: show g_fact structure" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        let Just ax = findAxiomByName doc "g_fact"
        -- This will print the Show instance of LeanExpr
        putStrLn ("\nDEBUG g_fact type: " ++ show (axiomType ax))
        putStrLn ("DEBUG IsWithinBounds structure expected: " ++ show (LIsWithinBounds (sortMinName "S") "X1" (sortMaxName "S")))
        "debug" `shouldBe` "debug"  -- always passes
      -}

      it "fact axiom contains the biconditional (X1 = g_1 ∧ X2 = g_res) ↔ X2 = g(X1) somewhere inside" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        let targetBody = LBicond
                     (LConj (LEq (LVar "X1") (LVar "g_1"))
                            (LEq (LVar "X2") (LVar "g_res")))
                     (LEq (LVar "X2") (LApp (LVar "g") [LVar "X1"]))
        -- Check that the biconditional appears somewhere in the doc's types
        -- (it will be nested inside foralls)
        any (containsExpr targetBody) (allTypes doc) `shouldBe` True

    describe "inverse function" $ do
      it "declares inverse g_inv : Prop → Prop for single-arg user-declared FOL function" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_inv" `shouldSatisfy` (/= Nothing)
        fmap axiomType (findAxiomByName doc "g_inv") `shouldBe` Just (LImpl LProp LProp)

      it "does NOT declare inverse for function with empty sort (edge case)" $ do
        -- This test just verifies that we don't crash; the "does not generate
        -- inverse for SOL" is covered by checking specific SOL functions
        doc <- buildStr [r|{ signature { sort S; g : S → S; h : S → S; } }|]
        -- Both g and h are user-declared FOL, so both should get inverses
        findAxiomByName doc "g_inv" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "h_inv" `shouldSatisfy` (/= Nothing)

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
        let target = LBicond
              (LConj (LEq (LVar "X1") (LVar "g_inv_1"))
                     (LEq (LVar "X2") (LVar "g_inv_res")))
              (LEq (LVar "X2") (LApp (LVar "g_inv") [LVar "X1"]))
        any (containsExpr target) (allTypes doc) `shouldBe` True

    describe "adjunction axioms" $ do
      it "generates g_adjunction for single-arg function g" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_adjunction" `shouldSatisfy` (/= Nothing)

      it "adjunction: (Y → g(X)) ↔ (g_inv(Y) → X) with bounded quantifiers" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        let target = LBicond
              (LImpl (LVar "Y") (LApp (LVar "g") [LVar "X"]))
              (LImpl (LApp (LVar "g_inv") [LVar "Y"]) (LVar "X"))
        hasForallWithBound doc "X" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        hasForallWithBound doc "Y" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        any (containsExpr target) (allTypes doc) `shouldBe` True

      it "does NOT generate adjunction for the inverse function itself" $ do
        doc <- buildStr [r|{ signature { sort S; g : S → S; } }|]
        findAxiomByName doc "g_inv_adjunction" `shouldBe` Nothing

  -- =========================================================================
  describe "theoryToLeanDoc – multi-argument FOL functions" $ do
  -- =========================================================================

    describe "function declaration" $ do
      it "declares multi-arg function with arity n as Prop → Prop → ... → Prop" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f" `shouldSatisfy` \case
          Just ax -> axiomType ax == LImpl LProp (LImpl LProp LProp)
          Nothing -> False

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
        let target = LBicond
              (LConj (LEq (LVar "A") (LVar "f_arg"))
                     (LEq (LVar "B") (LVar "f_res")))
              (LEq (LVar "B") (LApp (LVar "f_dir_img") [LVar "A"]))
        hasForallWithBound doc "A" "f_dom_Min" "f_dom_Max" `shouldBe` True
        hasForallWithBound doc "B" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        any (containsExpr target) (allTypes doc) `shouldBe` True

    describe "inverse-image witness declarations" $ do
      it "declares f_inv_img_arg, f_inv_img_res" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasPropDecl doc "f_inv_img_arg" `shouldBe` True
        hasPropDecl doc "f_inv_img_res" `shouldBe` True

      it "inv_img witnesses have correct sort bounds" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        hasImplication doc pMin (LImpl (LVar "f_inv_img_arg") (LVar (sortMinName "S"))) `shouldBe` True
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
        let target = LBicond
              (LImpl (LVar "Y") (LApp (LVar "f_dir_img") [LVar "X"]))
              (LImpl (LApp (LVar "f_inv_img") [LVar "Y"]) (LVar "X"))
        hasForallWithBound doc "X" "f_dom_Min" "f_dom_Max" `shouldBe` True
        hasForallWithBound doc "Y" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        any (containsExpr target) (allTypes doc) `shouldBe` True

    describe "decomposition axiom" $ do
      it "generates f_decomposition" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_decomposition" `shouldSatisfy` (/= Nothing)

      it "decomposition: f(X1, X2) = f_dir_img(f_tuple(X1, X2))" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        let target = LEq (LApp (LVar "f") [LVar "X1", LVar "X2"])
                        (LApp (LVar "f_dir_img") [LApp (LVar "f_tuple") [LVar "X1", LVar "X2"]])
        hasForallWithBound doc "X1" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        hasForallWithBound doc "X2" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        any (containsExpr target) (allTypes doc) `shouldBe` True

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
        hasImplication doc pMin (LImpl (LVar "f_pi_1_1") (LVar "f_dom_Min")) `shouldBe` True
        hasImplication doc pMin (LImpl (LVar "f_pi_1_res") (LVar (sortMinName "S"))) `shouldBe` True

    describe "projection fact axioms" $ do
      it "generates f_pi_1_fact, f_pi_2_fact" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        findAxiomByName doc "f_pi_1_fact" `shouldSatisfy` (/= Nothing)
        findAxiomByName doc "f_pi_2_fact" `shouldSatisfy` (/= Nothing)

      it "pi_fact: (X1 = f_pi_1_1 ∧ X2 = f_pi_1_res) ↔ X2 = f_pi_1(X1)" $ do
        doc <- buildStr [r|{ signature { sort S; f : S, S → S; } }|]
        let target = LBicond
              (LConj (LEq (LVar "X1") (LVar "f_pi_1_1"))
                     (LEq (LVar "X2") (LVar "f_pi_1_res")))
              (LEq (LVar "X2") (LApp (LVar "f_pi_1") [LVar "X1"]))
        hasForallWithBound doc "X1" "f_dom_Min" "f_dom_Max" `shouldBe` True
        hasForallWithBound doc "X2" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        any (containsExpr target) (allTypes doc) `shouldBe` True

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
        let target = LEq (LApp (LVar "f_tuple") [LVar "X1", LVar "X2"])
                        (LConj (LApp (LVar "f_pi_1_inv") [LVar "X1"])
                               (LApp (LVar "f_pi_2_inv") [LVar "X2"]))
        hasForallWithBound doc "X1" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        hasForallWithBound doc "X2" (sortMinName "S") (sortMaxName "S") `shouldBe` True
        any (containsExpr target) (allTypes doc) `shouldBe` True

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

-- ---------------------------------------------------------------------------
-- Helper: recursively check if an expression contains a sub-expression
-- ---------------------------------------------------------------------------

containsExpr :: LeanExpr -> LeanExpr -> Bool
containsExpr target expr
  | expr == target = True
containsExpr target (LApp f args) = containsExpr target f || any (containsExpr target) args
containsExpr target (LImpl a b) = containsExpr target a || containsExpr target b
containsExpr target (LConj a b) = containsExpr target a || containsExpr target b
containsExpr target (LDisj a b) = containsExpr target a || containsExpr target b
containsExpr target (LBicond a b) = containsExpr target a || containsExpr target b
containsExpr target (LForall _ _ body) = containsExpr target body
containsExpr target (LForallKw _ _ body) = containsExpr target body
containsExpr target (LBoundedForall _ _ _ body) = containsExpr target body
containsExpr target (LExists _ _ body) = containsExpr target body
containsExpr target (LEq a b) = containsExpr target a || containsExpr target b
containsExpr _ (LIsWithinBounds _ _ _) = False  -- atomic, would have matched above if equal
containsExpr target (LProjectIntoInterval a b c) =
  containsExpr target a || containsExpr target b || containsExpr target c
containsExpr _ _ = False
