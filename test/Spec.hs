module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)

import Eidos.AST
import Eidos.Parser (parseString)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

mustParse :: String -> IO TheoryDecl
mustParse src = case parseString src of
  Left err -> fail $ "Unexpected parse failure:\n" ++ errorBundlePretty err
  Right td -> return td

mustFail :: String -> IO ()
mustFail src = case parseString src of
  Left  _  -> return ()
  Right _  -> fail $ "Expected parse failure but succeeded for:\n" ++ src

wrap :: String -> String
wrap inner = "{\n" ++ inner ++ "\n}"

wrapSig :: String -> String
wrapSig items = wrap ("signature {\n" ++ items ++ "\n}")

wrapAssert :: String -> String
wrapAssert stmts = wrap ("axioms { assertions {\n" ++ stmts ++ "\n} }")

wrapFacts :: String -> String
wrapFacts stmts = wrap ("axioms { facts {\n" ++ stmts ++ "\n} }")

getSigItems :: TheoryDecl -> [SignatureItem]
getSigItems td = go (sections (theoryBody td))
  where
    go (SectionSignature (SignatureSection is) : _) = is
    go (_:rest) = go rest
    go [] = []

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  -- -------------------------------------------------------------------------
  -- 1. Empty and minimal theories
  -- -------------------------------------------------------------------------
  describe "Empty and minimal theories" $ do

    it "parses empty theory" $
      mustParse "{}" >>= \td ->
        sections (theoryBody td) `shouldBe` []

    it "parses theory with empty sections" $
      mustParse "{ signature {}, axioms {}, subtheories {} }" >>= \_ -> return ()

    it "allows trailing comma in axioms" $
      mustParse "{ axioms { assertions {}, facts {}, }, subtheories {} }" >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 2. Sorts
  -- -------------------------------------------------------------------------
  describe "Sorts" $ do

    it "parses simple sort" $ do
      td <- mustParse (wrapSig "sort S;")
      let [SigSimpleSort (SimpleSortDeclaration n)] = getSigItems td
      n `shouldBe` "S"

    it "parses multiple sorts" $ do
      td <- mustParse (wrapSig "sort A; sort B; sort C;")
      let is = getSigItems td
      length is `shouldBe` 3
      let names = [n | SigSimpleSort (SimpleSortDeclaration n) <- is]
      names `shouldBe` ["A", "B", "C"]

    it "parses subsort declaration" $ do
      td <- mustParse (wrapSig "T subsort S;")
      let [SigRelationalSort r] = getSigItems td
      relSortName r `shouldBe` "T"
      relSortRel  r `shouldBe` "subsort"
      sortConstant (sortRef (relSortSort r)) `shouldBe` "S"

    it "parses quotient sort declaration" $ do
      td <- mustParse (wrapSig "Q quotient S;")
      let [SigRelationalSort r] = getSigItems td
      relSortRel r `shouldBe` "quotient"

    it "parses subquotient sort declaration" $ do
      td <- mustParse (wrapSig "SQ subquotient S;")
      let [SigRelationalSort r] = getSigItems td
      relSortRel r `shouldBe` "subquotient"

    it "parses built-in sort ℙ (unicode)" $
      mustParse (wrapSig "P : ℙ;") >>= \_ -> return ()

    it "parses built-in sort Prop (ASCII)" $
      mustParse (wrapSig "P : Prop;") >>= \_ -> return ()

    it "parses qualified sort in subsort" $
      mustParse (wrapSig "T subsort sub.S;") >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 3. Signature — individuals, sets, functions, relations
  -- -------------------------------------------------------------------------
  describe "Signature declarations" $ do

    it "parses individual declaration" $ do
      td <- mustParse (wrapSig "a : S;")
      let [SigIndividual (IndividualDeclaration n s)] = getSigItems td
      n `shouldBe` "a"
      sortConstant (sortRef s) `shouldBe` "S"

    it "parses individual with domain sort 𝔻" $
      mustParse (wrapSig "g : 𝔻;") >>= \_ -> return ()

    it "parses set declaration" $ do
      td <- mustParse (wrapSig "mySet ⊆ S;")
      let [SigSet (SetDeclaration n ds)] = getSigItems td
      n `shouldBe` "mySet"
      sortConstant (sortRef (head ds)) `shouldBe` "S"

    it "parses binary relation (set) declaration" $ do
      td <- mustParse (wrapSig "r ⊆ S, T;")
      let [SigSet (SetDeclaration _ ds)] = getSigItems td
      length ds `shouldBe` 2
      sortConstant (sortRef (ds !! 0)) `shouldBe` "S"
      sortConstant (sortRef (ds !! 1)) `shouldBe` "T"

    it "parses ternary relation declaration" $
      mustParse (wrapSig "r2 ⊆ S, B, B;") >>= \_ -> return ()

    it "parses unary function declaration" $ do
      td <- mustParse (wrapSig "inv : 𝔻 → 𝔻;")
      let [SigFunction (FunctionDeclaration n ds _)] = getSigItems td
      n `shouldBe` "inv"
      length ds `shouldBe` 1

    it "parses binary function declaration" $ do
      td <- mustParse (wrapSig "f : S, T → U;")
      let [SigFunction (FunctionDeclaration _ ds cd)] = getSigItems td
      length ds `shouldBe` 2
      sortConstant (sortRef cd) `shouldBe` "U"

    it "parses SOL function declaration" $
      mustParse (wrapSig "G : S, B, B → C;") >>= \_ -> return ()

    it "parses SOL relation with ℙ codomain" $
      mustParse (wrapSig "Pred : A, B → ℙ;") >>= \_ -> return ()

    it "parses SOL relation with Prop codomain" $
      mustParse (wrapSig "Pred2 : A, B → Prop;") >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 4. Assertions — propositions
  -- -------------------------------------------------------------------------
  describe "Assertions" $ do

    it "parses simple equality"     $ mustParse (wrapAssert "a = b;")     >>= \_ -> return ()
    it "parses sorted equality"     $ mustParse (wrapAssert "[x:S][y:S] f(x,y) =_S f(y,x);") >>= \_ -> return ()
    it "parses SOL equality"        $ mustParse (wrapAssert "A =^S B;")   >>= \_ -> return ()
    it "parses negation"            $ mustParse (wrapAssert "¬⊥;")        >>= \_ -> return ()
    it "parses double negation"     $ mustParse (wrapAssert "¬¬P;")       >>= \_ -> return ()
    it "parses top and bottom"      $ mustParse (wrapAssert "⊥ → ⊤;")    >>= \_ -> return ()
    it "parses conjunction"         $ mustParse (wrapAssert "P ∧ Q;")     >>= \_ -> return ()
    it "parses disjunction"         $ mustParse (wrapAssert "P ∨ Q;")     >>= \_ -> return ()
    it "parses biconditional"       $ mustParse (wrapAssert "P ↔ Q;")     >>= \_ -> return ()
    it "parses reverse implication" $ mustParse (wrapAssert "P ← Q;")     >>= \_ -> return ()
    it "parses chained implication" $ mustParse (wrapAssert "P → Q → R;") >>= \_ -> return ()
    it "parses mixed connectives"   $ mustParse (wrapAssert "(P ∨ Q) ∧ R → S;") >>= \_ -> return ()

    it "parses universal quantifier" $
      mustParse (wrapAssert "∀x:S x = x;") >>= \_ -> return ()

    it "parses existential quantifier" $
      mustParse (wrapAssert "∃x:S x = x;") >>= \_ -> return ()

    it "parses set quantifier ⊆" $
      mustParse (wrapAssert "∀X⊆S X = X;") >>= \_ -> return ()

    it "parses propositional quantifier ℙ" $
      mustParse (wrapAssert "∀X:ℙ (X ∨ ¬X);") >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 5. Term operations
  -- -------------------------------------------------------------------------
  describe "Term operations" $ do

    it "parses mereological plus"     $ mustParse (wrapAssert "a + b = c;")  >>= \_ -> return ()
    it "parses mereological minus"    $ mustParse (wrapAssert "a - b = c;")  >>= \_ -> return ()
    it "parses mereological times ×" $ mustParse (wrapAssert "a × b = c;")  >>= \_ -> return ()
    it "parses mereological times *" $ mustParse (wrapAssert "a * b = c;")  >>= \_ -> return ()
    it "parses dotMinus ∸"           $ mustParse (wrapAssert "a ∸ b = c;")  >>= \_ -> return ()
    it "parses impliesOp ⇒"          $ mustParse (wrapAssert "a ⇒ b = c;")  >>= \_ -> return ()
    it "parses union ∪"              $ mustParse (wrapAssert "A ∪ B = C;")  >>= \_ -> return ()
    it "parses intersection ∩"       $ mustParse (wrapAssert "A ∩ B = C;")  >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 6. Hash suffixes
  -- -------------------------------------------------------------------------
  describe "Hash suffixes" $ do

    it "parses #1, #2 argument selectors" $ do
      mustParse (wrapAssert "op#1 = x;") >>= \_ -> return ()
      mustParse (wrapAssert "op#2 = y;") >>= \_ -> return ()

    it "parses #res suffix"  $ mustParse (wrapAssert "op#res = z;") >>= \_ -> return ()
    it "parses #dom suffix"  $ mustParse (wrapAssert "f#dom = x;")  >>= \_ -> return ()
    it "parses #min / #max"  $ mustParse (wrapAssert "S#min ⊆ S#max;") >>= \_ -> return ()

    it "parses #set / #individual / #mereological / #proposition" $ do
      mustParse (wrapAssert "x#set = y#individual;") >>= \_ -> return ()
      mustParse (wrapAssert "x#mereological = y;")   >>= \_ -> return ()
      mustParse (wrapAssert "x#proposition = y;")    >>= \_ -> return ()

    it "parses #hash in metafact" $
      mustParse (wrap "axioms { metafacts { [x : D][y : D] ((op#1 ∸ x) + (op#2 ∸ y)) ⇒ (op#res ∸ op(x, y)) = 0; } }") >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 7. Projection disambiguation
  -- -------------------------------------------------------------------------
  describe "Projections" $ do

    it "parses sort projection <S>(x)"       $ mustParse (wrapAssert "<S>(x) = x;")        >>= \_ -> return ()
    it "parses qualified sort projection"    $ mustParse (wrapAssert "<sub.S>(x) = x;")    >>= \_ -> return ()
    it "parses built-in sort projection 𝔻"  $ mustParse (wrapAssert "<𝔻>(x) = x;")       >>= \_ -> return ()
    it "parses interval projection <lo,hi>" $ mustParse (wrapAssert "<lo, hi>(x) = x;")   >>= \_ -> return ()
    it "parses hash-qualified interval"     $ mustParse (wrapAssert "<S#min, S#max>(x) = x;") >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 8. Generalized sum / product
  -- -------------------------------------------------------------------------
  describe "Generalized sum and product" $ do

    it "parses Σ with bare id"     $ mustParse (wrapAssert "[y : S] Σy(y) = y;")  >>= \_ -> return ()
    it "parses Σ with var decl"    $ mustParse (wrapAssert "Σz : D (z) = z;")     >>= \_ -> return ()
    it "parses Π with bare id"     $ mustParse (wrapAssert "[y : S] Πy(y) = y;")  >>= \_ -> return ()
    it "parses Π with var decl"    $ mustParse (wrapAssert "Πz : D (z) = z;")     >>= \_ -> return ()
    it "rejects Σ with no bound var" $ mustFail (wrapAssert "Σ(x) = y;")
    it "rejects Π with no bound var" $ mustFail (wrapAssert "Π(x) = y;")

  -- -------------------------------------------------------------------------
  -- 9. Subtheories
  -- -------------------------------------------------------------------------
  describe "Subtheories" $ do

    it "parses inline body" $
      mustParse (wrap "subtheories { sub: { signature { sort A; } } }") >>= \_ -> return ()

    it "parses external ref [[name]]" $
      mustParse (wrap "subtheories { sub: [[mylib]] }") >>= \_ -> return ()

    it "parses implicit group" $
      mustParse (wrap "subtheories { implicit { sub: [[ext]] } }") >>= \_ -> return ()

    it "parses bracket qualifier [implicit]" $ do
      td <- mustParse (wrap "subtheories { [implicit] sub: [[ext]] }")
      let SectionSubtheories (SubtheoriesSection [SubtheoryEntryItem item]) =
            head (sections (theoryBody td))
      itemQualifier item `shouldBe` Just "implicit"

    it "parses bracket qualifier [named]" $ do
      td <- mustParse (wrap "subtheories { [named] sub: [[ext]] }")
      let SectionSubtheories (SubtheoriesSection [SubtheoryEntryItem item]) =
            head (sections (theoryBody td))
      itemQualifier item `shouldBe` Just "named"

    it "parses bracket qualifier [reflection]" $ do
      td <- mustParse (wrap "subtheories { [reflection] sub: [[ext]] }")
      let SectionSubtheories (SubtheoriesSection [SubtheoryEntryItem item]) =
            head (sections (theoryBody td))
      itemQualifier item `shouldBe` Just "reflection"

  -- -------------------------------------------------------------------------
  -- 10. Evaluation in theory
  -- -------------------------------------------------------------------------
  describe "Evaluation in theory" $ do

    it "parses <<th>>(expr)" $
      mustParse (wrapAssert "<<th>>(a) = b;") >>= \_ -> return ()

    it "parses <<th1.th2>>(expr)" $
      mustParse (wrapAssert "<<th1.th2>>(a) = b;") >>= \_ -> return ()

  -- -------------------------------------------------------------------------
  -- 11. Error cases
  -- -------------------------------------------------------------------------
  describe "Error cases" $ do

    it "rejects missing colon in individual" $
      mustFail (wrapSig "a S;")

    it "rejects missing semicolon in function" $
      mustFail (wrapSig "f : S → T")

    it "rejects arrow with no codomain" $
      mustFail (wrapSig "f : S → ;")

    it "rejects malformed subsort" $
      mustFail (wrapSig "T subsort ;")

    it "rejects semicolon alone as signature item" $
      mustFail (wrapSig ";")

    it "rejects structural keyword 'sort' as term" $
      mustFail (wrapAssert "sort = x;")

  -- -------------------------------------------------------------------------
  -- 12. Integration: monoid theory
  -- -------------------------------------------------------------------------
  describe "Integration" $ do

    it "parses a full monoid theory" $ do
      let src = "{\
        \  signature {\
        \    sort D;\
        \    n : D;\
        \    op : D, D → D;\
        \  },\
        \  axioms {\
        \    facts {\
        \      [x : D] op(n, x) =_D x;\
        \      [x : D] op(x, n) =_D x;\
        \      [x : D][y : D][z : D] op(x, op(y, z)) =_D op(op(x, y), z);\
        \    }\
        \  }\
        \}"
      mustParse src >>= \_ -> return ()

    it "parses a complex axiom block" $ do
      let src = "{ axioms { assertions {\
        \  [x : sub.S]∀z : S ∃y : S (y ⊆ y)↔((x ⊆ y)→((z ⊆ y)←((y ⊆ y)∨(y ⊆ y))));\
        \  [x : S][y : S] f(y, x) =_S f(x, y);\
        \  ⊥ ∨ ¬sub.⊤;\
        \} } }"
      mustParse src >>= \_ -> return ()
