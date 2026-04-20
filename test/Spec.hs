{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)

import Eidos.Parser (parseString)
import Eidos.FromSyntax (buildTheory)
import Eidos.Pretty (prettyTheoryDecl)
import Eidos.AST
import qualified Eidos.AST as AST
import Eidos.IR
import qualified Eidos.IR as IR
import Text.RawString.QQ (r)

main :: IO ()
main = hspec $ do
  describe "Parser" $ do
    describe "Basic syntax" $ do
      it "parses an empty theory" $
        parseString "{}" `shouldSatisfy` isRight
      
      it "parses a theory with signature section" $
        parseString "{ signature { } }" `shouldSatisfy` isRight
      
      it "parses a theory with axioms section" $
        parseString "{ axioms { } }" `shouldSatisfy` isRight
      
      it "parses a theory with subtheories section" $
        parseString "{ subtheories { } }" `shouldSatisfy` isRight

    describe "Signature items" $ do
      it "parses a simple sort declaration" $ do
        let input = "{ signature { sort S; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right (TheoryDecl body) -> do
            let sections = AST.sections body
            sections `shouldBe` [SectionSignature (SignatureSection [SigSimpleSort (SimpleSortDeclaration "S")])]
      
      it "parses multiple sorts" $
        parseString "{ signature { sort A; sort B; sort C; } }" `shouldSatisfy` isRight
      
      it "parses a subsort declaration" $
        parseString "{ signature { sort S; T subsort S; } }" `shouldSatisfy` isRight
      
      it "parses a quotient declaration" $
        parseString "{ signature { sort S; T quotient S; } }" `shouldSatisfy` isRight
      
      it "parses a subquotient declaration" $
        parseString "{ signature { sort S; T subquotient S; } }" `shouldSatisfy` isRight
      
      it "parses a function declaration" $
        parseString "{ signature { f : S, T → U; } }" `shouldSatisfy` isRight
      
      it "parses a unary function declaration" $
        parseString "{ signature { f : S → T; } }" `shouldSatisfy` isRight
      
      it "parses a relation declaration" $
        parseString "{ signature { r : S, T; } }" `shouldSatisfy` isRight
      
      it "parses an individual declaration" $
        parseString "{ signature { x : S; } }" `shouldSatisfy` isRight
      
      it "parses a set declaration" $
        parseString "{ signature { mySet ⊆ S; } }" `shouldSatisfy` isRight
      
      it "parses a multi-arity set declaration" $
        parseString "{ signature { mySet ⊆ S, T, U; } }" `shouldSatisfy` isRight

    describe "Axioms" $ do
      it "parses assertions section" $
        parseString "{ axioms { assertions { ⊤; } } }" `shouldSatisfy` isRight
      
      it "parses facts section" $
        parseString "{ axioms { facts { ⊤; } } }" `shouldSatisfy` isRight
      
      it "parses metafacts section" $
        parseString "{ axioms { metafacts { ⊤; } } }" `shouldSatisfy` isRight
      
      it "parses bare axioms" $
        parseString "{ assertions { ⊤; } }" `shouldSatisfy` isRight
      
      it "parses quantified formulas" $
        parseString "{ axioms { assertions { ∀x:S x =_S x; } } }" `shouldSatisfy` isRight
      
      it "parses formulas with connectives" $
        parseString "{ axioms { assertions { P → Q ∧ R; } } }" `shouldSatisfy` isRight

  describe "Subtheories" $ do
    it "parses implicit subtheory block" $
      parseString "{ subtheories { implicit { { signature { sort Q; } } } } }" `shouldSatisfy` isRight
    
    it "parses named subtheory block" $
      parseString "{ subtheories { named { sub: [[ext]] } } }" `shouldSatisfy` isRight
    
    it "parses reflection subtheory block" $
      parseString "{ subtheories { reflection { sub2: { signature { sort Z; } } } } }" `shouldSatisfy` isRight
    
    it "parses multiple subtheories in implicit block" $ do
      let input = "{ subtheories { implicit { { signature { sort Q; } } { signature { sort R; } } } } }"
      parseString input `shouldSatisfy` isRight
    
    it "parses multiple subtheories in named block" $ do
      let input = "{ subtheories { named { sub1: [[ext1]] sub2: [[ext2]] } } }"
      parseString input `shouldSatisfy` isRight
    
    it "parses mixed subtheory blocks" $ do
      let input = "{ subtheories { implicit { { signature { sort Q; } } } named { sub: [[ext]] } reflection { sub2: { signature { sort Z; } } } } }"
      parseString input `shouldSatisfy` isRight
    
    it "parses subtheory with inline body" $ do
      let input = "{ subtheories { implicit { { signature { sort Q; } } } } }"
      parseString input `shouldSatisfy` isRight
    
    it "parses subtheory with external reference" $ do
      let input = "{ subtheories { named { sub: [[external.theory]] } } }"
      parseString input `shouldSatisfy` isRight
    
    it "parses complete example from documentation" $ do
      let input = [r|{
            signature {
                sort S;
                sort MySort;
                sort B;
                sort E;
                A subsort E;
                C subquotient B;
                D quotient B;
                f : S, S → B;
                g : 𝔻;
                p ⊆ 𝔻;
                r ⊆ S, B;
                r2 ⊆ S, B, B;
                d : S, B → C;
                G : S, B, B → C;
            },
            axioms {
                assertions {
                    [x : sub.S]∀z : S ∃y : S (y ⊆ y)↔((x ⊆ y)→((z ⊆ y)←((y ⊆ y)∨(y ⊆ y))));
                    [x : sub.S][y : sub.S](y ⊆ y)↔((y ⊆ <<sub>>(∃y : S y))→((f(y, y) ⊆ f(f(x, x), y))←((y ⊆ y)∨(y ⊆ y))));
                    [x : Q][y ⊆ Q](y ⊆ y)↔(y = y);
                    [x : S][y : S] f(y, x) =_S f(x, y);
                    ⊥ ∨ ¬sub.⊤;
                    [y : S] (f(f(y, y), y) ⊆ f(f(y, y), Σy(y)));
                    [x : S] f(x, x)=sub.h(x);
                    ¬⊥;
                    [x : S] ⊥ ∨ ¬x⊆x ∨ x≤x ∧ ¬sub.h(x)=sub.h(x) ∧ ¬sub.h(x)=sub.h(x);
                },
                facts {
                },
                metafacts {
                }
            },
            subtheories {
                implicit {
                    {
                        signature {
                            sort Q;
                        }
                    }
                },
                named {
                    sub: [[ext]]
                },
                reflection {
                    sub2: {
                        signature {
                            sort Z;
                            a : Z;
                            F : Z, Z → Z;
                        },
                        axioms {
                            assertions {
                                a = F(a, a + a);
                            }
                        }
                    }
                }
            }
        }|]

      parseString input `shouldSatisfy` isRight

    describe "Terms" $ do
      it "parses singleton set" $
        parseString "{ axioms { assertions { {x} ⊆ S; } } }" `shouldSatisfy` isRight
      
      it "parses sort projection" $
        parseString "{ axioms { assertions { <S>(x) =_S x; } } }" `shouldSatisfy` isRight
      
      it "parses interval projection" $
        parseString "{ axioms { assertions { <a, b>(x) ⊆ S; } } }" `shouldSatisfy` isRight
      
      it "parses evaluation in theory" $
        parseString "{ axioms { assertions { <<Sub>>(⊤); } } }" `shouldSatisfy` isRight
      
      it "parses generalized sum" $
        parseString "{ axioms { assertions { Σx:S(x); } } }" `shouldSatisfy` isRight
      
      it "parses generalized product" $
        parseString "{ axioms { assertions { Πx:S(x); } } }" `shouldSatisfy` isRight

      it "builds IR for theory with sort" $ do
        let input = "{ signature { sort S; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let sortNames = [ IR.sortName s | EntitySort s <- objects ]
              -- Should contain our new sort S (along with built-ins)
              sortNames `shouldContain` ["S"]
              -- Should also have built-in sorts
              sortNames `shouldContain` ["𝕌", "𝔻", "ℙ"]
      
      it "builds IR for theory with multiple sorts" $ do
        let input = "{ signature { sort A; sort B; sort C; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let sorts = [ IR.sortName s | EntitySort s <- objects ]
              all (`elem` sorts) ["A", "B", "C"] `shouldBe` True
      
      it "builds IR for theory with function" $ do
        let input = "{ signature { sort S; sort T; f : S → T; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let functionNames = [ IR.funcName f | EntityFunction f <- objects ]
              functionNames `shouldContain` ["f"]
      
      it "builds IR for theory with individual" $ do
        let input = "{ signature { sort S; x : S; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let individuals = [ IR.mereoName m | EntityMereological m <- objects
                                , IR.mereoKind m == MereologicalEntityKindIndividual ]
              individuals `shouldContain` ["x"]
      
      it "builds IR for theory with set" $ do
        let input = "{ signature { sort S; mySet ⊆ S; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let sets = [ IR.mereoName m | EntityMereological m <- objects
                         , IR.mereoKind m == MereologicalEntityKindSet ]
              sets `shouldContain` ["mySet"]
      
      it "builds IR with built-in sorts" $ do
        let input = "{ }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let sortNames = [ IR.sortName s | EntitySort s <- objects ]
              all (`elem` sortNames) ["𝕌", "𝔻", "ℙ"] `shouldBe` True
      
      it "builds IR with built-in functions" $ do
        let input = "{ }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let funcNames = [ IR.funcName f | EntityFunction f <- objects ]
              all (`elem` funcNames) ["+", "×", "-", "⇒", "∸"] `shouldBe` True
      
      it "builds IR with built-in truth and falsity" $ do
        let input = "{ }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let objects = IR.theoryObjects theory
              let mereoNames = [ IR.mereoName m | EntityMereological m <- objects ]
              all (`elem` mereoNames) ["⊤", "⊥"] `shouldBe` True

    describe "Subtheory handling" $ do
      it "builds IR with nested subtheory" $ do
        let input = "{ signature { sort S; } subtheories { named { Sub: { signature { sort T; } } } } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right theory -> do
              let subs = IR.theorySubtheories theory
              length subs `shouldBe` 1
              IR.theoryName (head subs) `shouldBe` "Sub"
      
      it "resolves qualified names in subtheories" $ do
        let input = "{ signature { sort S; } subtheories { named { Sub { signature { sort T; } } } axioms { assertions { Sub.T#min ⊆ Sub.T#max; } } } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> case buildTheory ast of
            Left err -> fail ("IR build failed: " ++ err)
            Right _ -> pure () :: IO ()

    describe "Error handling" $ do
      it "fails on unknown sort reference" $ do
        let input = "{ signature { x : UnknownSort; } }"
        case parseString input of
          Left _ -> pure () :: IO ()  -- Parse error is fine
          Right ast -> case buildTheory ast of
            Left _ -> pure () :: IO ()  -- Build error is expected
            Right _ -> fail "Should have failed on unknown sort"
      
      it "fails on duplicate sort declaration" $ do
        let input = "{ signature { sort S; sort S; } }"
        case parseString input of
          Left _ -> pure () :: IO ()
          Right ast -> case buildTheory ast of
            Left _ -> pure () :: IO ()  -- Should fail on duplicate
            Right _ -> fail "Should have failed on duplicate sort"
      
      it "fails on malformed function declaration" $ do
        parseString "{ signature { f : S T; } }" `shouldSatisfy` isLeft

  describe "Pretty printer" $ do
    it "round-trips simple theory" $ do
      let input = "{ signature { sort S; } }"
      case parseString input of
        Left err -> fail (errorBundlePretty err)
        Right ast -> do
          let pretty = prettyTheoryDecl ast
          case parseString pretty of
            Left err -> fail ("Re-parse failed: " ++ errorBundlePretty err ++ "\nPretty output: " ++ pretty)
            Right _ -> pure () :: IO ()
    
    it "round-trips theory with function" $ do
      let input = "{ signature { sort S; sort T; f : S → T; } }"
      case parseString input of
        Left err -> fail (errorBundlePretty err)
        Right ast -> do
          let pretty = prettyTheoryDecl ast
          case parseString pretty of
            Left err -> fail ("Re-parse failed: " ++ errorBundlePretty err ++ "\nPretty output: " ++ pretty)
            Right _ -> pure () :: IO ()
    
    it "preserves sort names in round-trip" $ do
      let input = "{ signature { sort MySort; } }"
      case parseString input of
        Left err -> fail (errorBundlePretty err)
        Right ast -> do
          let pretty = prettyTheoryDecl ast
          case parseString pretty of
            Left err -> fail ("Re-parse failed: " ++ errorBundlePretty err)
            Right ast2 -> do
              let sections1 = AST.sections (theoryBody ast)
              let sections2 = AST.sections (theoryBody ast2)
              sections1 `shouldBe` sections2

-- Helper functions
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False