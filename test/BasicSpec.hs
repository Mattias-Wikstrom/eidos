{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)

import Eidos.Parser (parseString)
import Eidos.Pretty (prettyTheoryDecl)
import Eidos.AST
import qualified Eidos.AST as AST
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
        parseString "{ subtheories { implicit { sub: { signature { sort Q; } } } } }" `shouldSatisfy` isRight
      
      it "parses named subtheory block" $
        parseString "{ subtheories { named { sub: @dir.ext } } }" `shouldSatisfy` isRight
      
      it "parses reflection subtheory block" $
        parseString "{ subtheories { reflection { sub2: { signature { sort Z; } } } } }" `shouldSatisfy` isRight
      
      it "parses multiple subtheories in implicit block" $
        parseString "{ subtheories { implicit { sub1: { signature { sort Q; } } sub2: { signature { sort R; } } } } }" `shouldSatisfy` isRight
      
      it "parses multiple subtheories in named block" $
        parseString "{ subtheories { named { sub1: [[ext1]] sub2: [[ext2]] } } }" `shouldSatisfy` isRight
      
      it "parses mixed subtheory blocks" $
        parseString "{ subtheories { implicit { sub1: { signature { sort Q; } } } named { sub2: [[ext]] } reflection { sub3: { signature { sort Z; } } } } }" `shouldSatisfy` isRight
      
      it "parses subtheory with inline body" $
        parseString "{ subtheories { implicit { sub: { signature { sort Q; } } } } }" `shouldSatisfy` isRight
      
      it "parses subtheory with external reference" $
        parseString "{ subtheories { named { sub: [[external]] } } }" `shouldSatisfy` isRight
      
      it "rejects implicit subtheory without a name" $
        parseString "{ subtheories { implicit { { signature { sort Q; } } } } }"
          `shouldSatisfy` isLeft
          
      it "parses complete example from documentation" $
        parseString [r|{
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
                    sub3: {
                        signature {
                            sort Q;
                        }
                    }
                },
                named {
                    sub: @ext
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
        }|] `shouldSatisfy` isRight

      it "parses subtheories separated by commas" $
        parseString [r|{
          subtheories {
            implicit {
              field: @field,
              strict_linear_order: @strict_linear_order
            }
          },
          axioms {
          }
        }|] `shouldSatisfy` isRight

      it "sfsdf" $
        parseString [r|{
          subtheories {
           implicit {
             ring: @ring
           },
           named {
             multiplicative_group: @group
           }
         },
         signature {
           sort E; // Used for non-zero elements
           multiplicative_inv: E → E;
           E subsort D; // The non-zero elements form a subdomain
         },
         axioms {
           facts {
             multiplicative_group.D = E;
             ring.one = multiplicative_group.n;
             multiplicative_inv = multiplicative_group.inv;
             [x : E] [y : E] ring.prod(x, y) = multiplicative_group.op(x, y);
           },
           assertions {
             [x : D] (x = 0) ∨ ∃y:E x=y; // Any element is either zero or non-zero
           }
         }
        }|] `shouldSatisfy` isRight
        
 
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

    describe "Error handling" $ do
      it "fails on malformed function declaration" $
        parseString "{ signature { f : S T; } }" `shouldSatisfy` isLeft

    describe "Pretty printer" $ do
      it "round-trips simple theory" $ (do
        let input = "{ signature { sort S; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> do
            let pretty = prettyTheoryDecl ast
            case parseString pretty of
              Left err -> fail ("Re-parse failed: " ++ errorBundlePretty err ++ "\nPretty output: " ++ pretty)
              Right _ -> return () :: IO ())
      
      it "round-trips theory with function" $ (do
        let input = "{ signature { sort S; sort T; f : S → T; } }"
        case parseString input of
          Left err -> fail (errorBundlePretty err)
          Right ast -> do
            let pretty = prettyTheoryDecl ast
            case parseString pretty of
              Left err -> fail ("Re-parse failed: " ++ errorBundlePretty err ++ "\nPretty output: " ++ pretty)
              Right _ -> return () :: IO ())
      
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

      it "rejects duplicate named sections in subtheories" $
        parseString "{ subtheories { named { sub1: {} } named { sub2: {} } } }"
          `shouldSatisfy` isLeft

      it "rejects duplicate implicit sections" $
        parseString "{ subtheories { implicit { { } } implicit { { } } } }"
          `shouldSatisfy` isLeft

      it "rejects duplicate reflection sections" $
        parseString "{ subtheories { reflection { sub1: {} } reflection { sub2: {} } } }"
          `shouldSatisfy` isLeft

      it "accepts mixed distinct sections" $
        parseString "{ subtheories { implicit { sub: { } } named { sub1: {} } reflection { sub2: {} } } }"
          `shouldSatisfy` isRight
                
      it "rejects repeated subtheory names for subtheories of the same kind" $
        parseString "{ subtheories { named { sub: {} sub: {} } } }"
          `shouldSatisfy` isLeft
          
      it "rejects repeated subtheory names for subtheories of different kinds" $
        parseString "{ subtheories { named { sub: {} } reflection { sub: {} } } }"
          `shouldSatisfy` isLeft
          
    describe "Suffix syntax" $ do
      -- Valid hash suffixes
      it "accepts #res suffix on a term" $
        parseString "{ axioms { assertions { f#res = f#res; } } }" `shouldSatisfy` isRight

      it "accepts #arg suffix on a term" $
        parseString "{ axioms { assertions { f#arg = f#arg; } } }" `shouldSatisfy` isRight

      it "accepts #dom suffix on a term" $
        parseString "{ axioms { assertions { f#dom = f#dom; } } }" `shouldSatisfy` isRight

      it "accepts #min and #max suffixes" $
        parseString "{ axioms { assertions { S#min ≤ S#max; } } }" `shouldSatisfy` isRight

      -- .res / .arg / .dom must be rejected (these are NOT valid dot-attr suffixes;
      -- use #res, #arg, #dom instead). We use a parenthesised base term so that
      -- the dot cannot be parsed as a qualified-ref separator, forcing the suffix path.
      it "rejects .res as a dot-attribute suffix" $
        parseString "{ axioms { assertions { (f).res = (f).res; } } }" `shouldSatisfy` isLeft

      it "rejects .arg as a dot-attribute suffix" $
        parseString "{ axioms { assertions { (f).arg = (f).arg; } } }" `shouldSatisfy` isLeft

      it "rejects .dom as a dot-attribute suffix" $
        parseString "{ axioms { assertions { (f).dom = (f).dom; } } }" `shouldSatisfy` isLeft

      -- .min and .max remain valid dot-attr alternatives
      it "accepts .min as a dot-attribute suffix" $
        parseString "{ axioms { assertions { S.min ≤ S.max; } } }" `shouldSatisfy` isRight

      it "accepts .max as a dot-attribute suffix" $
        parseString "{ axioms { assertions { S.max = S.max; } } }" `shouldSatisfy` isRight

    describe "Subtheory structure" $ do
      -- Bare items at top level of subtheories {} are not allowed
      it "rejects a bare named item at top level of subtheories block" $
        parseString "{ subtheories { sub: { signature { sort S; } } } }"
          `shouldSatisfy` isLeft

      it "rejects a bare external reference at top level of subtheories block" $
        parseString "{ subtheories { sub: @ext } }"
          `shouldSatisfy` isLeft

      -- [bracket] qualifier syntax is forbidden
      it "rejects [implicit] qualifier inside an implicit block" $
        parseString "{ subtheories { implicit { [implicit] sub: { } } } }"
          `shouldSatisfy` isLeft

      it "rejects [named] qualifier inside a named block" $
        parseString "{ subtheories { named { [named] sub: { } } } }"
          `shouldSatisfy` isLeft

      it "rejects [implicit] qualifier inside a named block" $
        parseString "{ subtheories { named { [implicit] sub: { } } } }"
          `shouldSatisfy` isLeft

      it "rejects [reflection] qualifier inside a reflection block" $
        parseString "{ subtheories { reflection { [reflection] sub: { } } } }"
          `shouldSatisfy` isLeft

-- Helper functions
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False