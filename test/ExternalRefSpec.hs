-- test/ExternalRefSpec.hs
{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import System.IO.Temp (withSystemTempDirectory)
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing)
import Data.List (isInfixOf)

import Eidos.Parser (parseString)
import Eidos.FromSyntax (buildTheoryWithResolver, buildTheoryFromFile)
import Eidos.ExternalRef (ExternalRefResult(..), ExternalRefSource(..), TheoryType(..), mockResolver)
import qualified Eidos.IR as IR

main :: IO ()
main = hspec $ do
  describe "External reference resolver (pluggable)" $ do
    
    describe "Mock resolver (pure, no IO)" $ do
      it "can resolve using a mock resolver" $ do
        let entries = [("ext", Right $ ExternalRefResult
                          { extRefIdentifier = "ext"  -- not used as theory name
                          , extRefTheoryType = PlainTheory
                          , extRefSource = MemorySource "{ signature { sort Mock; } }"
                          })]
        let mock = mockResolver entries
        let input = "{ subtheories { named { sub: @ext } } }"
        case parseString input of
          Left err -> fail (show err)
          Right ast -> case buildTheoryWithResolver mock Nothing ast of
            Left err -> fail err
            Right th -> do
              let subs = IR.theorySubtheories th
              length subs `shouldBe` 1
              IR.theoryName (head subs) `shouldBe` "sub"  -- alias, not "ext"
      
      it "reports missing references" $ do
        let mock = mockResolver []
        let input = "{ subtheories { named { sub: @missing } } }"
        case parseString input of
          Left err -> fail (show err)
          Right ast -> case buildTheoryWithResolver mock Nothing ast of
            Left err -> err `shouldContain` "NoMatchingFile"
            Right _ -> fail "Expected failure"
      
      it "reports ambiguous references" $ do
        let entries = [ ("ext", Right $ ExternalRefResult
                            { extRefIdentifier = "ext1"
                            , extRefTheoryType = PlainTheory
                            , extRefSource = MemorySource "{ signature { sort One; } }"
                            })
                      , ("ext", Right $ ExternalRefResult
                            { extRefIdentifier = "ext2"
                            , extRefTheoryType = CoherentTheory
                            , extRefSource = MemorySource "{ signature { sort Two; } }"
                            })
                      ]
        let mock = mockResolver entries
        let input = "{ subtheories { named { sub: @ext } } }"
        case parseString input of
          Left err -> fail (show err)
          Right ast -> case buildTheoryWithResolver mock Nothing ast of
            Left err -> err `shouldContain` "AmbiguousMatch"
            Right _ -> fail "Expected ambiguous error"
    
    describe "Custom resolver (pure function)" $ do
      it "allows custom resolution logic" $ do
        let customResolver _baseContext _ref = Right $ ExternalRefResult
              { extRefIdentifier = "custom"
              , extRefTheoryType = PlainTheory
              , extRefSource = MemorySource "{ signature { sort Custom; } }"
              }
        let input = "{ subtheories { named { sub1: @anything sub2: @whatever } } }"
        case parseString input of
          Left err -> fail (show err)
          Right ast -> case buildTheoryWithResolver customResolver Nothing ast of
            Left err -> fail err
            Right th -> do
              let subs = IR.theorySubtheories th
              length subs `shouldBe` 2
              all (\sub -> IR.theoryName sub == "sub1" || IR.theoryName sub == "sub2") subs `shouldBe` True

      it "can use base context for resolution" $ do
        -- The resolver uses base context to find the file, but the theory name is the alias
        let contextResolver baseContext ref =
              let fullRef = case baseContext of
                    Just ctx -> ctx ++ "/" ++ ref
                    Nothing -> ref
              in Right $ ExternalRefResult
                { extRefIdentifier = fullRef  -- not used as theory name
                , extRefTheoryType = PlainTheory
                , extRefSource = MemorySource "{ signature { sort Dummy; } }"
                }
        let input = "{ subtheories { named { sub: @ext } } }"
        case parseString input of
          Left err -> fail (show err)
          Right ast -> case buildTheoryWithResolver contextResolver (Just "parent") ast of
            Left err -> fail err
            Right th -> do
              let subs = IR.theorySubtheories th
              length subs `shouldBe` 1
              IR.theoryName (head subs) `shouldBe` "sub"  -- alias, not "parent.ext"
    
    describe "Filesystem resolver (IO, actual file reading)" $ do
      it "resolves @ext to ext.theory" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let subFile = dir </> "ext.theory"
          writeFile subFile "{ signature { sort External; } }"
          writeFile mainFile "{ subtheories { named { sub: @ext } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> fail err
                Right th -> do
                  let subs = IR.theorySubtheories th
                  length subs `shouldBe` 1
                  IR.theoryName (head subs) `shouldBe` "sub"  -- alias
      
      it "reports ambiguity when both .theory and .coh.theory exist" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let plainFile = dir </> "ext.theory"
          let cohFile = dir </> "ext.coh.theory"
          writeFile plainFile "{ signature { sort Plain; } }"
          writeFile cohFile "{ signature { sort Coh; } }"
          writeFile mainFile "{ subtheories { named { sub: @ext } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> err `shouldContain` "AmbiguousMatch"
                Right _ -> fail "Expected ambiguous error"
      
      it "resolves @a.b.ext to a/b/ext.theory" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let subDir = dir </> "a" </> "b"
          createDirectoryIfMissing True subDir
          let subFile = subDir </> "ext.theory"
          writeFile subFile "{ signature { sort Deep; } }"
          writeFile mainFile "{ subtheories { named { sub: @a.b.ext } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> fail err
                Right th -> do
                  let subs = IR.theorySubtheories th
                  length subs `shouldBe` 1
                  IR.theoryName (head subs) `shouldBe` "sub"
      
      it "resolves @a.b.ext to a/b.ext.theory" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let subDir = dir </> "a"
          createDirectoryIfMissing True subDir
          let subFile = subDir </> "b.ext.theory"
          writeFile subFile "{ signature { sort Dotted; } }"
          writeFile mainFile "{ subtheories { named { sub: @a.b.ext } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> fail err
                Right th -> do
                  let subs = IR.theorySubtheories th
                  length subs `shouldBe` 1
                  IR.theoryName (head subs) `shouldBe` "sub"
      
      it "reports ambiguity when multiple distinct file paths match" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let file1 = dir </> "a.b.ext.theory"
          let file2 = dir </> "a" </> "b.ext.theory"
          createDirectoryIfMissing True (dir </> "a")
          writeFile file1 "{ signature { sort One; } }"
          writeFile file2 "{ signature { sort Two; } }"
          writeFile mainFile "{ subtheories { named { sub: @a.b.ext } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> do
                  err `shouldContain` "AmbiguousMatch"
                  err `shouldContain` "a.b.ext.theory"
                  err `shouldContain` "b.ext.theory"
                Right _ -> fail "Expected ambiguous error"
      
      it "supports .coh.theory extension when no .theory exists" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let cohFile = dir </> "logic.coh.theory"
          writeFile cohFile "{ signature { sort Coherent; } }"
          writeFile mainFile "{ subtheories { named { sub: @logic } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> fail err
                Right th -> do
                  let subs = IR.theorySubtheories th
                  length subs `shouldBe` 1
                  IR.theoryName (head subs) `shouldBe` "sub"
      
      it "extracts correct theory name from extension when alias is used" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let eqFile = dir </> "group.eq.theory"
          writeFile eqFile "{ signature { sort Group; } }"
          writeFile mainFile "{ subtheories { named { sub: @group } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> fail err
                Right th -> do
                  let subs = IR.theorySubtheories th
                  length subs `shouldBe` 1
                  IR.theoryName (head subs) `shouldBe` "sub"  -- alias, not "group.eq"
    
    describe "Backward compatibility" $ do
      it "supports old [[ext]] syntax" $ do
        withSystemTempDirectory "eidos-test" $ \dir -> do
          let mainFile = dir </> "main.theory"
          let subFile = dir </> "ext.theory"
          writeFile subFile "{ signature { sort Old; } }"
          writeFile mainFile "{ subtheories { named { sub: [[ext]] } } }"
          
          content <- readFile mainFile
          case parseString content of
            Left err -> fail (show err)
            Right ast -> do
              result <- buildTheoryFromFile mainFile ast
              case result of
                Left err -> fail err
                Right th -> do
                  let subs = IR.theorySubtheories th
                  length subs `shouldBe` 1
                  IR.theoryName (head subs) `shouldBe` "sub"