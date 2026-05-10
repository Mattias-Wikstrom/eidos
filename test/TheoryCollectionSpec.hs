{-# LANGUAGE QuasiQuotes #-}
module Main where

import Test.Hspec
import Text.Megaparsec (errorBundlePretty)
import System.Directory (listDirectory, doesFileExist)
import System.FilePath ((</>), takeExtension)
import Control.Monad (filterM)
import Data.List (isSuffixOf)

import Eidos.Pipeline.Parse.Parser (parseString)

main :: IO ()
main = do
  let theoriesDir = "theories"
  allFiles <- listDirectory theoriesDir
  -- Filter only files that end with ".theory" (including .coh.theory, .eq.theory, etc.)
  theoryFiles <- filterM (isTheoryFile theoriesDir) allFiles
  hspec $ do
    describe "Theory collection" $ do
      it ("parses all " ++ show (length theoryFiles) ++ " theories in theories/") $
        mapM_ (parseTheoryFile theoriesDir) theoryFiles

-- | Check if a file is a theory file (ends with .theory, possibly with a suffix)
isTheoryFile :: FilePath -> String -> IO Bool
isTheoryFile dir file = do
  let fullPath = dir </> file
  exists <- doesFileExist fullPath
  return (exists && (".theory" `isSuffixOf` file))

-- | Read and parse a single theory file
parseTheoryFile :: FilePath -> String -> IO ()
parseTheoryFile dir file = do
  content <- readFile (dir </> file)
  case parseString content of
    Left err -> fail $ "Failed to parse " ++ file ++ "\n" ++ content ++ "\n" ++ errorBundlePretty err
    Right _ -> return ()