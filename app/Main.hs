module Main where

import           System.Environment (getArgs)
import           System.Exit        (exitFailure, exitSuccess)
import qualified System.IO          as IO

import           Eidos.Parser       (parseFile)
import           Eidos.FromSyntax   (buildTheoryIO, buildTheoryFromFile, buildTheoryPure)
import           Eidos.BuildMonad   (mkPureResolver)
import           Eidos.Pretty       (prettyTheory, prettyTheoryDecl)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filePath] -> do
      -- Parse the file
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          -- Build the IR using IO resolver (reads files from disk)
          irResult <- buildTheoryFromFile filePath ast
          case irResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn "\nIR successfully built!"
              putStrLn "\n=== Pretty-printed IR theory ==="
              putStrLn $ prettyTheory theory
              exitSuccess
    
    ["--pure", filePath] -> do
      -- Parse the file
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          -- Build the IR using a pure resolver (for testing)
          -- Note: This will only work if the theory has no external references,
          -- or if you provide a resolver with the external content
          let pureResolver = mkPureResolver []  -- Empty resolver - no externals
          case buildTheoryPure pureResolver Nothing ast of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn "\nIR successfully built (pure mode)!"
              putStrLn "\n=== Pretty-printed IR theory ==="
              putStrLn $ prettyTheory theory
              exitSuccess
    
    ["--pretty", filePath] -> do
      -- Just parse and pretty-print the AST
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          putStrLn "\n=== Pretty-printed AST ==="
          putStrLn $ prettyTheoryDecl ast
          exitSuccess
    
    _ -> do
      IO.hPutStrLn IO.stderr "Usage:"
      IO.hPutStrLn IO.stderr "  eidos-parser <file.theory>              # Parse and build IR (IO mode)"
      IO.hPutStrLn IO.stderr "  eidos-parser --pure <file.theory>       # Parse and build IR (pure mode, no external files)"
      IO.hPutStrLn IO.stderr "  eidos-parser --pretty <file.theory>     # Parse and pretty-print AST"
      exitFailure