module Main where

import           System.Environment (getArgs)
import           System.Exit        (exitFailure, exitSuccess)
import qualified System.IO          as IO

import           Eidos.Parser       (parseFile)
import           Eidos.FromSyntax   (buildTheoryFromFile, buildTheoryPure)
import           Eidos.BuildMonad   (mkPureResolver)
import           Eidos.Pretty       (prettyTheory, prettyTheoryDecl, prettyFactDebug)
import           Eidos.DebugIR      (dumpTheoryIR)
import           Eidos.IR as IR 

import           Eidos.Export.JSON      (exportTheoryToJSONString)
import           Eidos.Export.LeanProps (exportToLeanProps)
import Eidos.Export.LeanMereo (exportToLeanMereo)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
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
    
    ["--debug", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          irResult <- buildTheoryFromFile filePath ast
          case irResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn "\nIR successfully built (debug mode)!"
              putStrLn "\n=== Debug: Facts with resolved expressions ==="
              mapM_ (putStrLn . prettyFactDebug) (IR.theoryFacts theory)
              putStrLn "\n=== Pretty-printed IR theory ==="
              putStrLn $ prettyTheory theory
              exitSuccess

    ["--dump-ir", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          irResult <- buildTheoryFromFile filePath ast
          case irResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn "\n=== AST (source-level) ==="
              putStrLn $ prettyTheoryDecl ast
              putStrLn "\n=== IR dump (resolved, deterministic) ==="
              putStrLn $ dumpTheoryIR theory
              exitSuccess
    
    ["--json", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          irResult <- buildTheoryFromFile filePath ast
          case irResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn $ exportTheoryToJSONString theory
              exitSuccess

    ["--pure", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          let pureResolver = mkPureResolver []
          case buildTheoryPure pureResolver Nothing ast of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn "\nIR successfully built (pure mode)!"
              putStrLn "\n=== Pretty-printed IR theory ==="
              putStrLn $ prettyTheory theory
              exitSuccess
    
    ["--lean_using_mereo", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          irResult <- buildTheoryFromFile filePath ast
          case irResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStrLn $ exportToLeanMereo theory
              exitSuccess

    ["--pretty", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          putStrLn "\n=== Pretty-printed AST ==="
          putStrLn $ prettyTheoryDecl ast
          exitSuccess
    
    ["--lean_using_props", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          irResult <- buildTheoryFromFile filePath ast
          case irResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nIR build error: " ++ buildErr)
              exitFailure
            Right theory -> do
              putStr $ exportToLeanProps theory
              exitSuccess

    _ -> do
      IO.hPutStrLn IO.stderr "Usage:"
      IO.hPutStrLn IO.stderr "  eidos-parser <file.theory>              # Parse and build IR (IO mode)"
      IO.hPutStrLn IO.stderr "  eidos-parser --debug <file.theory>      # Parse and build IR with debug output (shows resolved facts)"
      IO.hPutStrLn IO.stderr "  eidos-parser --dump-ir <file.theory>    # Parse and print AST + deterministic IR dump"
      IO.hPutStrLn IO.stderr "  eidos-parser --pure <file.theory>       # Parse and build IR (pure mode, no external files)"
      IO.hPutStrLn IO.stderr "  eidos-parser --pretty <file.theory>     # Parse and pretty-print AST"
      IO.hPutStrLn IO.stderr "  eidos-parser --lean_using_props <file.theory>  # Export propositional theory to Lean 4 (all Props strategy)"
      IO.hPutStrLn IO.stderr "  eidos-parser --lean_using_mereo <file.theory>   # Generate Lean 4 code for mereological theories"
      IO.hPutStrLn IO.stderr "  eidos-parser --json <file.theory>             # Export IR as JSON"
      IO.hPutStrLn IO.stderr "  eidos-parser --json --compact <file.theory>   # Export IR as compact JSON"
      exitFailure