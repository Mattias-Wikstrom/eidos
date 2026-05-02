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
import qualified Eidos.Export.LeanProps as LeanProps
import           Eidos.Export.Lean (exportToLean)

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
    
    ("--lean_using_props":rest) -> do
      case reverse rest of
        [] -> usage
        (filePath:revFlags) -> do
          let flags = reverse revFlags
              opts = parseLeanPropsOptions flags
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
                  putStr $ LeanProps.exportToLeanPropsWithOptions opts theory
                  exitSuccess
    
    ["--lean", filePath] -> do
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
              putStr $ Eidos.Export.Lean.exportToLean theory
              exitSuccess

    _ -> do
      usage

usage :: IO ()
usage = do
      IO.hPutStrLn IO.stderr "Usage:"
      IO.hPutStrLn IO.stderr "  eidos-parser <file.theory>              # Parse and build IR (IO mode)"
      IO.hPutStrLn IO.stderr "  eidos-parser --debug <file.theory>      # Parse and build IR with debug output (shows resolved facts)"
      IO.hPutStrLn IO.stderr "  eidos-parser --dump-ir <file.theory>    # Parse and print AST + deterministic IR dump"
      IO.hPutStrLn IO.stderr "  eidos-parser --pure <file.theory>       # Parse and build IR (pure mode, no external files)"
      IO.hPutStrLn IO.stderr "  eidos-parser --pretty <file.theory>     # Parse and pretty-print AST"
      IO.hPutStrLn IO.stderr "  eidos-parser --lean_using_props <file.theory>  # Export to Lean 4 (handles ℙ, 𝕌, and mixed theories)"
      IO.hPutStrLn IO.stderr "    Optional flags before file: --group-by-entity --sorting-axioms --comment-groups --comment-tags --bounded-forall-syntax"
      IO.hPutStrLn IO.stderr "  eidos-parser --json <file.theory>             # Export IR as JSON"
      IO.hPutStrLn IO.stderr "  eidos-parser --json --compact <file.theory>   # Export IR as compact JSON"
      IO.hPutStrLn IO.stderr "  eidos-parser --lean <file.theory>                   # Export to Lean 4 using structure-based encoding (sorts → Types)"
      exitFailure

parseLeanPropsOptions :: [String] -> LeanProps.LeanPropsOptions
parseLeanPropsOptions flags =
  foldl apply LeanProps.defaultLeanPropsOptions flags
  where
    apply o "--group-by-entity" = o { LeanProps.optGroupByEntity = True }
    apply o "--sorting-axioms" = o { LeanProps.optUseSortingAxioms = True }
    apply o "--comment-groups" = o { LeanProps.optAddGroupComments = True }
    apply o "--bounded-forall-syntax" = o { LeanProps.optUseBoundedForallSyntax = True }
    apply o "--comment-tags" = o { LeanProps.optAddTagComments = True }
    apply o _ = o
