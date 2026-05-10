module Main where

import           System.Environment (getArgs)
import           System.Exit        (exitFailure, exitSuccess)
import qualified System.IO          as IO

import           Eidos.Parse.Parser       (parseFile)
import           Eidos.FromSyntax   (buildTheoryFromFile, buildTheoryPure,
                                     buildTheoryFromResolved)
import           Eidos.Resolution.Resolution   (resolveExternalRefs)

import           Eidos.Print.Pretty       (prettyTheory, prettyTheoryDecl, prettyFactDebug,
                                           prettyResolvedRefs)
import           Eidos.Print.DebugIR      (dumpTheoryIR)
import           Eidos.Print.JSON         (exportTheoryToJSONString)

import           Eidos.IR as IR

import           Eidos.Backend.LeanProps.LeanProps (exportToLeanProps)
import qualified Eidos.Backend.LeanProps.LeanProps as LeanProps
import           Eidos.Backend.Lean.Lean (exportToLean)
import qualified Eidos.Backend.CoqProps.CoqProps as CoqProps

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
        Right ast ->
          case buildTheoryPure ast of
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

    ["--resolve", filePath] -> do
      result <- parseFile filePath
      case result of
        Left err -> do
          IO.hPutStrLn IO.stderr ("Parse error: " ++ show err)
          exitFailure
        Right ast -> do
          resolveResult <- resolveExternalRefs filePath ast
          case resolveResult of
            Left buildErr -> do
              IO.hPutStrLn IO.stderr ("\nResolution error: " ++ buildErr)
              exitFailure
            Right refMap -> do
              putStrLn "\n=== External reference pre-pass ==="
              putStrLn $ prettyResolvedRefs refMap
              exitSuccess

    ("--coq_using_props":rest) -> do
      case reverse rest of
        [] -> usage
        (filePath:revFlags) -> do
          let flags = reverse revFlags
              opts = parseCoqPropsOptions flags
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
                  putStr $ CoqProps.exportToCoqPropsWithOptions opts theory
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
              putStr $ Eidos.Backend.Lean.Lean.exportToLean theory
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
      IO.hPutStrLn IO.stderr "  eidos-parser --resolve <file.theory>    # Resolve external refs only (pre-pass debug)"
      IO.hPutStrLn IO.stderr "  eidos-parser --coq_using_props <file.theory>   # Export to Coq (handles ℙ, 𝕌, and mixed theories)"
      IO.hPutStrLn IO.stderr "    Optional flags before file: --group-by-entity --sorting-axioms --comment-groups --comment-tags"
      IO.hPutStrLn IO.stderr "  eidos-parser --lean_using_props <file.theory>  # Export to Lean 4 (handles ℙ, 𝕌, and mixed theories)"
      IO.hPutStrLn IO.stderr "    Optional flags before file: --group-by-entity --sorting-axioms --comment-groups --comment-tags --bounded-forall-syntax"
      IO.hPutStrLn IO.stderr "  eidos-parser --json <file.theory>             # Export IR as JSON"
      IO.hPutStrLn IO.stderr "  eidos-parser --json --compact <file.theory>   # Export IR as compact JSON"
      IO.hPutStrLn IO.stderr "  eidos-parser --lean <file.theory>             # Export to Lean 4 using structure-based encoding (sorts → Types)"
      exitFailure

parseCoqPropsOptions :: [String] -> CoqProps.CoqPropsOptions
parseCoqPropsOptions flags =
  foldl apply CoqProps.defaultCoqPropsOptions flags
  where
    apply o "--group-by-entity" = o { CoqProps.optGroupByEntity = True }
    apply o "--sorting-axioms"  = o { CoqProps.optUseSortingAxioms = True }
    apply o "--comment-groups"  = o { CoqProps.optAddGroupComments = True }
    apply o "--comment-tags"    = o { CoqProps.optAddTagComments = True }
    apply o _                   = o

parseLeanPropsOptions :: [String] -> LeanProps.LeanPropsOptions
parseLeanPropsOptions flags =
  foldl apply LeanProps.defaultLeanPropsOptions flags
  where
    apply o "--group-by-entity"       = o { LeanProps.optGroupByEntity = True }
    apply o "--sorting-axioms"        = o { LeanProps.optUseSortingAxioms = True }
    apply o "--comment-groups"        = o { LeanProps.optAddGroupComments = True }
    apply o "--bounded-forall-syntax" = o { LeanProps.optUseBoundedForallSyntax = True }
    apply o "--comment-tags"          = o { LeanProps.optAddTagComments = True }
    apply o _                         = o