module Main where

import Eidos.Parser (parseString)
import Eidos.FromSyntax (buildTheory)
import Eidos.Pretty (prettyTheoryDecl, prettyTheory, prettyTheoryDeclWithOpts, PrettyOptions(..), defaultPrettyOptions)
import Eidos.AST (TheoryDecl)
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = do
  -- Test with a simple theory
  let input = "{ signature { sort S; sort T; f: S → T; } }"

  putStrLn "=== Parsing and building theory ==="
  case parseString input of
    Left parseErr -> putStrLn $ "Parse error:\n" ++ errorBundlePretty parseErr
    Right ast -> do
      putStrLn "AST successfully parsed!"
      putStrLn "\n=== Pretty-printed AST ==="
      putStrLn $ prettyTheoryDecl ast

      case buildTheory ast of
        Left buildErr -> putStrLn $ "\nIR build error: " ++ buildErr
        Right theory -> do
          putStrLn "\nIR successfully built!"
          putStrLn "\n=== Pretty-printed IR theory ==="
          putStrLn $ prettyTheory theory

          -- Optional: pretty-print with different options
          putStrLn "\n=== Compact mode ==="
          let compactOpts = defaultPrettyOptions { poCompact = True }
          putStrLn $ prettyTheoryDeclWithOpts compactOpts ast