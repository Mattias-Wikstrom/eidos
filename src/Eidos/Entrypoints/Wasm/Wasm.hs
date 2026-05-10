module Eidos.Entrypoints.Wasm.Wasm
  ( compileBundle
  , compileBundleWithTypes
  , compileSingle
  , mainKey
  ) where

import qualified Data.Map.Strict as Map
import Text.Megaparsec          (errorBundlePretty)
import Eidos.Pipeline.Parse.Parser       (parseString)
import Eidos.Pipeline.Parse.AST          (TheoryDecl(..), TheoryBody)
import Eidos.Pipeline.Resolution.ExternalRef        (TheoryType(..))
import Eidos.Pipeline.Targets.LeanProps.LeanProps (exportToLeanProps)
import Eidos.Pipeline.FromSyntax.FromSyntax (buildTheoryPure, buildTheoryFromResolved)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

mainKey :: String
mainKey = "__main__"

compileSingle :: String -> String
compileSingle src = compileBundle (Map.singleton mainKey src)

compileBundle :: Map.Map String String -> String
compileBundle bundle =
  case Map.lookup mainKey bundle of
    Nothing ->
      "Error: bundle does not contain a \"" ++ mainKey ++ "\" entry"
    Just mainSrc ->
      let deps = [ (ref, src, PlainTheory) | (ref, src) <- Map.toList (Map.delete mainKey bundle) ]
      in compileBundleWithTypes mainSrc deps

compileBundleWithTypes :: String -> [(String, String, TheoryType)] -> String
compileBundleWithTypes mainSrc deps =
  case parseString mainSrc of
    Left err ->
      "Error: parse error:\n" ++ errorBundlePretty err
    Right ast@(TheoryDecl mainBody) -> do
      -- Parse all dependencies, collecting errors if any
      let parseResults = map parseDep deps
          parseDep (ref, src, tt) = case parseString src of
            Left parseErr -> Left (ref, parseErr)
            Right (TheoryDecl body) -> Right (ref, body, tt)
      
      -- Check for any parse errors
      case sequence parseResults of
        Left (ref, parseErr) ->
          "Error: parse error in dependency " ++ ref ++ ":\n" ++ errorBundlePretty parseErr
        Right parsedDeps -> do
          -- Build refMap from successfully parsed dependencies
          let refMap = Map.fromList [ (ref, (body, tt)) | (ref, body, tt) <- parsedDeps ]
          
          -- Build theory using pure builder with refMap
          -- Note: buildTheoryFromResolved takes (refMap, constraints, theoryDecl)
          -- For Wasm, constraints come from the main theory's file extension,
          -- but we don't have a file path. Default to empty constraints
          -- (PlainTheory is the most permissive).
          case buildTheoryFromResolved refMap [] ast of
            Left buildErr ->
              "Error: build error: " ++ buildErr
            Right theory ->
              exportToLeanProps theory