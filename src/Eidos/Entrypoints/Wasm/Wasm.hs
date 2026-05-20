module Eidos.Entrypoints.Wasm.Wasm
  ( compileBundle
  , compileBundleWithTypes
  , compileSingle
  , mainKey
  , targetKey
  , resolveTarget
  ) where

import qualified Data.Map.Strict as Map
import Text.Megaparsec          (errorBundlePretty)
import Eidos.Pipeline.Parse.Parser       (parseString)
import Eidos.Pipeline.Parse.AST          (TheoryDecl(..))
import Eidos.Pipeline.Resolution.ExternalRef        (TheoryType(..))
import Eidos.Pipeline.FromSyntax.FromSyntax (buildTheoryPure, buildTheoryFromResolved)
import qualified Eidos.Pipeline.InvokePipeline as PL

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

mainKey :: String
mainKey = "__main__"

compileSingle :: String -> String
compileSingle src = compileBundle (Map.singleton mainKey src)

targetKey :: String
targetKey = "__target__"

compileBundle :: Map.Map String String -> String
compileBundle bundle =
  case Map.lookup mainKey bundle of
    Nothing ->
      "Error: bundle does not contain a \"" ++ mainKey ++ "\" entry"
    Just mainSrc ->
      let target = resolveTarget (Map.lookup targetKey bundle)
          deps   = [ (ref, src, PlainTheory)
                   | (ref, src) <- Map.toList (Map.delete mainKey (Map.delete targetKey bundle)) ]
      in compileBundleWithTypes target mainSrc deps

resolveTarget :: Maybe String -> PL.PipelineTarget
resolveTarget (Just "coq_using_props") = PL.TargetCoqProps
resolveTarget (Just "lean_runtime")    = PL.TargetLeanRuntime
resolveTarget (Just "coq_runtime")     = PL.TargetCoqRuntime
resolveTarget (Just "mereological")    = PL.TargetMereological
resolveTarget _                        = PL.TargetLeanProps

compileBundleWithTypes :: PL.PipelineTarget -> String -> [(String, String, TheoryType)] -> String
compileBundleWithTypes target mainSrc deps =
  case parseString mainSrc of
    Left err ->
      "Error: parse error:\n" ++ errorBundlePretty err
    Right ast@(TheoryDecl _mainBody) -> do
      let parseResults = map parseDep deps
          parseDep (ref, src, tt) = case parseString src of
            Left parseErr -> Left (ref, parseErr)
            Right (TheoryDecl body) -> Right (ref, body, tt)
      case sequence parseResults of
        Left (ref, parseErr) ->
          "Error: parse error in dependency " ++ ref ++ ":\n" ++ errorBundlePretty parseErr
        Right parsedDeps -> do
          let refMap = Map.fromList [ (ref, (body, tt)) | (ref, body, tt) <- parsedDeps ]
          case buildTheoryFromResolved refMap [] ast of
            Left buildErr ->
              "Error: build error: " ++ buildErr
            Right theory ->
              PL.invokePipeline target PL.defaultTargetOptions theory
