-- | Eidos.Wasm.Wasm
--
-- Entry point for the GHC WebAssembly build target.
--
-- == Architecture
--
-- When compiled to Wasm the Haskell runtime has no filesystem access, so the
-- host (JavaScript / Node.js) is responsible for gathering every theory file
-- that the main theory depends on.  This module exposes a single pure
-- function, 'compileBundle', that accepts an in-memory bundle and returns
-- either Lean 4 output or an error message.
--
-- == Bundle protocol
--
-- The caller provides a @Map String String@ where:
--
--   * The key @"__main__"@ maps to the source of the theory being compiled.
--   * Every other key is the reference string as it appears after @\@@
--     in a theory file (e.g. @"foundations.sets"@), and its value is the
--     source text of that theory.
--
-- All keys other than @"__main__"@ are registered with 'mkPureResolver', so
-- they will be found when the builder encounters an @\@@ reference.
--
-- == JavaScript / Node.js glue
--
-- See @wasm/eidos_wasm.mjs@ for the Node.js wrapper that loads the Wasm
-- module and exposes @compileTheory(src)@ and @compileBundle(bundleObj)@.
--
-- == Foreign exports
--
-- The two @foreign export ccall@ declarations at the bottom of this file are
-- only compiled when the @wasm32@ target is active (guarded by the @wasm32@
-- CPP conditional from GHC's Wasm toolchain).  In a normal GHC build they
-- are omitted, so the module is safe to import from tests or other modules.

module Eidos.Wasm.Wasm
  ( compileBundle
  , compileBundleWithTypes
  , compileSingle
  , mainKey
  ) where

import qualified Data.Map.Strict as Map

import Text.Megaparsec          (errorBundlePretty)
import Eidos.Parse.Parser            (parseString)
import Eidos.BuildMonad        (mkPureResolverWithTypes, emptyPureResolver)
import Eidos.ExternalRef       (TheoryType(..))
import Eidos.FromSyntax        (buildTheoryPure)
import Eidos.Backend.LeanProps.LeanProps  (exportToLeanProps)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | The reserved key for the main (entry) theory in a bundle.
mainKey :: String
mainKey = "__main__"

-- | Compile a single theory source string that has no external @\@@ references.
--
-- This is a convenience wrapper around 'compileBundle' that creates a
-- single-entry bundle.
compileSingle :: String -> String
compileSingle src = compileBundle (Map.singleton mainKey src)

-- | Compile a bundle of theory sources.
--
-- The bundle must contain at least the @"__main__"@ key.  All other keys are
-- made available to the resolver for @\@@ references.
--
-- Returns either a Lean 4 string (on success) or a human-readable error
-- message prefixed with @"Error: "@.
compileBundle :: Map.Map String String -> String
compileBundle bundle =
  case Map.lookup mainKey bundle of
    Nothing ->
      "Error: bundle does not contain a \"" ++ mainKey ++ "\" entry"
    Just mainSrc ->
      let deps = [ (ref, src, PlainTheory) | (ref, src) <- Map.toList (Map.delete mainKey bundle) ]
      in compileBundleWithTypes mainSrc deps

-- | Compile a main theory source together with typed dependency entries.
compileBundleWithTypes :: String -> [(String, String, TheoryType)] -> String
compileBundleWithTypes mainSrc deps =
  case parseString mainSrc of
    Left err ->
      "Error: parse error:\n" ++ errorBundlePretty err
    Right ast ->
      let resolver = if null deps
                       then emptyPureResolver
                       else mkPureResolverWithTypes deps
      in case buildTheoryPure resolver Nothing ast of
           Left buildErr ->
             "Error: build error: " ++ buildErr
           Right theory ->
             exportToLeanProps theory

-- ---------------------------------------------------------------------------
-- Foreign exports (Wasm target only)
--
-- GHC's Wasm backend uses the standard Haskell FFI with the ccall calling
-- convention.  String passing goes via a JSON envelope so that both keys and
-- values can contain arbitrary Unicode without encoding hassle.
--
-- The actual marshalling (C string <-> Haskell String, JSON decode/encode) is
-- handled in the JS glue layer (wasm/eidos_wasm.mjs), which calls the
-- lower-level primitives that GHC's Wasm RTS exposes for string I/O.
-- ---------------------------------------------------------------------------

-- NOTE: Foreign exports are intentionally left out of this module.
-- The recommended pattern for GHC Wasm is to write a tiny separate
-- module (e.g. Eidos.WasmFFI) that imports Eidos.Wasm and adds the
-- foreign exports, and to compile *only* that module with the Wasm
-- toolchain.  This keeps the core logic testable with a normal GHC
-- build.  See wasm/README.md for the full build instructions.
