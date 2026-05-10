-- | Eidos.Entrypoints.Wasm.WasmFFI
--
-- Foreign exports for the GHC WebAssembly build target.
--
-- This module is intentionally separate from 'Eidos.Wasm' so that the
-- core compilation logic can be imported and tested with a normal GHC
-- build.  Only this thin shim needs the Wasm toolchain.
--
-- == Calling convention
--
-- Both exported functions receive and return null-terminated C strings
-- (UTF-8).  The JS glue layer in @wasm/eidos_wasm.mjs@ handles the
-- conversion between JavaScript strings and the linear Wasm memory.
--
-- === hs_compile_single
--
-- Takes a single theory source string, returns Lean 4 output or an
-- @"Error: ..."@ string.
--
-- === hs_compile_bundle
--
-- Takes a JSON object string of the form:
--
-- @
-- { "__main__": "..theory source..",
--   "some.reference": "..dependency source..",
--   ...
-- }
-- @
--
-- Returns Lean 4 output or an @"Error: ..."@ string.
--
-- == Build
--
-- See @wasm/README.md@ for the full @wasm32-wasi-ghc@ build recipe.

{-# LANGUAGE ForeignFunctionInterface #-}

module Eidos.Entrypoints.Wasm.WasmFFI where

import Foreign.C.String  (CString, newCString, peekCString)
import qualified Data.Map.Strict as Map

import Eidos.Entrypoints.Wasm.Wasm (compileBundleWithTypes, compileSingle, mainKey)
import Eidos.Pipeline.Resolution.ExternalRef (TheoryType(..))

-- ---------------------------------------------------------------------------
-- hs_compile_single
-- ---------------------------------------------------------------------------

-- | Compile a single theory with no external references.
--   Receives and returns a UTF-8 C string.
foreign export ccall hs_compile_single :: CString -> IO CString

hs_compile_single :: CString -> IO CString
hs_compile_single cSrc = do
  src    <- peekCString cSrc
  result <- pure (compileSingle src)
  newCString result

-- ---------------------------------------------------------------------------
-- hs_compile_bundle
-- ---------------------------------------------------------------------------

-- | Compile a bundle supplied as a JSON object string.
--   The JSON must be @{ \"__main__\": \"...\", \"ref\": \"...\" }@.
--   Returns Lean 4 output or @"Error: ..."@.
foreign export ccall hs_compile_bundle :: CString -> IO CString

hs_compile_bundle :: CString -> IO CString
hs_compile_bundle cJson = do
  json   <- peekCString cJson
  result <- pure (compileBundleFromJSON json)
  newCString result

-- ---------------------------------------------------------------------------
-- JSON parsing (minimal, no external dependency)
-- ---------------------------------------------------------------------------

-- | Parse the bundle JSON and call 'compileBundle'.
--
-- We use a hand-rolled parser instead of aeson to keep the Wasm binary
-- small.  The format is intentionally simple: a flat JSON object whose
-- keys and values are both JSON strings.  No nesting is supported.
--
-- Backward-compatible input:
--   { "__main__": "...", "group": "..." }
--
-- Typed dependency metadata (optional):
--   { "__main__": "...",
--     "group": "...",
--     "__theory_type__.group": "eq" }
--
-- Allowed type tags: plain, eq, reg, coh, fol, sol, prop, mereo.
compileBundleFromJSON :: String -> String
compileBundleFromJSON json =
  case parseSimpleStringMap json of
    Left err     -> "Error: JSON parse error: " ++ err
    Right bundle ->
      case buildTypedBundle bundle of
        Left err ->
          "Error: bundle metadata error: " ++ err
        Right (mainSrc, deps) ->
          compileBundleWithTypes mainSrc deps

theoryTypePrefix :: String
theoryTypePrefix = "__theory_type__."

buildTypedBundle :: [(String, String)] -> Either String (String, [(String, String, TheoryType)])
buildTypedBundle entries = do
  mainSrc <- case lookup mainKey entries of
    Nothing -> Left $ "bundle does not contain a \"" ++ mainKey ++ "\" entry"
    Just src -> Right src
  depTypeMap <- parseTypeMetadata entries
  let dependencies =
        [ (ref, src, Map.findWithDefault PlainTheory ref depTypeMap)
        | (ref, src) <- entries
        , ref /= mainKey
        , not (isTheoryTypeMetadataKey ref)
        ]
      dependencyRefs = Map.fromList [ (ref, ()) | (ref, _, _) <- dependencies ]
  mapM_ (ensureMetadataRefExists dependencyRefs) (Map.keys depTypeMap)
  Right (mainSrc, dependencies)

ensureMetadataRefExists :: Map.Map String () -> String -> Either String ()
ensureMetadataRefExists dependencyRefs ref =
  if Map.member ref dependencyRefs
    then Right ()
    else Left $ "theory-type metadata references unknown dependency \"" ++ ref ++ "\""

parseTypeMetadata :: [(String, String)] -> Either String (Map.Map String TheoryType)
parseTypeMetadata entries = foldl step (Right Map.empty) entries
  where
    step :: Either String (Map.Map String TheoryType) -> (String, String) -> Either String (Map.Map String TheoryType)
    step acc (k, v)
      | not (isTheoryTypeMetadataKey k) = acc
      | otherwise = do
          current <- acc
          let ref = drop (length theoryTypePrefix) k
          if null ref
            then Left "empty reference key in theory-type metadata"
            else do
              theoryType <- parseTheoryTypeTag v
              Right (Map.insert ref theoryType current)

isTheoryTypeMetadataKey :: String -> Bool
isTheoryTypeMetadataKey key = take (length theoryTypePrefix) key == theoryTypePrefix

parseTheoryTypeTag :: String -> Either String TheoryType
parseTheoryTypeTag tag = case tag of
  "plain" -> Right PlainTheory
  "eq"    -> Right EquationalTheory
  "reg"   -> Right RegularTheory
  "coh"   -> Right CoherentTheory
  "fol"   -> Right FOLTheory
  "sol"   -> Right SOLTheory
  "prop"  -> Right PropositionalTheory
  "mereo" -> Right MereologicalTheory
  _       -> Left $ "unknown theory type tag \"" ++ tag ++ "\""

-- | Parse a flat JSON object @{ "k": "v", ... }@ into a list of pairs.
-- Handles basic JSON string escaping (\n \t \\ \").
parseSimpleStringMap :: String -> Either String [(String, String)]
parseSimpleStringMap s =
  case dropSpace s of
    '{' : rest -> parseMembers (dropSpace rest) []
    _          -> Left "expected '{'"

parseMembers :: String -> [(String, String)] -> Either String [(String, String)]
parseMembers s acc =
  case s of
    '}' : _ -> Right (reverse acc)
    '"' : _ -> do
      (k, rest1)  <- parseString' s
      rest2       <- expectColon (dropSpace rest1)
      (v, rest3)  <- parseString' (dropSpace rest2)
      let rest4 = dropSpace rest3
      case rest4 of
        ',' : rest5 -> parseMembers (dropSpace rest5) ((k, v) : acc)
        '}'  : _    -> Right (reverse ((k, v) : acc))
        []          -> Right (reverse ((k, v) : acc))
        _           -> Left ("unexpected character after value: " ++ take 10 rest4)
    _ -> Left ("expected '\"' or '}', got: " ++ take 10 s)

expectColon :: String -> Either String String
expectColon (':' : rest) = Right rest
expectColon s            = Left ("expected ':', got: " ++ take 10 s)

-- | Parse a JSON string starting at the leading '"'.
parseString' :: String -> Either String (String, String)
parseString' ('"' : rest) = go rest []
  where
    go []              _   = Left "unterminated string"
    go ('"'  : tail_) acc  = Right (reverse acc, tail_)
    go ('\\' : c : t) acc  = go t (unescape c : acc)
    go (c    : t)     acc  = go t (c : acc)
    unescape 'n'  = '\n'
    unescape 't'  = '\t'
    unescape 'r'  = '\r'
    unescape '\\' = '\\'
    unescape '"'  = '"'
    unescape '/'  = '/'
    unescape c    = c          -- pass through unknown escapes
parseString' s = Left ("expected '\"', got: " ++ take 10 s)

dropSpace :: String -> String
dropSpace = dropWhile (`elem` " \t\n\r")
