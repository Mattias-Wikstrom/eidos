-- | WasmFFI
--
-- JSON bundle parsing for the Wasm stdin/stdout protocol.
--
-- 'compileBundleFromJSON' is called from 'WasmMain.main': it decodes the
-- JSON object read from stdin, delegates to 'Eidos.Wasm.compileBundleWithTypes',
-- and returns the result string that main writes to stdout.
--
-- The JSON parser is hand-rolled (no aeson dependency) and handles only
-- the flat @{ "key": "value", ... }@ shape that the protocol uses.
--
-- Typed dependency metadata (optional):
--   { "__main__": "...",
--     "group": "...",
--     "__theory_type__.group": "eq" }
--
-- Allowed type tags: plain, eq, reg, coh, fol, sol, prop, mereo.

module WasmFFI
  ( compileBundleFromJSON
  ) where

import qualified Data.Map.Strict as Map
import Eidos.Entrypoints.Wasm.Wasm (compileBundleWithTypes, mainKey, targetKey, resolveTarget)
import Eidos.Pipeline.Resolution.ExternalRef (TheoryType(..))

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

-- | Decode a JSON bundle string and compile it.
-- Returns Lean 4 output or an @"Error: …"@ string.
compileBundleFromJSON :: String -> String
compileBundleFromJSON json =
  case parseSimpleStringMap json of
    Left  err   -> "Error: JSON parse error: " ++ err
    Right pairs ->
      let target     = resolveTarget (lookup targetKey pairs)
          pairsClean = filter ((/= targetKey) . fst) pairs
      in case buildTypedBundle pairsClean of
        Left  err             -> "Error: bundle metadata error: " ++ err
        Right (mainSrc, deps) -> compileBundleWithTypes target mainSrc deps

-- ---------------------------------------------------------------------------
-- Bundle metadata handling
-- ---------------------------------------------------------------------------

theoryTypePrefix :: String
theoryTypePrefix = "__theory_type__."

buildTypedBundle :: [(String, String)] -> Either String (String, [(String, String, TheoryType)])
buildTypedBundle entries = do
  mainSrc <- case lookup mainKey entries of
    Nothing  -> Left $ "bundle does not contain a \"" ++ mainKey ++ "\" entry"
    Just src -> Right src
  depTypeMap <- parseTypeMetadata entries
  let dependencies =
        [ (ref, src, Map.findWithDefault PlainTheory ref depTypeMap)
        | (ref, src) <- entries
        , ref /= mainKey
        , not (isTheoryTypeMetadataKey ref)
        ]
  Right (mainSrc, dependencies)

parseTypeMetadata :: [(String, String)] -> Either String (Map.Map String TheoryType)
parseTypeMetadata entries = foldl step (Right Map.empty) entries
  where
    step acc (k, v)
      | not (isTheoryTypeMetadataKey k) = acc
      | otherwise = do
          current <- acc
          let ref = drop (length theoryTypePrefix) k
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

-- ---------------------------------------------------------------------------
-- Minimal flat-JSON parser
-- ---------------------------------------------------------------------------
-- Supports only: { "string": "string", ... }
-- Handles standard JSON string escapes: \" \\ \/ \n \t \r

parseSimpleStringMap :: String -> Either String [(String, String)]
parseSimpleStringMap s =
  case dropSpace s of
    '{' : rest -> parseMembers (dropSpace rest) []
    _          -> Left "expected '{'"

parseMembers :: String -> [(String, String)] -> Either String [(String, String)]
parseMembers s acc =
  case s of
    '}' : _  -> Right (reverse acc)
    '"' : _  -> do
      (k, r1) <- parseJsonString s
      r2      <- expectColon (dropSpace r1)
      (v, r3) <- parseJsonString (dropSpace r2)
      let r4 = dropSpace r3
      case r4 of
        ',' : r5 -> parseMembers (dropSpace r5) ((k, v) : acc)
        '}'  : _ -> Right (reverse ((k, v) : acc))
        []       -> Right (reverse ((k, v) : acc))
        _        -> Left ("unexpected character: " ++ take 10 r4)
    _ -> Left ("expected '\"' or '}', got: " ++ take 10 s)

expectColon :: String -> Either String String
expectColon (':' : rest) = Right rest
expectColon s            = Left ("expected ':', got: " ++ take 10 s)

parseJsonString :: String -> Either String (String, String)
parseJsonString ('"' : rest) = go rest []
  where
    go []              _   = Left "unterminated string"
    go ('"'  : t)     acc  = Right (reverse acc, t)
    go ('\\' : c : t) acc  = go t (unescape c : acc)
    go (c    : t)     acc  = go t (c : acc)
    unescape '"'  = '"'
    unescape '\\' = '\\'
    unescape '/'  = '/'
    unescape 'n'  = '\n'
    unescape 't'  = '\t'
    unescape 'r'  = '\r'
    unescape c    = c
parseJsonString s = Left ("expected '\"', got: " ++ take 10 s)

dropSpace :: String -> String
dropSpace = dropWhile (`elem` " \t\n\r")
