-- | Eidos.WasmFFI
--
-- JSON bundle parsing for the Wasm stdin/stdout protocol.
--
-- 'compileBundleFromJSON' is called from 'WasmMain.main': it decodes the
-- JSON object read from stdin, delegates to 'Eidos.Wasm.compileBundle',
-- and returns the result string that main writes to stdout.
--
-- The JSON parser is hand-rolled (no aeson dependency) and handles only
-- the flat @{ "key": "value", ... }@ shape that the protocol uses.

module WasmFFI
  ( compileBundleFromJSON
  ) where

import qualified Data.Map.Strict as Map
import Eidos.Wasm.Wasm (compileBundle)

-- ---------------------------------------------------------------------------
-- Top-level entry point
-- ---------------------------------------------------------------------------

-- | Decode a JSON bundle string and compile it.
-- Returns Lean 4 output or an @"Error: …"@ string.
compileBundleFromJSON :: String -> String
compileBundleFromJSON json =
  case parseSimpleStringMap json of
    Left  err    -> "Error: JSON parse error: " ++ err
    Right pairs  -> compileBundle (Map.fromList pairs)

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
    go []            _   = Left "unterminated string"
    go ('"'  : t)   acc  = Right (reverse acc, t)
    go ('\\' : c : t) acc = go t (unescape c : acc)
    go (c    : t)   acc  = go t (c : acc)
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
