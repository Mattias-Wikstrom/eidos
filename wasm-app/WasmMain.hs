-- | WasmMain.hs
--
-- WASI command entry point for the Eidos Wasm module.
--
-- GHC's current Wasm backend compiles to a WASI /command/ — a module whose
-- sole export is @_start@.  There is no way to export individual Haskell
-- functions as callable Wasm exports with the standard toolchain.
--
-- == Protocol (stdin → stdout)
--
-- The JS host writes a JSON object to stdin and reads the result from stdout.
--
-- Input (one JSON object, UTF-8, followed by EOF):
--
-- > { "__main__": "<theory source>",
-- >   "<ref>":    "<dependency source>",
-- >   ...
-- > }
--
-- Output (UTF-8 to stdout):
--
-- > <Lean 4 source>        -- on success
-- > Error: <message>       -- on failure (always prefixed with "Error: ")
--
-- The JS glue (wasm/eidos_wasm.mjs) uses Node's WASI class to run the
-- module as a child-process-like instance and captures its stdout.

module Main where

import System.IO   (hSetEncoding, stdin, stdout, utf8, hFlush)
import System.Exit (exitWith, ExitCode(..))

import WasmFFI (compileBundleFromJSON)

main :: IO ()
main = do
  hSetEncoding stdin  utf8
  hSetEncoding stdout utf8
  input  <- getContents
  let result = compileBundleFromJSON input
  putStr result
  hFlush stdout
