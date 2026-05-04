# Eidos → WebAssembly

This directory contains the Node.js glue layer for running the Eidos compiler
as a WebAssembly module.

## Architecture

GHC's Wasm backend compiles to a **WASI command** — a module whose sole export
is `_start`.  Individual Haskell functions cannot be exported as callable Wasm
exports with the current toolchain.  Instead, the JS host runs the module as a
self-contained process and communicates via stdin/stdout:

```
JS host                          Wasm module (_start)
──────                           ────────────────────
JSON bundle → stdin    ───────►  main: getContents
                                   │ compileBundleFromJSON
stdout ◄──────────────────────     putStr (Lean 4 or "Error: …")
```

```
{ "__main__": "..theory source..",      ← stdin (UTF-8 JSON)
  "some.reference": "..dep source..",
  ...
}

<Lean 4 source text>                    ← stdout on success
Error: <message>                        ← stdout on failure
```

The JS glue (`wasm/eidos_wasm.mjs`) implements the WASI syscalls needed by
GHC's RTS from scratch, routing fd 0 (stdin) from an in-memory buffer and
capturing fd 1 (stdout) into an in-memory buffer.  No real filesystem access
is needed and no child processes are spawned — everything runs inside the
same Node.js process using `WebAssembly.instantiate`.

The compiled `WebAssembly.Module` object is cached after the first call, so
only the first compilation pays the parse cost.  Each `compileSingle` /
`compileBundle` call creates a fresh `WebAssembly.Instance` from the cached
module, which is cheap.

## Prerequisites

Install the GHC Wasm toolchain via `ghcup`:

```bash
ghcup config add-release-channel \
  https://ghc.gitlab.haskell.org/ghcup-metadata/ghcup-cross-0.0.9.yaml
ghcup install ghc wasm32-wasi-9.12   # match your project's GHC version
```

Check availability:

```bash
wasm32-wasi-ghc    --version
wasm32-wasi-cabal  --version
```

## Build

From the project root:

```bash
# 1. Compile to Wasm
wasm32-wasi-cabal build exe:eidos-wasm

# 2. Copy the output
cp $(wasm32-wasi-cabal list-bin exe:eidos-wasm) wasm/eidos.wasm

# 3. (Optional) optimise — no special export flags needed
wasm-opt -O2 wasm/eidos.wasm -o wasm/eidos.wasm
```

## Run

```bash
node wasm/demo.mjs
```

Node.js 18+ is required.

## JavaScript API

```js
import { loadEidos } from './wasm/eidos_wasm.mjs';

const eidos = await loadEidos('./wasm/eidos.wasm');

// Single theory, no @-references:
const lean = await eidos.compileSingle(`{
  signature { P : ℙ; Q : ℙ; },
  axioms { assertions { P → Q; } }
}`);

// Bundle with dependencies:
const lean2 = await eidos.compileBundle({
  '__main__': '{ subtheories { foundations: @foundations; }, signature { S ⊆ 𝕌; } }',
  'foundations': '{ signature { Empty : 𝕌; } }',
});
```

Both methods return a `Promise<string>`.  On failure the string begins with
`"Error: "`.

## Handling @-references in JavaScript

When a theory uses `@some.reference`, your JS host must supply the dependency
source in the bundle.  A simple recursive file loader:

```js
import { readFile } from 'node:fs/promises';

async function buildBundle(mainPath) {
  const bundle = {};
  const queue  = [['__main__', mainPath]];
  while (queue.length > 0) {
    const [key, path] = queue.shift();
    if (bundle[key]) continue;
    const src = await readFile(path, 'utf8');
    bundle[key] = src;
    for (const m of src.matchAll(/@([\w.]+)/g)) {
      const ref = m[1];
      if (!bundle[ref])
        queue.push([ref, ref.replaceAll('.', '/') + '.theory']);
    }
  }
  return bundle;
}

const lean = await eidos.compileBundle(await buildBundle('my.theory'));
```

## Web page usage (future)

For in-browser use the architecture is identical — `WebAssembly.instantiate`
works in browsers too.  Replace `readFile` with `fetch` for loading the
`.wasm` file and dependency sources.  The WASI syscall stubs in
`eidos_wasm.mjs` are already environment-agnostic (no Node.js APIs are used
inside them), so only the `loadEidos` loader function needs a browser variant.
