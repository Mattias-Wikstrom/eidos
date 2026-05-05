# Eidos UI

Browser UI for compiling Eidos theory bundles to Lean through the Wasm runtime.

## Runtime File Map

- `public/wasm/eidos.wasm`: Wasm binary loaded by the browser.
- `src/wasm/eidos_wasm.mjs`: browser glue that exposes `loadEidos(...)`.
- `src/useEidos.js`: initializes Wasm and exposes `{ eidos, loadingWasm, wasmError }`.
- `src/App.jsx`: editor + bundle construction + compile workflow.

## Bundle Contract (UI -> Wasm)

The UI sends a single JSON object to `compileBundle(...)`.

- The entry file is always mapped to `__main__`.
- Every non-entry file must provide an explicit reference key.
- Default key generation uses the filename stem before extensions (for example, `group.eq.theory` -> `group`).
- Each non-entry reference also gets a metadata key `__theory_type__.<ref>` so Wasm can enforce sublanguage constraints for imports.
- Reference keys must be unique across the bundle.
- `__main__` is reserved and cannot be used as a non-entry key.
- Allowed key characters are `[A-Za-z0-9_.-]`.

Example payload:

```json
{
  "__main__": "{ signature { P : 𝒫; } ... }",
  "group": "{ signature { G : S; } ... }",
  "__theory_type__.group": "eq",
  "ring.core": "{ signature { R : S; } ... }",
  "__theory_type__.ring.core": "plain"
}
```

Theory-type tags are inferred from filename suffixes (`.eq.theory`, `.coh.theory`, `.reg.theory`, `.fol.theory`, `.sol.theory`, `.prop.theory`, `.mereo.theory`); default is `plain`.

## Compile Modes

The UI exposes two compile modes:

- `--lean_using_props`: default path, calls `eidos.compileBundle(bundle)`.
- `--lean`: forward-compatible path for future mode-aware Wasm APIs.

If `--lean` is selected but the loaded runtime does not expose mode-aware compilation, the UI fails early with a clear error instead of silently compiling with the wrong mode.

## Development

Install dependencies and run dev server:

```bash
npm install
npm run dev
```

Build production assets:

```bash
npm run build
```
