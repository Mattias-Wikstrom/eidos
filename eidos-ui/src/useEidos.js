// src/useEidos.js
import { useEffect, useState } from 'react';
import { loadEidos } from './wasm/eidos_wasm.mjs';

export function useEidos() {
  const [eidos, setEidos] = useState(null);
  const [loadingWasm, setLoadingWasm] = useState(true);
  const [wasmError, setWasmError] = useState(null);

  useEffect(() => {
    let cancelled = false;

    (async () => {
      setLoadingWasm(true);
      setWasmError(null);
      try {
        const instance = await loadEidos('/wasm/eidos.wasm');
        if (!cancelled) {
          setEidos(instance);
        }
      } catch (err) {
        if (!cancelled) {
          setWasmError(err instanceof Error ? err.message : String(err));
          setEidos(null);
        }
      } finally {
        if (!cancelled) {
          setLoadingWasm(false);
        }
      }
    })();

    return () => {
      cancelled = true;
    };
  }, []);

  return { eidos, loadingWasm, wasmError };
}
