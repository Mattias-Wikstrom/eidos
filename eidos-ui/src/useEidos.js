// src/useEidos.js
import { useEffect, useState } from 'react';
import { loadEidos } from './wasm/eidos_wasm.mjs';

export function useEidos() {
  const [eidos, setEidos] = useState(null);

  useEffect(() => {
    (async () => {
      const instance = await loadEidos('/wasm/eidos.wasm');
      setEidos(instance);
    })();
  }, []);

  return eidos;
}
