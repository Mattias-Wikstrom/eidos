/**
 * demo.mjs — Quick smoke-test for the Eidos Wasm module under Node.js
 *
 * Run after building:
 *   node wasm/demo.mjs
 *
 * Expected output: Lean 4 source text (or "Error: ..." if something went wrong).
 */

import { loadEidos } from './eidos_wasm.mjs';
import { fileURLToPath } from 'node:url';
import { dirname, join }  from 'node:path';

const __dir = dirname(fileURLToPath(import.meta.url));

async function main() {
  const eidos = await loadEidos(join(__dir, 'eidos.wasm'));

  // ── Test 1: single self-contained theory ──────────────────────────────────
  console.log('=== compileSingle ===');
  const src1 = `{
    signature { P : ℙ; Q : ℙ; },
    axioms { assertions { P → Q; } }
  }`;
  console.log(await eidos.compileSingle(src1));

  // ── Test 2: bundle with a dependency ─────────────────────────────────────
  console.log('\n=== compileBundle (with dependency) ===');
  const dep = `{ signature { Empty : 𝕌; } }`;
  const main_ = `{
    subtheories {
    implicit {
      base: @base,
    }
  },
  signature {
    sort D;
    sort E; // Used for non-zero elements
    multiplicative_inv: E → E;
    E subsort D; // The non-zero elements form a subdomain
  },
  axioms {
    metafacts {
      Empty = Empty;
    }
  }

  }`;
  console.log(await eidos.compileBundle({ '__main__': main_, 'base': dep }));

  // ── Test 3: error handling ────────────────────────────────────────────────
  console.log('\n=== error (bad syntax, expected to fail) ===');
  console.log(await eidos.compileSingle('this is not valid eidos'));
}

main().catch(err => { console.error(err); process.exit(1); });
