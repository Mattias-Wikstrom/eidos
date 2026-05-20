/**
 * eidos_wasm.mjs — Universal glue for the Eidos Wasm module
 *
 * Works in Node.js (>= 18) and in browsers (as an ES module).
 *
 * The Eidos Wasm module is compiled as a WASI command whose only export
 * is _start.  This glue instantiates it, feeds a JSON bundle to stdin,
 * and captures Lean 4 output from stdout — all in memory, no filesystem.
 *
 * Usage (Node.js)
 * ---------------
 *   import { loadEidos } from './eidos_wasm.mjs';
 *   const eidos = await loadEidos(new URL('./eidos.wasm', import.meta.url));
 *   const lean  = await eidos.compileSingle('{ signature { P : ℙ; } }');
 *
 * Usage (browser)
 * ---------------
 *   import { loadEidos } from './eidos_wasm.mjs';
 *   const eidos = await loadEidos(new URL('./eidos.wasm', import.meta.url));
 *   const lean  = await eidos.compileSingle('{ signature { P : ℙ; } }');
 *
 * Loading the .wasm file
 * ----------------------
 * Pass anything that fetch() or WebAssembly.compileStreaming() can accept:
 * a URL object, a URL string, or (Node.js only) a file path string.
 * The loader tries compileStreaming first (browser-optimal) and falls
 * back to fetch + compile for environments that lack streaming compilation.
 */

const ENC = new TextEncoder();
const DEC = new TextDecoder();

// ---------------------------------------------------------------------------
// Portable byte-buffer helpers (no Buffer, no Node APIs)
// ---------------------------------------------------------------------------

function concatChunks(chunks) {
  const total  = chunks.reduce((n, c) => n + c.length, 0);
  const result = new Uint8Array(total);
  let offset = 0;
  for (const c of chunks) { result.set(c, offset); offset += c.length; }
  return result;
}

// ---------------------------------------------------------------------------
// Module cache — compile once, instantiate per call
// ---------------------------------------------------------------------------

let _compiledModule = null;

async function getModule(wasmPath) {
  if (_compiledModule) return _compiledModule;
  // compileStreaming is the most efficient path in browsers.
  // It also works in Node >= 22 when given a URL.
  // Fall back to fetch + compile for older Node or plain string paths.
  try {
    _compiledModule = await WebAssembly.compileStreaming(fetch(wasmPath.toString()));
  } catch (_) {
    const response = await fetch(wasmPath.toString());
    const bytes    = await response.arrayBuffer();
    _compiledModule = await WebAssembly.compile(bytes);
  }
  return _compiledModule;
}

// ---------------------------------------------------------------------------
// Run the Wasm module once with a given stdin payload
// ---------------------------------------------------------------------------

async function runWasm(wasmPath, inputJson) {
  const mod        = await getModule(wasmPath);
  const inputBytes = ENC.encode(inputJson);

  const stdoutChunks = [];
  const stderrChunks = [];
  let   stdinOffset  = 0;

  const memory = { ref: null };
  const view   = () => new DataView(memory.ref.buffer);
  const u8     = (ptr, len) => new Uint8Array(memory.ref.buffer, ptr, len);

  const wasi = {
    // ── args / environ ──────────────────────────────────────────────────
    args_get:          () => 0,
    args_sizes_get:    () => 0,
    environ_get:       () => 0,
    environ_sizes_get: () => 0,

    // ── clock ───────────────────────────────────────────────────────────
    clock_time_get: (_id, _prec, ptime) => {
      view().setBigUint64(ptime, BigInt(Date.now()) * 1_000_000n, true);
      return 0;
    },

    // ── fd_close ────────────────────────────────────────────────────────
    fd_close: () => 0,

    // ── fd_fdstat_get ───────────────────────────────────────────────────
    // GHC's RTS queries this to determine whether fds 0/1/2 are seekable.
    // Reporting filetype=2 (character_device) tells it they are not.
    fd_fdstat_get: (_fd, statPtr) => {
      // __wasi_fdstat_t: u8 filetype, u8 pad, u16 flags, u32 pad, u64 rights_base, u64 rights_inh
      view().setUint8(statPtr,       2);   // character_device
      view().setUint8(statPtr + 1,   0);
      view().setUint16(statPtr + 2,  0,    true);
      view().setBigUint64(statPtr + 8,  0xFFFFFFFFFFFFFFFFn, true);
      view().setBigUint64(statPtr + 16, 0xFFFFFFFFFFFFFFFFn, true);
      return 0;
    },

    fd_fdstat_set_flags:  () => 0,
    fd_filestat_get:      () => 8,
    fd_filestat_set_size: () => 8,

    // ── fd_prestat_get ──────────────────────────────────────────────────
    fd_prestat_get:      () => 8,   // EBADF — no preopened directories
    fd_prestat_dir_name: () => 8,

    // ── fd_read (stdin) ─────────────────────────────────────────────────
    fd_read: (fd, iovsPtr, iovsLen, nreadPtr) => {
      if (fd !== 0) return 8;
      let total = 0;
      for (let i = 0; i < iovsLen; i++) {
        const bufPtr    = view().getUint32(iovsPtr + i * 8,     true);
        const bufLen    = view().getUint32(iovsPtr + i * 8 + 4, true);
        const remaining = inputBytes.length - stdinOffset;
        if (remaining <= 0) break;
        const n = Math.min(bufLen, remaining);
        u8(bufPtr, n).set(inputBytes.subarray(stdinOffset, stdinOffset + n));
        stdinOffset += n;
        total += n;
      }
      view().setUint32(nreadPtr, total, true);
      return 0;
    },

    fd_seek: () => 8,

    // ── fd_write (stdout / stderr) ──────────────────────────────────────
    fd_write: (fd, iovsPtr, iovsLen, nwrittenPtr) => {
      let total = 0;
      for (let i = 0; i < iovsLen; i++) {
        const base  = view().getUint32(iovsPtr + i * 8,     true);
        const len   = view().getUint32(iovsPtr + i * 8 + 4, true);
        const chunk = u8(base, len).slice();
        if (fd === 1) stdoutChunks.push(chunk);
        else          stderrChunks.push(chunk);
        total += len;
      }
      view().setUint32(nwrittenPtr, total, true);
      return 0;
    },

    // ── path ────────────────────────────────────────────────────────────
    path_create_directory: () => 8,
    path_filestat_get:     () => 8,
    path_open:             () => 8,

    // ── poll ────────────────────────────────────────────────────────────
    poll_oneoff: () => 8,

    // ── proc_exit ───────────────────────────────────────────────────────
    proc_exit: (code) => { throw { wasiExit: code }; },

    // ── random ──────────────────────────────────────────────────────────
    random_get: (bufPtr, bufLen) => {
      crypto.getRandomValues(u8(bufPtr, bufLen));
      return 0;
    },
  };

  const instance = await WebAssembly.instantiate(mod, {
    wasi_snapshot_preview1: wasi,
  });

  memory.ref = instance.exports.memory;

  try {
    instance.exports._start();
  } catch (e) {
    if (e && typeof e === 'object' && 'wasiExit' in e) {
      if (e.wasiExit !== 0) {
        const errText = DEC.decode(concatChunks(stderrChunks));
        return 'Error: process exited with code ' + e.wasiExit +
               (errText ? '\n' + errText : '');
      }
      // exit(0) — normal termination, fall through
    } else {
      throw e;
    }
  }

  if (stderrChunks.length > 0) {
    console.error(DEC.decode(concatChunks(stderrChunks)));
  }

  return DEC.decode(concatChunks(stdoutChunks));
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

export async function loadEidos(wasmPath) {
  await getModule(wasmPath);   // warm the cache
  return {
    /** Compile a single theory with no @-references.
     *  @param {string} src
     *  @param {string} [target] one of: lean_using_props, coq_using_props, lean_runtime, coq_runtime, mereological
     *  @returns {Promise<string>} */
    async compileSingle(src, target) {
      const bundle = { __main__: src };
      if (target) bundle.__target__ = target;
      return runWasm(wasmPath, JSON.stringify(bundle));
    },
    /** Compile a bundle; bundle['__main__'] is the entry theory.
     *  @param {Object} bundle
     *  @param {string} [target] one of: lean_using_props, coq_using_props, lean_runtime, coq_runtime, mereological
     *  @returns {Promise<string>} */
    async compileBundle(bundle, target) {
      const payload = target ? { ...bundle, __target__: target } : bundle;
      return runWasm(wasmPath, JSON.stringify(payload));
    },
  };
}