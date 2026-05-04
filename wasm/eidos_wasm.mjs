/**
 * eidos_wasm.mjs — Node.js glue for the Eidos Wasm module
 *
 * The Eidos Wasm module is compiled as a WASI command (exports only
 * _start).  This glue layer runs it using Node's built-in WASI class,
 * passing the input JSON via stdin and reading Lean 4 output from stdout.
 *
 * Usage
 * -----
 *   import { loadEidos } from './eidos_wasm.mjs';
 *
 *   const eidos = await loadEidos(new URL('./eidos.wasm', import.meta.url));
 *
 *   // Compile a single self-contained theory:
 *   const lean = await eidos.compileSingle('{ signature { P : ℙ; } }');
 *
 *   // Compile a theory that @-references dependencies:
 *   const lean2 = await eidos.compileBundle({
 *     '__main__': '{ @base; signature { MySet ⊆ 𝕌; } }',
 *     'base':     '{ signature { Empty : 𝕌; } }',
 *   });
 *
 * Requirements
 * ------------
 *   Node.js >= 18  (WASI class, WebAssembly.compile from file)
 *
 * Note: compileSingle / compileBundle are async because each call
 * instantiates and runs the Wasm module fresh.  The compiled WebAssembly.Module
 * object is cached so only the first call pays the compilation cost.
 */

import { readFile }        from 'node:fs/promises';
import { WASI }            from 'node:wasi';
import { createRequire }   from 'node:module';

const ENC = new TextEncoder();
const DEC = new TextDecoder();

// ---------------------------------------------------------------------------
// Module cache — compile once, instantiate per call
// ---------------------------------------------------------------------------

let _compiledModule = null;

async function getModule(wasmPath) {
  if (!_compiledModule) {
    const bytes = await readFile(wasmPath);
    _compiledModule = await WebAssembly.compile(bytes);
  }
  return _compiledModule;
}

// ---------------------------------------------------------------------------
// Run the Wasm module once with a given stdin payload
// ---------------------------------------------------------------------------

async function runWasm(wasmPath, inputJson) {
  const mod = await getModule(wasmPath);

  // Encode the input we will feed to stdin.
  const inputBytes = ENC.encode(inputJson);

  // Buffers for capturing stdout / stderr.
  const stdoutChunks = [];
  const stderrChunks = [];

  // Build a minimal in-memory file-descriptor table:
  //   fd 0 = stdin  (our input bytes)
  //   fd 1 = stdout (captured)
  //   fd 2 = stderr (forwarded to process.stderr for debugging)
  let stdinOffset = 0;

  // We implement WASI ourselves rather than using Node's WASI class because
  // Node's WASI class requires real file descriptors and does not support
  // in-memory stdin/stdout.  We only need the small subset that GHC's RTS
  // actually calls (verified from the import list above).

  const memory = { ref: null };  // filled after instantiation

  function view()  { return new DataView(memory.ref.buffer); }
  function u8(ptr, len) { return new Uint8Array(memory.ref.buffer, ptr, len); }

  const wasi = {
    // ── args / environ ──────────────────────────────────────────────────
    args_get:             () => 0,
    args_sizes_get:       () => 0,
    environ_get:          () => 0,
    environ_sizes_get:    () => 0,

    // ── clock ───────────────────────────────────────────────────────────
    clock_time_get: (_id, _prec, ptime) => {
      view().setBigUint64(ptime, BigInt(Date.now()) * 1_000_000n, true);
      return 0;
    },

    // ── fd_close ────────────────────────────────────────────────────────
    fd_close: () => 0,

    // ── fd_fdstat_get ───────────────────────────────────────────────────
    // GHC's RTS calls this on fd 0/1/2 to check if they are seekable.
    // We report filetype = 2 (regular file would be 4, but character device
    // = 2 signals "not seekable" which is what we want for pipes).
    fd_fdstat_get: (fd, statPtr) => {
      //   __wasi_fdstat_t layout (24 bytes):
      //   u8  fs_filetype        offset 0
      //   u8  padding            offset 1
      //   u16 fs_flags           offset 2
      //   u32 padding            offset 4
      //   u64 fs_rights_base     offset 8
      //   u64 fs_rights_inheriting offset 16
      view().setUint8(statPtr,      2);   // filetype = character_device
      view().setUint8(statPtr + 1,  0);
      view().setUint16(statPtr + 2, 0, true);
      view().setBigUint64(statPtr + 8,  0xFFFFFFFFFFFFFFFFn, true);
      view().setBigUint64(statPtr + 16, 0xFFFFFFFFFFFFFFFFn, true);
      return 0;
    },

    fd_fdstat_set_flags:  () => 0,
    fd_filestat_get:      () => 8,   // ENOSYS
    fd_filestat_set_size: () => 8,

    // ── fd_prestat_get ──────────────────────────────────────────────────
    // Return EBADF (8) for all fds — signals "no preopened directories".
    fd_prestat_get:      () => 8,
    fd_prestat_dir_name: () => 8,

    // ── fd_read (stdin) ─────────────────────────────────────────────────
    fd_read: (fd, iovsPtr, iovsLen, nreadPtr) => {
      if (fd !== 0) return 8;  // only stdin is readable
      let total = 0;
      for (let i = 0; i < iovsLen; i++) {
        const bufPtr = view().getUint32(iovsPtr + i * 8,     true);
        const bufLen = view().getUint32(iovsPtr + i * 8 + 4, true);
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
        const base = view().getUint32(iovsPtr + i * 8,     true);
        const len  = view().getUint32(iovsPtr + i * 8 + 4, true);
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
    proc_exit: (code) => {
      // Throw a special object so we can distinguish a clean exit(0) from
      // a real error.
      throw { wasiExit: code };
    },

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
        const errText = DEC.decode(Buffer.concat(stderrChunks));
        return 'Error: process exited with code ' + e.wasiExit +
               (errText ? '\n' + errText : '');
      }
      // exit(0) — normal termination
    } else {
      throw e;
    }
  }

  // Forward any stderr output for debugging.
  if (stderrChunks.length > 0) {
    process.stderr.write(Buffer.concat(stderrChunks));
  }

  return DEC.decode(Buffer.concat(stdoutChunks));
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

export async function loadEidos(wasmPath) {
  // Pre-compile the module so the first call isn't slower than the rest.
  await getModule(wasmPath);

  return {
    /**
     * Compile a single theory with no @-references.
     * @param {string} src  EidosLang source.
     * @returns {Promise<string>}  Lean 4 output or "Error: …".
     */
    async compileSingle(src) {
      return runWasm(wasmPath, JSON.stringify({ __main__: src }));
    },

    /**
     * Compile a bundle of theories.
     * @param {Object.<string,string>} bundle
     *   '__main__' → entry theory source; other keys → @-importable deps.
     * @returns {Promise<string>}  Lean 4 output or "Error: …".
     */
    async compileBundle(bundle) {
      return runWasm(wasmPath, JSON.stringify(bundle));
    },
  };
}
