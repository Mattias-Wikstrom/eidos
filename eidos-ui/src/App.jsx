import { useEffect, useMemo, useState } from 'react';
import Editor from '@monaco-editor/react';
import { useEidos } from './useEidos';

const theoryModules = import.meta.glob('./demo-theories/*.theory', {
  query: '?raw',
  import: 'default',
});

const ENTRY_FILE = '__main__.theory';
const RESERVED_BUNDLE_KEY = '__main__';
const REFERENCE_KEY_PATTERN = /^[A-Za-z0-9_.-]+$/;

const theoryEntries = Object.keys(theoryModules)
  .map((path) => ({
    path,
    name: path.split('/').pop(),
  }))
  .sort((a, b) => a.name.localeCompare(b.name));

export default function App() {
  const { eidos, loadingWasm, wasmError } = useEidos();
  const [selectedTheory, setSelectedTheory] = useState(theoryEntries[0]?.name ?? '');
  const [files, setFiles] = useState({ [ENTRY_FILE]: '' });
  const [referenceKeys, setReferenceKeys] = useState({});
  const [activeFile, setActiveFile] = useState(ENTRY_FILE);
  const [entryFile, setEntryFile] = useState(ENTRY_FILE);
  const [compileMode, setCompileMode] = useState('lean_using_props');
  const [output, setOutput] = useState('');
  const [loading, setLoading] = useState(false);

  const selectedPath = useMemo(
    () => theoryEntries.find((entry) => entry.name === selectedTheory)?.path,
    [selectedTheory]
  );

  const fileNames = useMemo(() => Object.keys(files).sort(), [files]);

  useEffect(() => {
    if (!selectedPath) return;

    let cancelled = false;

    (async () => {
      const loadedFiles = {};
      const loadTasks = theoryEntries.map(async (entry) => {
        const text = await theoryModules[entry.path]();
        loadedFiles[entry.name] = text;
      });

      await Promise.all(loadTasks);

      if (!cancelled) {
        loadedFiles[ENTRY_FILE] = loadedFiles[selectedTheory] ?? '';
        setFiles(loadedFiles);
        setReferenceKeys(buildDefaultReferenceKeys(loadedFiles));
        setActiveFile(ENTRY_FILE);
        setEntryFile(ENTRY_FILE);
        setOutput('');
      }
    })();

    return () => {
      cancelled = true;
    };
  }, [selectedPath, selectedTheory]);

  const updateFileContent = (name, text) => {
    setFiles((prev) => ({ ...prev, [name]: text }));
  };

  const updateReferenceKey = (name, key) => {
    setReferenceKeys((prev) => ({ ...prev, [name]: key }));
  };

  const addFile = () => {
    const name = window.prompt('New file name (for example: group.eq.theory)');
    if (!name) return;
    if (files[name]) {
      setOutput(`Error: file "${name}" already exists.`);
      return;
    }
    setFiles((prev) => ({ ...prev, [name]: '' }));
    setReferenceKeys((prev) => ({ ...prev, [name]: defaultReferenceKey(name) }));
    setActiveFile(name);
  };

  const removeActiveFile = () => {
    if (activeFile === ENTRY_FILE) {
      setOutput(`Error: ${ENTRY_FILE} cannot be deleted.`);
      return;
    }
    const nextFiles = { ...files };
    delete nextFiles[activeFile];
    setFiles(nextFiles);
    setReferenceKeys((prev) => {
      const nextKeys = { ...prev };
      delete nextKeys[activeFile];
      return nextKeys;
    });
    if (entryFile === activeFile) setEntryFile(ENTRY_FILE);
    setActiveFile(ENTRY_FILE);
  };

  const compileWithMode = async (bundle) => {
    if (compileMode === 'lean_using_props') {
      return eidos.compileBundle(bundle);
    }

    if (compileMode === 'lean') {
      if (typeof eidos.compileBundleWithMode === 'function') {
        return eidos.compileBundleWithMode(bundle, { mode: 'lean' });
      }
      throw new Error(
        'Compile mode "--lean" is selected, but the current Wasm runtime does not expose mode-aware compilation yet.'
      );
    }

    throw new Error(`Unsupported compile mode: ${compileMode}`);
  };

  const compile = async () => {
    if (!eidos) return;

    try {
      const bundle = createBundle(files, referenceKeys, entryFile);
      setLoading(true);
      const result = await compileWithMode(bundle);
      setOutput(result);
    } catch (err) {
      setOutput('Error: ' + (err instanceof Error ? err.message : String(err)));
    } finally {
      setLoading(false);
    }
  };

  return (
    <div style={{ padding: 20, fontFamily: 'sans-serif' }}>
      <h1>Eidos → Lean</h1>
      <label htmlFor="theory-select" style={{ display: 'block', marginBottom: 8 }}>
        Starter theory
      </label>
      <select
        id="theory-select"
        value={selectedTheory}
        onChange={(event) => setSelectedTheory(event.target.value)}
        style={{ marginBottom: 12, minWidth: 360 }}
      >
        {theoryEntries.map((entry) => (
          <option key={entry.path} value={entry.name}>
            {entry.name}
          </option>
        ))}
      </select>

      <div style={{ display: 'flex', gap: 12, marginBottom: 8, alignItems: 'center', flexWrap: 'wrap' }}>
        <label htmlFor="entry-select">Entry file:</label>
        <select id="entry-select" value={entryFile} onChange={(event) => setEntryFile(event.target.value)}>
          {fileNames.map((name) => (
            <option key={name} value={name}>
              {name}
            </option>
          ))}
        </select>
        <label htmlFor="mode-select">Mode:</label>
        <select id="mode-select" value={compileMode} onChange={(event) => setCompileMode(event.target.value)}>
          <option value="lean_using_props">--lean_using_props</option>
          <option value="lean">--lean</option>
        </select>
        <button onClick={addFile}>Add file</button>
        <button onClick={removeActiveFile} disabled={activeFile === ENTRY_FILE}>
          Delete active file
        </button>
      </div>

      <div style={{ display: 'flex', gap: 10, marginBottom: 8, flexWrap: 'wrap' }}>
        {fileNames.map((name) => (
          <button
            key={name}
            onClick={() => setActiveFile(name)}
            style={{
              padding: '4px 8px',
              border: name === activeFile ? '2px solid #2c7' : '1px solid #ccc',
              borderRadius: 4,
              background: name === activeFile ? '#f4fff8' : '#fff',
            }}
          >
            {name}
          </button>
        ))}
      </div>

      <Editor
        height="420px"
        defaultLanguage="plaintext"
        value={files[activeFile] ?? ''}
        onChange={(value) => updateFileContent(activeFile, value ?? '')}
      />

      <div style={{ marginTop: 12 }}>
        <label htmlFor="reference-key-input" style={{ display: 'block', marginBottom: 4 }}>
          Reference key for active file
        </label>
        <input
          id="reference-key-input"
          type="text"
          value={referenceKeys[activeFile] ?? ''}
          onChange={(event) => updateReferenceKey(activeFile, event.target.value)}
          disabled={activeFile === entryFile}
          placeholder={activeFile === entryFile ? 'Entry file maps to __main__' : 'e.g. group'}
          style={{ minWidth: 320 }}
        />
      </div>

      {wasmError && (
        <div style={{ marginTop: 10, color: '#b00020' }}>
          Wasm failed to load: {wasmError}
        </div>
      )}

      <button onClick={compile} disabled={!eidos || loading || loadingWasm} style={{ marginTop: 12 }}>
        {loadingWasm ? 'Loading Wasm...' : loading ? 'Compiling...' : 'Compile bundle'}
      </button>

      <pre
        style={{
          marginTop: 20,
          background: '#111',
          color: '#0f0',
          padding: 10,
          whiteSpace: 'pre-wrap',
        }}
      >
        {output}
      </pre>
    </div>
  );
}

function defaultReferenceKey(name) {
  return name.replace(/\.theory$/i, '').trim();
}

function buildDefaultReferenceKeys(fileMap) {
  const keys = {};
  for (const fileName of Object.keys(fileMap)) {
    keys[fileName] = defaultReferenceKey(fileName);
  }
  return keys;
}

function createBundle(fileMap, refKeyMap, entryFile) {
  if (!Object.prototype.hasOwnProperty.call(fileMap, entryFile)) {
    throw new Error(`Entry file "${entryFile}" does not exist.`);
  }

  const bundle = {};
  const seenRefKeys = new Set();

  for (const [fileName, src] of Object.entries(fileMap)) {
    if (fileName === entryFile) {
      bundle[RESERVED_BUNDLE_KEY] = src;
      continue;
    }

    const key = (refKeyMap[fileName] ?? '').trim();
    if (!key) {
      throw new Error(`File "${fileName}" is missing a reference key.`);
    }
    if (key === RESERVED_BUNDLE_KEY) {
      throw new Error(`Reference key "${RESERVED_BUNDLE_KEY}" is reserved for the entry file.`);
    }
    if (!REFERENCE_KEY_PATTERN.test(key)) {
      throw new Error(
        `Reference key "${key}" for "${fileName}" is invalid. Allowed characters: A-Z a-z 0-9 _ . -`
      );
    }
    if (seenRefKeys.has(key)) {
      throw new Error(`Reference key "${key}" is duplicated. Keys must be unique across the bundle.`);
    }

    seenRefKeys.add(key);
    bundle[key] = src;
  }

  return bundle;
}
