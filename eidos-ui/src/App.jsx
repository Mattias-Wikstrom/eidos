import { useEffect, useMemo, useState } from 'react';
import Editor from '@monaco-editor/react';
import { useEidos } from './useEidos';
import './App.css';

const theoryModules = import.meta.glob('./demo-theories/*.theory', {
  query: '?raw',
  import: 'default',
});

const ENTRY_FILE = '__main__.theory';
const RESERVED_BUNDLE_KEY = '__main__';
const THEORY_TYPE_META_PREFIX = '__theory_type__.';
const REFERENCE_KEY_PATTERN = /^[A-Za-z0-9_.-]+$/;

const theoryEntries = Object.keys(theoryModules)
  .map((path) => ({ path, name: path.split('/').pop() }))
  .sort((a, b) => a.name.localeCompare(b.name));

const TYPE_TAG_COLORS = {
  eq:    '#c8a96e',
  reg:   '#7eb8c8',
  coh:   '#9ec87e',
  fol:   '#c87eb8',
  sol:   '#e0876a',
  prop:  '#a08ec8',
  mereo: '#6abfa8',
  plain: '#555',
};

function TheoryTypeTag({ tag }) {
  const color = TYPE_TAG_COLORS[tag] || TYPE_TAG_COLORS.plain;
  return (
    <span style={{
      fontSize: '9px',
      fontFamily: 'var(--font-mono)',
      letterSpacing: '0.06em',
      color,
      border: `1px solid ${color}55`,
      borderRadius: '2px',
      padding: '1px 4px',
      marginLeft: '6px',
      verticalAlign: 'middle',
    }}>
      {tag}
    </span>
  );
}

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
  const [outputIsError, setOutputIsError] = useState(false);

  const selectedPath = useMemo(
    () => theoryEntries.find((e) => e.name === selectedTheory)?.path,
    [selectedTheory]
  );

  const fileNames = useMemo(() => Object.keys(files).sort(), [files]);

  useEffect(() => {
    if (!selectedPath) return;
    let cancelled = false;
    (async () => {
      const loadedFiles = {};
      await Promise.all(
        theoryEntries.map(async (entry) => {
          loadedFiles[entry.name] = await theoryModules[entry.path]();
        })
      );
      if (!cancelled) {
        loadedFiles[ENTRY_FILE] = loadedFiles[selectedTheory] ?? '';
        setFiles(loadedFiles);
        setReferenceKeys(buildDefaultReferenceKeys(loadedFiles));
        setActiveFile(ENTRY_FILE);
        setEntryFile(ENTRY_FILE);
        setOutput('');
        setOutputIsError(false);
      }
    })();
    return () => { cancelled = true; };
  }, [selectedPath, selectedTheory]);

  const updateFileContent = (name, text) =>
    setFiles((prev) => ({ ...prev, [name]: text ?? '' }));

  const updateReferenceKey = (name, key) =>
    setReferenceKeys((prev) => ({ ...prev, [name]: key }));

  const addFile = () => {
    const name = window.prompt('New file name (e.g. group.eq.theory)');
    if (!name) return;
    if (files[name]) {
      setOutput(`Error: file "${name}" already exists.`);
      setOutputIsError(true);
      return;
    }
    setFiles((prev) => ({ ...prev, [name]: '' }));
    setReferenceKeys((prev) => ({ ...prev, [name]: defaultReferenceKey(name) }));
    setActiveFile(name);
  };

  const removeActiveFile = () => {
    if (activeFile === ENTRY_FILE) {
      setOutput(`Error: ${ENTRY_FILE} cannot be deleted.`);
      setOutputIsError(true);
      return;
    }
    const nextFiles = { ...files };
    delete nextFiles[activeFile];
    setFiles(nextFiles);
    setReferenceKeys((prev) => { const n = { ...prev }; delete n[activeFile]; return n; });
    if (entryFile === activeFile) setEntryFile(ENTRY_FILE);
    setActiveFile(ENTRY_FILE);
  };

  const compile = async () => {
    if (!eidos) return;
    try {
      const bundle = createBundle(files, referenceKeys, entryFile);
      setLoading(true);
      const result = await eidos.compileBundle(bundle);
      setOutput(result);
      setOutputIsError(result.startsWith('Error:'));
    } catch (err) {
      setOutput('Error: ' + (err instanceof Error ? err.message : String(err)));
      setOutputIsError(true);
    } finally {
      setLoading(false);
    }
  };

  const activeTag = inferTheoryTypeTag(activeFile);

  return (
    <div className="app-shell">
      <header className="app-header">
        <div className="header-wordmark">
          <span className="wordmark-eidos">Eidos</span>
          <span className="wordmark-arrow">→</span>
          <span className="wordmark-lean">Lean</span>
        </div>
        <div className="header-controls">
          <div className="control-group">
            <label className="control-label">starter theory</label>
            <div className="select-wrap">
              <select
                value={selectedTheory}
                onChange={(e) => setSelectedTheory(e.target.value)}
                className="styled-select"
              >
                {theoryEntries.map((entry) => (
                  <option key={entry.path} value={entry.name}>{entry.name}</option>
                ))}
              </select>
            </div>
          </div>
          <div className="control-group">
            <label className="control-label">entry file</label>
            <div className="select-wrap">
              <select
                value={entryFile}
                onChange={(e) => setEntryFile(e.target.value)}
                className="styled-select"
              >
                {fileNames.map((name) => (
                  <option key={name} value={name}>{name}</option>
                ))}
              </select>
            </div>
          </div>
          <div className="control-group">
            <label className="control-label">mode</label>
            <div className="select-wrap">
              <select
                value={compileMode}
                onChange={(e) => setCompileMode(e.target.value)}
                className="styled-select"
              >
                <option value="lean_using_props">--lean_using_props</option>
                <option value="lean">--lean</option>
              </select>
            </div>
          </div>
        </div>
      </header>

      <div className="app-body">
        <div className="editor-panel">
          <div className="tab-bar">
            <div className="tab-list">
              {fileNames.map((name) => {
                const tag = inferTheoryTypeTag(name);
                const isActive = name === activeFile;
                const isEntry = name === entryFile;
                return (
                  <button
                    key={name}
                    className={`tab ${isActive ? 'tab--active' : ''} ${isEntry ? 'tab--entry' : ''}`}
                    onClick={() => setActiveFile(name)}
                    title={name}
                  >
                    <span className="tab-name">{name}</span>
                    {tag !== 'plain' && <TheoryTypeTag tag={tag} />}
                    {isEntry && <span className="tab-entry-dot" title="entry file" />}
                  </button>
                );
              })}
            </div>
            <div className="tab-actions">
              <button className="icon-btn" onClick={addFile} title="Add file">＋</button>
              <button
                className="icon-btn icon-btn--danger"
                onClick={removeActiveFile}
                disabled={activeFile === ENTRY_FILE}
                title="Delete active file"
              >✕</button>
            </div>
          </div>

          <div className="editor-wrap">
            <Editor
              height="100%"
              defaultLanguage="plaintext"
              theme="vs-dark"
              value={files[activeFile] ?? ''}
              onChange={(value) => updateFileContent(activeFile, value ?? '')}
              options={{
                fontSize: 13,
                fontFamily: "'JetBrains Mono', 'Fira Code', 'Cascadia Code', monospace",
                fontLigatures: true,
                lineHeight: 20,
                minimap: { enabled: false },
                scrollBeyondLastLine: false,
                renderLineHighlight: 'gutter',
                padding: { top: 16, bottom: 16 },
              }}
            />
          </div>

          <div className="refkey-bar">
            <span className="refkey-label">ref key</span>
            <input
              type="text"
              className="refkey-input"
              value={referenceKeys[activeFile] ?? ''}
              onChange={(e) => updateReferenceKey(activeFile, e.target.value)}
              disabled={activeFile === entryFile}
              placeholder={activeFile === entryFile ? '__main__  (entry file)' : 'e.g. group'}
            />
            {activeFile !== entryFile && activeTag !== 'plain' && (
              <span className="refkey-type-hint">
                inferred type: <TheoryTypeTag tag={activeTag} />
              </span>
            )}
          </div>
        </div>

        <div className="output-panel">
          <div className="output-header">
            <span className="output-title">output</span>
            {wasmError && <span className="wasm-error-badge">wasm error</span>}
            <button
              className={`compile-btn ${loading ? 'compile-btn--loading' : ''}`}
              onClick={compile}
              disabled={!eidos || loading || loadingWasm}
            >
              {loadingWasm ? (
                <><span className="spinner" /> loading wasm…</>
              ) : loading ? (
                <><span className="spinner" /> compiling…</>
              ) : (
                'compile bundle'
              )}
            </button>
          </div>

          {wasmError && (
            <div className="wasm-error-msg">Wasm failed to load: {wasmError}</div>
          )}

          <pre className={`output-pre ${outputIsError ? 'output-pre--error' : output ? 'output-pre--success' : ''}`}>
            {output || <span className="output-placeholder">// output will appear here</span>}
          </pre>
        </div>
      </div>
    </div>
  );
}

function defaultReferenceKey(name) {
  return name.split('.')[0].trim();
}

function buildDefaultReferenceKeys(fileMap) {
  const keys = {};
  for (const fileName of Object.keys(fileMap)) {
    keys[fileName] = defaultReferenceKey(fileName);
  }
  return keys;
}

function inferTheoryTypeTag(fileName) {
  const lower = fileName.toLowerCase();
  if (lower.endsWith('.eq.theory'))    return 'eq';
  if (lower.endsWith('.reg.theory'))   return 'reg';
  if (lower.endsWith('.coh.theory'))   return 'coh';
  if (lower.endsWith('.fol.theory'))   return 'fol';
  if (lower.endsWith('.sol.theory'))   return 'sol';
  if (lower.endsWith('.prop.theory'))  return 'prop';
  if (lower.endsWith('.mereo.theory')) return 'mereo';
  return 'plain';
}

function createBundle(fileMap, refKeyMap, entryFile) {
  if (!Object.prototype.hasOwnProperty.call(fileMap, entryFile)) {
    throw new Error(`Entry file "${entryFile}" does not exist.`);
  }
  const bundle = {};
  const seenRefKeys = new Set();
  for (const [fileName, src] of Object.entries(fileMap)) {
    if (fileName === entryFile) { bundle[RESERVED_BUNDLE_KEY] = src; continue; }
    const key = (refKeyMap[fileName] ?? '').trim();
    if (!key) throw new Error(`File "${fileName}" is missing a reference key.`);
    if (key === RESERVED_BUNDLE_KEY) throw new Error(`Key "${RESERVED_BUNDLE_KEY}" is reserved.`);
    if (!REFERENCE_KEY_PATTERN.test(key)) throw new Error(`Key "${key}" for "${fileName}" is invalid.`);
    if (seenRefKeys.has(key)) throw new Error(`Key "${key}" is duplicated.`);
    seenRefKeys.add(key);
    bundle[key] = src;
    bundle[`${THEORY_TYPE_META_PREFIX}${key}`] = inferTheoryTypeTag(fileName);
  }
  return bundle;
}
