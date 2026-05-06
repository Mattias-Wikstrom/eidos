import { useEffect, useMemo, useRef, useState } from 'react';
import Editor from '@monaco-editor/react';
import JSZip from 'jszip';
import { useEidos } from './useEidos';
import './App.css';

// ── Project catalogue ────────────────────────────────────────────────────────
// Each project is a folder under src/projects/. Every .theory file in the
// folder is a dependency; the file whose basename matches the folder name is
// the main theory.

const projectModules = import.meta.glob('./projects/**/*.theory', {
  query: '?raw',
  import: 'default',
});

function buildProjectCatalogue() {
  const projects = {};
  for (const path of Object.keys(projectModules)) {
    // path: ./projects/<folder>/<file>.theory
    const parts = path.replace('./projects/', '').split('/');
    if (parts.length !== 2) continue;
    const [folder, file] = parts;
    if (!projects[folder]) projects[folder] = [];
    projects[folder].push({ file, path });
  }
  return projects; // { folder: [{ file, path }] }
}

const PROJECT_CATALOGUE = buildProjectCatalogue();
const PROJECT_NAMES = Object.keys(PROJECT_CATALOGUE).sort();

// ── Theory type helpers ──────────────────────────────────────────────────────

const TYPE_TAG_COLORS = {
  eq:    '#c8a96e',
  reg:   '#7eb8c8',
  coh:   '#9ec87e',
  fol:   '#c87eb8',
  sol:   '#e0876a',
  prop:  '#a08ec8',
  mereo: '#6abfa8',
};

function inferTypeTag(filename) {
  const f = filename.toLowerCase();
  if (f.endsWith('.eq.theory'))    return 'eq';
  if (f.endsWith('.reg.theory'))   return 'reg';
  if (f.endsWith('.coh.theory'))   return 'coh';
  if (f.endsWith('.fol.theory'))   return 'fol';
  if (f.endsWith('.sol.theory'))   return 'sol';
  if (f.endsWith('.prop.theory'))  return 'prop';
  if (f.endsWith('.mereo.theory')) return 'mereo';
  return null;
}

// Bundle key = everything before the first dot (matches @reference syntax)
function bundleKey(filename) {
  return filename.split('.')[0];
}

function TypeBadge({ tag }) {
  if (!tag) return null;
  const color = TYPE_TAG_COLORS[tag] || '#666';
  return (
    <span className="type-badge" style={{ color, borderColor: color + '55' }}>
      {tag}
    </span>
  );
}

// ── Main component ───────────────────────────────────────────────────────────

export default function App() {
  const { eidos, loadingWasm, wasmError } = useEidos();

  // files: { filename: string (content) }
  const [files, setFiles] = useState({});
  const [mainFile, setMainFile] = useState('');
  const [activeFile, setActiveFile] = useState('');
  const [projectName, setProjectName] = useState('');  // '' = blank/custom workspace
  const [isDirty, setIsDirty] = useState(false);

  const [output, setOutput] = useState('');
  const [outputIsError, setOutputIsError] = useState(false);
  const [compiling, setCompiling] = useState(false);

  const [showProjectPanel, setShowProjectPanel] = useState(false);
  const [newFileName, setNewFileName] = useState('');
  const newFileInputRef = useRef(null);

  const fileNames = useMemo(() => Object.keys(files).sort(), [files]);

  // ── Load a project ────────────────────────────────────────────────────────

  async function loadProject(name) {
    const entries = PROJECT_CATALOGUE[name];
    if (!entries) return;
    const loaded = {};
    await Promise.all(
      entries.map(async ({ file, path }) => {
        loaded[file] = await projectModules[path]();
      })
    );
    // Determine main file: filename whose stem == folder name
    const main = entries.find(({ file }) => bundleKey(file) === name)?.file
               ?? entries[0]?.file
               ?? '';
    setFiles(loaded);
    setMainFile(main);
    setActiveFile(main);
    setProjectName(name);
    setIsDirty(false);
    setOutput('');
    setOutputIsError(false);
    setShowProjectPanel(false);
  }

  // ── Blank workspace on first load ─────────────────────────────────────────

  useEffect(() => {
    const blank = 'main.theory';
    setFiles({ [blank]: '' });
    setMainFile(blank);
    setActiveFile(blank);
  }, []);

  // ── Edit ──────────────────────────────────────────────────────────────────

  function updateContent(name, text) {
    setFiles(prev => ({ ...prev, [name]: text ?? '' }));
    setIsDirty(true);
  }

  // ── Add file ──────────────────────────────────────────────────────────────

  function commitNewFile() {
    const name = newFileName.trim();
    if (!name) return;
    const fullName = name.endsWith('.theory') ? name : name + '.theory';
    if (files[fullName]) {
      alert(`"${fullName}" already exists.`);
      return;
    }
    setFiles(prev => ({ ...prev, [fullName]: '' }));
    setActiveFile(fullName);
    setNewFileName('');
    setIsDirty(true);
  }

  // ── Delete file ───────────────────────────────────────────────────────────

  function deleteFile(name) {
    if (name === mainFile) return; // can't delete main
    if (!confirm(`Delete "${name}"?`)) return;
    setFiles(prev => {
      const next = { ...prev };
      delete next[name];
      return next;
    });
    if (activeFile === name) setActiveFile(mainFile);
    setIsDirty(true);
  }

  // ── Set main file ─────────────────────────────────────────────────────────

  function setAsMain(name) {
    setMainFile(name);
    setIsDirty(true);
  }

  // ── Compile ───────────────────────────────────────────────────────────────

  async function compile() {
    if (!eidos) return;
    try {
      setCompiling(true);
      const bundle = buildBundle(files, mainFile);
      const result = await eidos.compileBundle(bundle);
      setOutput(result);
      setOutputIsError(result.trimStart().startsWith('Error'));
    } catch (err) {
      setOutput('Error: ' + (err instanceof Error ? err.message : String(err)));
      setOutputIsError(true);
    } finally {
      setCompiling(false);
    }
  }

  // ── Download zip ──────────────────────────────────────────────────────────

  async function downloadZip() {
    const zip = new JSZip();
    const folder = zip.folder(projectName || 'eidos-project');
    for (const [name, content] of Object.entries(files)) {
      folder.file(name, content);
    }
    const blob = await zip.generateAsync({ type: 'blob' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = (projectName || 'eidos-project') + '.zip';
    a.click();
    URL.revokeObjectURL(url);
    setIsDirty(false);
  }

  // ── Upload zip ────────────────────────────────────────────────────────────

  async function uploadZip(e) {
    const file = e.target.files?.[0];
    if (!file) return;
    e.target.value = '';
    if (isDirty && !confirm('Open this zip? Unsaved changes will be lost.')) return;
    const zip = await JSZip.loadAsync(file);
    const loaded = {};
    let inferredMain = '';
    const zipName = file.name.replace(/\.zip$/i, '');
    await Promise.all(
      Object.entries(zip.files).map(async ([path, entry]) => {
        if (entry.dir || !path.endsWith('.theory')) return;
        const filename = path.split('/').pop();
        loaded[filename] = await entry.async('string');
        if (bundleKey(filename) === zipName) inferredMain = filename;
      })
    );
    if (!Object.keys(loaded).length) { alert('No .theory files found in zip.'); return; }
    const main = inferredMain || Object.keys(loaded).sort()[0];
    setFiles(loaded);
    setMainFile(main);
    setActiveFile(main);
    setProjectName(zipName);
    setIsDirty(false);
    setOutput('');
    setOutputIsError(false);
  }

  const uploadRef = useRef(null);

  // ── Render ────────────────────────────────────────────────────────────────

  return (
    <div className="app-shell">

      {/* ── Header ── */}
      <header className="app-header">
        <div className="header-wordmark">
          <span className="wordmark-eidos">Eidos</span>
          <span className="wordmark-arrow">→</span>
          <span className="wordmark-lean">Lean</span>
        </div>

        <div className="header-actions">
          <button
            className="hdr-btn"
            onClick={() => setShowProjectPanel(p => !p)}
            title="Open a sample project"
          >
            open project
          </button>

          <label className="hdr-btn" title="Upload a .zip project">
            upload .zip
            <input
              ref={uploadRef}
              type="file"
              accept=".zip"
              style={{ display: 'none' }}
              onChange={uploadZip}
            />
          </label>

          <button
            className="hdr-btn"
            onClick={downloadZip}
            title="Download project as .zip"
          >
            download .zip{isDirty ? ' *' : ''}
          </button>
        </div>

        {wasmError && <span className="wasm-error-badge" title={wasmError}>wasm error</span>}
      </header>

      {/* ── Project panel (dropdown) ── */}
      {showProjectPanel && (
        <div className="project-panel">
          <div className="project-panel-header">
            <span>sample projects</span>
            <button className="icon-btn" onClick={() => setShowProjectPanel(false)}>✕</button>
          </div>
          <div className="project-list">
            {PROJECT_NAMES.map(name => (
              <button
                key={name}
                className={`project-item ${name === projectName ? 'project-item--active' : ''}`}
                onClick={() => {
                  if (isDirty && !confirm(`Open "${name}"? Unsaved changes will be lost.`)) return;
                  loadProject(name);
                }}
              >
                <span className="project-name">{name}</span>
                <span className="project-file-count">
                  {PROJECT_CATALOGUE[name].length} file{PROJECT_CATALOGUE[name].length !== 1 ? 's' : ''}
                </span>
              </button>
            ))}
          </div>
        </div>
      )}

      {/* ── Body ── */}
      <div className="app-body">

        {/* ── Sidebar ── */}
        <aside className="sidebar">
          <div className="sidebar-section-label">files</div>

          <div className="file-list">
            {fileNames.map(name => {
              const tag = inferTypeTag(name);
              const isActive = name === activeFile;
              const isMain = name === mainFile;
              return (
                <div
                  key={name}
                  className={`file-item ${isActive ? 'file-item--active' : ''}`}
                  onClick={() => setActiveFile(name)}
                >
                  <div className="file-item-name" title={name}>
                    {isMain && <span className="main-dot" title="main theory" />}
                    <span>{name}</span>
                    {tag && <TypeBadge tag={tag} />}
                  </div>
                  <div className="file-item-actions">
                    {!isMain && (
                      <button
                        className="file-action-btn"
                        title="Set as main theory"
                        onClick={e => { e.stopPropagation(); setAsMain(name); }}
                      >
                        ★
                      </button>
                    )}
                    {!isMain && (
                      <button
                        className="file-action-btn file-action-btn--danger"
                        title="Delete file"
                        onClick={e => { e.stopPropagation(); deleteFile(name); }}
                      >
                        ✕
                      </button>
                    )}
                  </div>
                </div>
              );
            })}
          </div>

          {/* New file input */}
          <div className="new-file-row">
            <input
              ref={newFileInputRef}
              className="new-file-input"
              placeholder="new-file.eq.theory"
              value={newFileName}
              onChange={e => setNewFileName(e.target.value)}
              onKeyDown={e => { if (e.key === 'Enter') commitNewFile(); }}
            />
            <button className="icon-btn" onClick={commitNewFile} title="Add file">＋</button>
          </div>

          <div className="sidebar-section-label" style={{ marginTop: 'auto', paddingTop: '12px' }}>
            main theory
          </div>
          <div className="main-theory-name">{mainFile || '—'}</div>
        </aside>

        {/* ── Editor ── */}
        <div className="editor-panel">
          <div className="editor-file-label">
            {activeFile}
            {activeFile === mainFile && <span className="main-indicator"> · main</span>}
          </div>
          <div className="editor-wrap">
            <Editor
              height="100%"
              defaultLanguage="plaintext"
              theme="vs-dark"
              path={activeFile}
              value={files[activeFile] ?? ''}
              onChange={val => updateContent(activeFile, val ?? '')}
              options={{
                fontSize: 13,
                fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                fontLigatures: true,
                lineHeight: 20,
                minimap: { enabled: false },
                scrollBeyondLastLine: false,
                renderLineHighlight: 'gutter',
                padding: { top: 12, bottom: 12 },
              }}
            />
          </div>
        </div>

        {/* ── Output panel ── */}
        <div className="output-panel">
          <div className="output-header">
            <span className="output-label">output</span>
            <button
              className={`compile-btn ${compiling ? 'compile-btn--busy' : ''}`}
              onClick={compile}
              disabled={!eidos || compiling || loadingWasm}
            >
              {loadingWasm
                ? <><span className="spinner" /> loading…</>
                : compiling
                  ? <><span className="spinner" /> compiling…</>
                  : 'compile'}
            </button>
          </div>

          <pre className={`output-pre ${outputIsError ? 'output-pre--error' : output ? 'output-pre--ok' : ''}`}>
            {output || <span className="output-placeholder">// output will appear here</span>}
          </pre>
        </div>
      </div>
    </div>
  );
}

// ── Bundle builder ───────────────────────────────────────────────────────────

const THEORY_TYPE_META_PREFIX = '__theory_type__.';

function buildBundle(files, mainFile) {
  if (!files[mainFile]) throw new Error(`Main file "${mainFile}" not found.`);
  const bundle = {};
  for (const [filename, src] of Object.entries(files)) {
    const key = filename === mainFile ? '__main__' : bundleKey(filename);
    bundle[key] = src;
    if (filename !== mainFile) {
      const tag = inferTypeTag(filename);
      if (tag) bundle[THEORY_TYPE_META_PREFIX + key] = tag;
    }
  }
  return bundle;
}
