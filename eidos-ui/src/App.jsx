import { useEffect, useMemo, useState } from 'react';
import Editor from '@monaco-editor/react';
import { useEidos } from './useEidos';

const theoryModules = import.meta.glob('./demo-theories/*.theory', {
  query: '?raw',
  import: 'default',
});

const theoryEntries = Object.keys(theoryModules)
  .map((path) => ({
    path,
    name: path.split('/').pop(),
  }))
  .sort((a, b) => a.name.localeCompare(b.name));

export default function App() {
  const eidos = useEidos();
  const [selectedTheory, setSelectedTheory] = useState(theoryEntries[0]?.name ?? '');
  const [files, setFiles] = useState({ '__main__.theory': '' });
  const [activeFile, setActiveFile] = useState('__main__.theory');
  const [entryFile, setEntryFile] = useState('__main__.theory');
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

    theoryModules[selectedPath]().then((text) => {
      if (!cancelled) {
        setFiles({ '__main__.theory': text });
        setActiveFile('__main__.theory');
        setEntryFile('__main__.theory');
        setOutput('');
      }
    });

    return () => {
      cancelled = true;
    };
  }, [selectedPath]);

  const updateFileContent = (name, text) => {
    setFiles((prev) => ({ ...prev, [name]: text }));
  };

  const addFile = () => {
    const name = window.prompt('New file name (for example: group.eq.theory)');
    if (!name) return;
    if (files[name]) {
      setOutput(`Error: file "${name}" already exists.`);
      return;
    }
    setFiles((prev) => ({ ...prev, [name]: '' }));
    setActiveFile(name);
  };

  const removeActiveFile = () => {
    if (activeFile === '__main__.theory') {
      setOutput('Error: __main__.theory cannot be deleted.');
      return;
    }
    const nextFiles = { ...files };
    delete nextFiles[activeFile];
    setFiles(nextFiles);
    if (entryFile === activeFile) setEntryFile('__main__.theory');
    setActiveFile('__main__.theory');
  };

  const compile = async () => {
    if (!eidos) return;

    setLoading(true);
    try {
      const bundle = Object.fromEntries(
        Object.entries(files).map(([name, src]) => [name === entryFile ? '__main__' : name, src])
      );
      const result = await eidos.compileBundle(bundle);
      setOutput(result);
    } catch (err) {
      setOutput('Error: ' + err.message);
    }
    setLoading(false);
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
        <button onClick={addFile}>Add file</button>
        <button onClick={removeActiveFile} disabled={activeFile === '__main__.theory'}>
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

      <button onClick={compile} disabled={!eidos || loading} style={{ marginTop: 12 }}>
        {loading ? 'Compiling...' : 'Compile bundle'}
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
