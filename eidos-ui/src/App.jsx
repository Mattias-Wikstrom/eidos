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
  const [theoryText, setTheoryText] = useState('');
  const [output, setOutput] = useState('');
  const [loading, setLoading] = useState(false);

  const selectedPath = useMemo(
    () => theoryEntries.find((entry) => entry.name === selectedTheory)?.path,
    [selectedTheory]
  );

  useEffect(() => {
    if (!selectedPath) return;

    let cancelled = false;

    theoryModules[selectedPath]().then((text) => {
      if (!cancelled) {
        setTheoryText(text);
      }
    });

    return () => {
      cancelled = true;
    };
  }, [selectedPath]);

  const compile = async () => {
    if (!eidos) return;

    setLoading(true);
    try {
      const result = await eidos.compileSingle(theoryText);
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
        Theory
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

      <Editor
        height="420px"
        defaultLanguage="plaintext"
        value={theoryText}
        onChange={(value) => setTheoryText(value ?? '')}
      />

      <button onClick={compile} disabled={!eidos || loading} style={{ marginTop: 12 }}>
        {loading ? 'Compiling...' : 'Compile'}
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
