// src/App.jsx
import { useState } from 'react';
import { useEidos } from './useEidos';
import Editor from '@monaco-editor/react';

export default function App() {
  const eidos = useEidos();

  const [input, setInput] = useState(
    '{ signature { P : ℙ; } }'
  );
  const [output, setOutput] = useState('');
  const [loading, setLoading] = useState(false);

  const compile = async () => {
    if (!eidos) return;

    setLoading(true);
    try {
      const result = await eidos.compileSingle(input);
      setOutput(result);
    } catch (err) {
      setOutput('Error: ' + err.message);
    }
    setLoading(false);
  };

  return (
    <div style={{ padding: 20, fontFamily: 'sans-serif' }}>
      <h1>Eidos → Lean</h1>


      <Editor
  height="300px"
  defaultLanguage="plaintext"
  value={input}
  onChange={setInput}
/>

      <button onClick={compile} disabled={!eidos || loading}>
        {loading ? 'Compiling...' : 'Compile'}
      </button>

      <pre style={{
        marginTop: 20,
        background: '#111',
        color: '#0f0',
        padding: 10
      }}>
        {output}
      </pre>
    </div>
  );
}
