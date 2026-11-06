import DevWidgets.SnapshotExplorer.Model

namespace DevWidgets.SnapshotExplorer

/-- Bounded presentation helpers and one disposable file-observation lifecycle. -/
def frontendJs : String :=
  "const numericSettings = " ++ (Lean.Json.mkObj [
    ("intervalMs", Lean.toJson intervalSetting), ("maxCommands", Lean.toJson commandsSetting),
    ("maxNodes", Lean.toJson nodesSetting), ("maxDepth", Lean.toJson depthSetting)
  ]).compress ++ ";\n" ++ r#"
function snapshotSettings(props) {
  const settings = { autoRefresh: props?.autoRefresh !== false };
  for (const [key, { value, min, max }] of Object.entries(numericSettings))
    settings[key] = boundedNat(props?.[key], value, min, max);
  return settings;
}

// Pure conversion of bounded preorder rows; keys do not shift when a pending
// node gains descendants. No server objects or mutable UI state live in this tree.
function snapshotForest(nodes) {
  const forest = [], stack = [];
  for (const node of nodes) {
    while (stack.length && stack.at(-1).node.depth >= node.depth) stack.pop();
    const parent = stack.at(-1);
    const siblings = parent ? parent.children : forest;
    const item = { node, children: [], path: `${parent?.path ?? 'root'}.${siblings.length}` };
    siblings.push(item); stack.push(item);
  }
  return forest;
}

function useSnapshotObservation(rpc, uri, settings, frozen) {
  const [incarnation, setIncarnation] = React.useState(0);
  const file = React.useMemo(() => ({ minimumVersion: 0 }), [uri, incarnation]);
  const owner = React.useRef(null);
  const [snapshot, setSnapshot] = React.useState(null);
  const [selection, setSelection] = React.useState(null);
  const [revision, setRevision] = React.useState(0);
  const [error, setError] = React.useState(null);
  const [loading, setLoading] = React.useState(false);
  const params = {
    maxCommands: settings.maxCommands, maxNodes: settings.maxNodes, maxDepth: settings.maxDepth,
    ...(selection?.file === file ? selection.target : {})
  };
  // Transport changes invalidate replies, not file selection. The worker validates
  // generation/version before inspecting an index, including after reconnection.
  const input = React.useMemo(() => ({ rpc, params, frozen }),
    [file, rpc, JSON.stringify(params), frozen, revision]);
  const currentInput = React.useRef(input);
  currentInput.current = input;

  useClientNotificationEffect('textDocument/didChange', change => {
    if (change.textDocument.uri !== uri) return;
    file.minimumVersion = Math.max(file.minimumVersion, change.textDocument.version);
    setRevision(n => n + 1);
    setSelection(null);
  }, [uri, file]);
  useClientNotificationEffect('textDocument/didOpen', change => {
    if (change.textDocument.uri === uri) { setIncarnation(n => n + 1); setSelection(null); }
  }, [uri]);
  useClientNotificationEffect('textDocument/didClose', change => {
    if (change.textDocument.uri === uri) { setIncarnation(n => n + 1); setSelection(null); }
  }, [uri]);

  React.useEffect(() => {
    let disposed = false, inFlight = false, queued = false;
    setError(null);
    setLoading(false);
    async function load() {
      if (disposed || currentInput.current.frozen) return;
      if (inFlight) { queued = true; return; }
      inFlight = true;
      queued = false;
      const requestInput = currentInput.current;
      const isCurrent = () => !disposed && currentInput.current === requestInput;
      setLoading(true);
      try {
        const value = await requestInput.rpc.call('DevWidgets.SnapshotExplorer.readSnapshots', requestInput.params);
        if (isCurrent() && value.version >= file.minimumVersion && (!uri || value.uri === uri)) {
          setSnapshot({ file, value });
          setError(null);
          if (requestInput.params.command !== undefined &&
              (requestInput.params.generation !== value.generation || requestInput.params.version !== value.version))
            setSelection(null);
        }
      } catch (err) {
        if (isCurrent()) setError(String(err?.message ?? err));
      } finally {
        inFlight = false;
        if (!disposed) {
          setLoading(false);
          if (queued) void load();
        }
      }
    }
    const controller = { load, fail: err => { if (!disposed) setError(String(err)); } };
    owner.current = controller;
    return () => {
      disposed = true;
      if (owner.current === controller) owner.current = null;
    };
  }, [file]);
  React.useEffect(() => { void owner.current?.load(); }, [input]);
  React.useEffect(() => {
    if (!settings.autoRefresh || frozen) return;
    const timer = setInterval(() => {
      if (typeof document === 'undefined' || !document.hidden) void owner.current?.load();
    }, settings.intervalMs);
    return () => clearInterval(timer);
  }, [file, settings.autoRefresh, settings.intervalMs, frozen]);

  return {
    live: snapshot?.file === file && snapshot.value.version >= file.minimumVersion ? snapshot.value : null,
    error, loading,
    refresh: () => { void owner.current?.load(); },
    select: (view, command) => setSelection({ file, target: { generation: view.generation, version: view.version, command } }),
    reset: () => { setSelection(null); setRevision(n => n + 1); },
    // Capture the current lifetime, so a late navigation error cannot affect a new file.
    reportError: owner.current?.fail ?? (() => {})
  };
}
"#

end DevWidgets.SnapshotExplorer
