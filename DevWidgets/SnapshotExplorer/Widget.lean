import DevWidgets.SnapshotExplorer.Rpc
import DevWidgets.Lib.Panel

namespace DevWidgets.SnapshotExplorer

@[widget_module]
def snapshotWidget : Lean.Widget.Module where
  javascript := DevWidgets.Lib.Panel.javascript ++ r#"
import * as React from 'react';
import { useRpcSession, EditorContext, useClientNotificationEffect } from '@leanprover/infoview';
const e = React.createElement;
const method = 'DevWidgets.SnapshotExplorer.readSnapshots';

export default function SnapshotExplorer(props) {
  const rpc = useRpcSession();
  const editor = React.useContext(EditorContext);
  const uri = props?.pos?.uri;
  const [settings, setSettings, resetSettings] = usePanelSettings({
    autoRefresh: props?.autoRefresh !== false,
    intervalMs: boundedNat(props?.intervalMs, 500, 100, 60000),
    maxCommands: boundedNat(props?.maxCommands, 200, 1, 2000),
    maxNodes: boundedNat(props?.maxNodes, 128, 1, 2048),
    maxDepth: boundedNat(props?.maxDepth, 12, 0, 32)
  });
  const session = React.useMemo(() => ({ minimumVersion: 0 }), [rpc, uri]);
  const active = React.useRef(null);
  const trigger = React.useRef(null);
  const [snapshot, setSnapshot] = React.useState(null);
  const [frozen, setFrozen] = React.useState(null);
  const [selection, setSelection] = React.useState(null);
  const [pendingOnly, setPendingOnly] = React.useState(false);
  const [epoch, setEpoch] = React.useState(0);
  const [error, setError] = React.useState(null);
  const [loading, setLoading] = React.useState(false);
  const params = {
    maxCommands: settings.maxCommands, maxNodes: settings.maxNodes, maxDepth: settings.maxDepth,
    ...(selection?.session === session ? { version: selection.version, command: selection.command } : {})
  };
  const input = React.useMemo(() => ({ params, frozen: !!frozen }),
    [session, JSON.stringify(params), !!frozen, epoch]);
  const currentInput = React.useRef(input);
  currentInput.current = input;

  useClientNotificationEffect('textDocument/didChange', (change) => {
    if (change.textDocument.uri !== uri) return;
    session.minimumVersion = Math.max(session.minimumVersion, change.textDocument.version);
    setEpoch(value => value + 1);
    setSelection(null);
  }, [uri, session]);

  // One request per session, including manual refresh and selection changes. Queue the
  // newest intent while a request runs; stale responses cannot update the displayed capture.
  React.useEffect(() => {
    active.current = session;
    let inFlight = false, queued = false;
    setError(null);
    setLoading(false);
    async function load() {
      if (active.current !== session || currentInput.current.frozen) return;
      if (inFlight) { queued = true; return; }
      inFlight = true;
      queued = false;
      const requestInput = currentInput.current;
      setLoading(true);
      try {
        const value = await rpc.call(method, requestInput.params);
        if (active.current === session && currentInput.current === requestInput &&
            value.version >= session.minimumVersion && (!uri || value.uri === uri)) {
          setSnapshot({ session, value });
          setError(null);
          if (requestInput.params.version !== undefined && requestInput.params.version !== value.version)
            setSelection(null);
        }
      } catch (err) {
        if (active.current === session && currentInput.current === requestInput)
          setError(String(err?.message ?? err));
      } finally {
        inFlight = false;
        if (active.current === session) {
          setLoading(false);
          if (queued) void load();
        }
      }
    }
    trigger.current = load;
    return () => { active.current = null; trigger.current = null; };
  }, [session]);
  React.useEffect(() => { void trigger.current?.(); }, [input]);
  React.useEffect(() => {
    if (!settings.autoRefresh || frozen) return;
    const timer = setInterval(() => {
      if (typeof document === 'undefined' || !document.hidden) void trigger.current?.();
    }, settings.intervalMs);
    return () => clearInterval(timer);
  }, [session, settings.autoRefresh, settings.intervalMs, !!frozen]);

  const live = snapshot?.session === session && snapshot.value.version >= session.minimumVersion
    ? snapshot.value : null;
  const view = frozen ?? live;
  const waiting = row => !row.mainReady || !row.infoReady || !row.reportingReady;
  const rows = (view?.commands ?? []).filter(row => !pendingOnly || waiting(row) || row.fatal);
  const button = (key, label, onClick, disabled = false) => e('button', { key, type: 'button', onClick, disabled }, label);
  const location = range => range ? `line ${range.start.line + 1}` : 'no source range';
  const jump = range => editor.revealLocation({ uri: view.uri, range }).catch(err => setError(String(err)));
  // Reconstruct presentation nesting from bounded preorder rows. Structural keys keep
  // disclosures stable when a pending node gains descendants in the same file version.
  const forest = [], stack = [];
  for (const node of view?.nodes ?? []) {
    while (stack.length && stack.at(-1).node.depth >= node.depth) stack.pop();
    const parent = stack.at(-1);
    const siblings = parent ? parent.children : forest;
    const item = { node, children: [], path: `${parent?.path ?? 'root'}.${siblings.length}` };
    siblings.push(item); stack.push(item);
  }
  function renderNode({ node, children, path }) {
    return e('details', {
      key: `${view.version}:${view.selected}:${path}`, open: node.depth === 0 && node.label === 'Elaboration snapshots',
      style: { marginLeft: node.depth ? '0.6em' : 0, marginBottom: '0.35em' }
    }, [
      e('summary', {}, `${node.label} — ${node.ready ? 'available' : 'pending'}${node.fatal ? ' · fatal' : ''}`),
      e('details', {}, [e('summary', {}, 'Snapshot metadata'),
        e('p', {}, node.description || 'Result is not available yet.'),
        e('p', {}, `${location(node.range)} · reporting range: ${node.reporting}`),
        node.ready && e('p', {}, `${node.messages} local messages · InfoTree ${node.hasInfoTree ? 'available' : 'absent'}`)
      ]),
      node.unsupported && e('p', {}, 'This elaborator’s snapshot type is not expanded by this version of the widget.'),
      ...children.map(renderNode)
    ]);
  }
  const controls = e('div', { style: { display: 'flex', gap: '0.5em', flexWrap: 'wrap', alignItems: 'center' } }, [
    button('freeze', frozen ? 'Resume live' : 'Freeze capture', () => setFrozen(frozen ? null : live), !view),
    button('refresh', 'Refresh', () => { void trigger.current?.(); }, !!frozen || loading),
    button('reset', 'Reset panel', () => {
      resetSettings(); setFrozen(null); setSelection(null); setPendingOnly(false); setEpoch(value => value + 1);
    }),
    e('label', { key: 'auto' }, [e('input', {
      type: 'checkbox', checked: settings.autoRefresh, disabled: !!frozen,
      onChange: event => setSettings(s => ({ ...s, autoRefresh: event.target.checked }))
    }), ' Auto-refresh']),
    e('label', { key: 'filter' }, [e('input', {
      type: 'checkbox', checked: pendingOnly, onChange: event => setPendingOnly(event.target.checked)
    }), ' Hide ready rows'])
  ]);
  const frontierText = {
    pending: 'Further commands may still be discovered.',
    complete: 'Command discovery finished; individual tasks may still be pending.',
    limited: 'Command limit reached. Increase the limit to see later commands.',
    fatal: 'A fatal error stopped command discovery.'
  };
  return e('section', { 'aria-label': 'Snapshot Explorer', style: { overflowWrap: 'anywhere' } }, [
    e('h3', { key: 'title' }, 'Snapshot Explorer'), controls,
    error && e('p', { key: 'error', role: 'alert' }, error),
    !view && e('p', { key: 'loading', role: 'status' }, 'Waiting for a snapshot capture…'),
    view && e('div', { key: 'capture' }, [
      e('p', {}, `${view.uri.split('/').pop()} · version ${view.version} · ${frozen ? 'Frozen capture' : settings.autoRefresh ? 'Live' : 'Manual'}`),
      frozen && e('p', {}, 'Source navigation and command selection resume with live observation.'),
      e('p', {}, `${view.commands.length} commands captured. ${frontierText[view.frontier] ?? ''}`),
      e('p', {}, 'Readiness is for each named task; available snapshots may still have pending children.'),
      e('ol', { style: { paddingLeft: '1.5em', maxHeight: '20rem', overflowY: 'auto' } }, rows.map(row =>
        e('li', { key: row.index, style: { marginBottom: '0.5em' } }, [
          e('button', {
            type: 'button', disabled: !!frozen, 'aria-pressed': view.selected === row.index,
            style: { textAlign: 'left', whiteSpace: 'normal', maxWidth: '100%' },
            onClick: () => setSelection({ session, version: view.version, command: row.index })
          }, `${row.label} · ${location(row.range)}`),
          e('div', {}, row.fatal ? 'Fatal error' :
            `Main: ${row.mainReady ? 'returned' : 'pending'} · InfoTree: ${row.infoReady ? 'ready' : 'pending'} · Reporting root: ${row.reportingReady ? 'ready' : 'pending'}`)
        ]))),
      rows.length === 0 && e('p', {}, 'No commands match this filter.'),
      view.selected === undefined ? e('p', {}, 'Select a command to inspect its snapshots.') :
        e('div', { 'aria-label': 'Selected command snapshots' }, [
          e('h4', {}, `Snapshots for command ${view.selected + 1}`),
          view.commands.find(row => row.index === view.selected)?.range &&
            button('source', 'Go to source', () => jump(view.commands.find(row => row.index === view.selected).range), !!frozen),
          view.truncated && e('p', { role: 'status' }, 'Partial capture: node or depth limit reached.'),
          ...forest.map(renderNode)
        ])
    ]),
    e('details', { key: 'settings' }, [e('summary', {}, 'Capture settings'),
      ...[['intervalMs', 'Refresh interval (ms)', 100, 60000], ['maxCommands', 'Command limit', 1, 2000],
        ['maxNodes', 'Snapshot node limit', 1, 2048], ['maxDepth', 'Snapshot depth limit', 0, 32]].map(([key, label, min, max]) =>
        e('label', { key, style: { display: 'block', marginTop: '0.5em' } }, [label + ' ', e('input', {
          type: 'number', min, max, value: settings[key], style: { width: '6em' },
          onChange: event => setSettings(s => ({ ...s, [key]: boundedNat(Number(event.target.value), s[key], min, max) }))
        })])),
      e('p', {}, 'Snapshots describe available elaboration results, not exact execution timings or a complete dependency graph.')
    ])
  ]);
}
"#

end DevWidgets.SnapshotExplorer
