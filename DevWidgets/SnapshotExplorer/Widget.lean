import DevWidgets.SnapshotExplorer.Rpc
import DevWidgets.Lib.Panel
import DevWidgets.SnapshotExplorer.Frontend

namespace DevWidgets.SnapshotExplorer

@[widget_module]
def snapshotWidget : Lean.Widget.Module where
  javascript := DevWidgets.Lib.Panel.javascript ++ frontendJs ++ r#"
import * as React from 'react';
import { useRpcSession, EditorContext, useClientNotificationEffect } from '@leanprover/infoview';
const e = React.createElement;

export default function SnapshotExplorer(props) {
  const rpc = useRpcSession();
  const editor = React.useContext(EditorContext);
  const uri = props?.pos?.uri;
  const [settings, setSettings, resetSettings] = usePanelSettings(snapshotSettings(props));
  const [frozen, setFrozen] = React.useState(null);
  const [pendingOnly, setPendingOnly] = React.useState(false);
  const observer = useSnapshotObservation(rpc, uri, settings, !!frozen);
  const { live, error, loading } = observer;
  const view = frozen ?? live;
  const waiting = row => !row.mainReady || !row.infoReady || !row.reportingReady;
  const rows = (view?.commands ?? []).filter(row => !pendingOnly || waiting(row) || row.fatal);
  const button = (key, label, onClick, disabled = false) => e('button', { key, type: 'button', onClick, disabled }, label);
  const location = range => range ? `line ${range.start.line + 1}` : 'no source range';
  const jump = range => editor.revealLocation({ uri: view.uri, range }).catch(observer.reportError);
  const forest = snapshotForest(view?.nodes ?? []);
  function renderNode({ node, children, path }) {
    const facts = node.observation?.inspected?.facts;
    const unsupported = node.observation?.unsupported?.typeName;
    const status = facts ? 'available' : unsupported ? 'not inspected' :
      node.observation === 'noResult' ? 'no result' : 'pending';
    return e('details', {
      key: `${view.generation}:${view.version}:${view.selected}:${path}`, open: node.depth === 0 && node.kind === 'elaboration',
      style: { marginLeft: node.depth ? '0.6em' : 0, marginBottom: '0.35em' }
    }, [
      e('summary', {}, `${node.label} — ${status}${facts?.fatal ? ' · fatal' : ''}`),
      e('details', {}, [e('summary', {}, 'Snapshot metadata'),
        e('p', {}, facts?.description || (unsupported ? `Unsupported snapshot type: ${unsupported}` : status === 'no result' ? 'This task returned no snapshot.' : 'Result is not available yet.')),
        e('p', {}, `${location(node.range)} · reporting range: ${node.reporting}`),
        facts && e('p', {}, `${facts.messages} local messages · InfoTree ${facts.hasInfoTree ? 'available' : 'absent'}`)
      ]),
      unsupported && e('p', {}, 'Metadata and children were not inspected; their contents are unknown.'),
      ...children.map(renderNode)
    ]);
  }
  const controls = e('div', { style: { display: 'flex', gap: '0.5em', flexWrap: 'wrap', alignItems: 'center' } }, [
    button('freeze', frozen ? 'Resume live' : 'Freeze capture', () => setFrozen(frozen ? null : live), !view),
    button('refresh', 'Refresh', observer.refresh, !!frozen || loading),
    button('reset', 'Reset panel', () => {
      resetSettings(); setFrozen(null); observer.reset(); setPendingOnly(false);
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
    e('h3', { key: 'title' }, 'Snapshot Explorer'),
    e('p', {}, 'See where elaboration has reached and which results are still pending.'), controls,
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
            onClick: () => observer.select(view, row.index)
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
      ...[['intervalMs', 'Refresh interval (ms)'], ['maxCommands', 'Command limit'],
        ['maxNodes', 'Snapshot node limit'], ['maxDepth', 'Snapshot depth limit']].map(([key, label]) => {
          const { min, max } = numericSettings[key];
          return e('label', { key, style: { display: 'block', marginTop: '0.5em' } }, [label + ' ', e('input', {
            type: 'number', min, max, value: settings[key], style: { width: '6em' },
            onChange: event => setSettings(s => ({ ...s, [key]: boundedNat(Number(event.target.value), s[key], min, max) }))
          })]);
        }),
      e('p', {}, 'To watch blocked work, pin the host InfoView at an earlier completed command. Freeze capture above stops observation instead.'),
      e('p', {}, 'Snapshots describe available elaboration results, not exact execution timings or a complete dependency graph.')
    ])
  ]);
}
"#

end DevWidgets.SnapshotExplorer
