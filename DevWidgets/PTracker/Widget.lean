/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import DevWidgets.Lib.Panel
import DevWidgets.PTracker.ProgressRef

open Lean Server

namespace DevWidgets.PTracker

/-- Initial polling and retention settings for the progress panel. Durations are milliseconds. -/
structure Config where
  autoRefresh : Bool := true
  intervalMs : Nat := 250
  autoRemove : Bool := true
  retainDoneMs : Nat := 20000
  deriving ToJson, FromJson

/-- Less frequent polling and a longer window to inspect completed tasks. -/
def Config.quiet : Config := { intervalMs := 1000, retainDoneMs := 60000 }

/-- Refresh and remove entries only on request. -/
def Config.manual : Config := { autoRefresh := false, autoRemove := false }

structure ReadProgressViewParams where
  deriving ToJson, FromJson

structure ProgressView where
  nowNs : Nat
  entries : Array TrackedProgressRef
  deriving ToJson, FromJson

@[server_rpc_method]
meta def readProgressViewRpc (_ : ReadProgressViewParams) : RequestM (RequestTask ProgressView) :=
  RequestM.asTask do
    let nowNs ← IO.monoNanosNow
    let entries ← listProgressRefs
    pure { nowNs := nowNs, entries := entries }

structure DeleteProgressRefParams where
  id : Nat
  deriving ToJson, FromJson

@[server_rpc_method]
meta def deleteProgressRefRpc (params : DeleteProgressRefParams) : RequestM (RequestTask Bool) :=
  RequestM.asTask do
    deleteProgressRef params.id
    pure true

@[widget_module]
def progressWidget : Lean.Widget.Module where
  javascript := DevWidgets.Lib.Panel.javascript ++ "
import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';

const e = React.createElement;

export default function ProgressWidget(props) {
  const rpc = useRpcSession();
  const [settings, setSettings, resetSettings] = usePanelSettings({
    autoRefresh: props?.autoRefresh !== false,
    intervalMs: boundedNat(props?.intervalMs, 250, 100, 60000),
    autoRemove: props?.autoRemove !== false,
    retainDoneMs: boundedNat(props?.retainDoneMs, 20000, 1000, 3600000)
  });
  const autoEnabled = settings.autoRefresh;
  const periodMs = settings.intervalMs;
  const RETAIN_DONE_MS = settings.retainDoneMs;
  const setAutoEnabled = (value) => setSettings((prev) => ({ ...prev, autoRefresh: value }));
  const setPeriodMs = (value) => setSettings((prev) => ({ ...prev, intervalMs: value }));
  // Requests and row IDs belong to one RPC session. A restarted worker may reuse IDs.
  const session = React.useMemo(() => ({ inFlight: false, pendingDeleteIds: new Set() }), [rpc]);
  const activeSession = React.useRef(null);
  const [snapshot, setSnapshot] = React.useState(null);
  const entries = snapshot?.session === session ? snapshot.entries : [];
  const [manualLoading, setManualLoading] = React.useState(false);
  const [error, setError] = React.useState(null);
  const [, setClockTick] = React.useState(0);

  React.useEffect(() => {
    activeSession.current = session;
    setSnapshot(null);
    setManualLoading(false);
    setError(null);
    return () => { activeSession.current = null; };
  }, [session]);

  React.useEffect(() => {
    const id = setInterval(() => {
      setClockTick((tick) => tick + 1);
    }, 250);
    return () => clearInterval(id);
  }, []);

  const estimatedNowNs = snapshot?.session === session
    ? snapshot.nowNs + Math.max(0, Date.now() - snapshot.atMs) * 1_000_000
    : 0;

  function formatMonoSeconds(ns) {
    if (!Number.isFinite(ns)) return 'n/a';
    return `${(ns / 1_000_000_000).toFixed(3)} s`;
  }

  function formatDurationMs(totalMs) {
    if (!Number.isFinite(totalMs)) return 'n/a';
    const ms = Math.max(0, Math.floor(totalMs));
    if (ms < 1_500) return 'just now';
    const sec = Math.round(ms / 1000);
    if (sec < 60) return `${sec}s`;
    const min = Math.floor(sec / 60);
    const s = sec % 60;
    if (min < 60) return s === 0 ? `${min}m` : `${min}m ${s}s`;
    const hr = Math.floor(min / 60);
    const m = min % 60;
    if (hr < 24) return m === 0 ? `${hr}h` : `${hr}h ${m}m`;
    const day = Math.floor(hr / 24);
    const h = hr % 24;
    return h === 0 ? `${day}d` : `${day}d ${h}h`;
  }

  function formatElapsedSince(ns) {
    const n = Number(ns);
    if (!Number.isFinite(n)) return 'n/a';
    const elapsedMs = Math.max(0, (estimatedNowNs - n) / 1_000_000);
    return `${formatDurationMs(elapsedMs)} ago`;
  }

  function statusIcon(status) {
    if (status === 'done') return '✓';
    if (status === 'cancelled') return '⨯';
    return '●';
  }

  function statusLabel(status) {
    if (status === 'done') return 'Done';
    if (status === 'cancelled') return 'Cancelled';
    return 'Running';
  }

  function rowBackground(status) {
    if (status === 'done') return 'rgba(40, 167, 69, 0.10)';
    if (status === 'cancelled') return 'rgba(220, 53, 69, 0.11)';
    return 'transparent';
  }

  function isClosedStatus(status) {
    return status === 'done' || status === 'cancelled';
  }

  function getRemainingMs(entry) {
    if (!settings.autoRemove) return null;
    if (!isClosedStatus(String(entry.status ?? ''))) return null;
    if (entry.closedAtNs === null || entry.closedAtNs === undefined) return null;
    const closedAtNs = Number(entry.closedAtNs);
    if (!Number.isFinite(closedAtNs)) return null;
    const elapsedMs = Math.max(0, (estimatedNowNs - closedAtNs) / 1_000_000);
    return Math.max(0, RETAIN_DONE_MS - elapsedMs);
  }

  function renderExpiry(entry) {
    const remainingMs = getRemainingMs(entry);
    if (remainingMs === null) return null;
    const ratio = Math.max(0, Math.min(1, remainingMs / RETAIN_DONE_MS));
    const sweepDeg = `${(ratio * 360).toFixed(1)}deg`;
    return e('div', { key: 'expiry', style: { display: 'inline-flex', alignItems: 'center', gap: '0.35rem' } }, [
      e('span', {
        key: 'ring',
        title: `${Math.ceil(remainingMs / 1000)}s until auto-remove`,
        style: {
          width: '1rem',
          height: '1rem',
          borderRadius: '50%',
          border: '1px solid rgba(127,127,127,0.35)',
          display: 'inline-grid',
          placeItems: 'center',
          background: `conic-gradient(var(--vscode-progressBar-background, #0e70c0) ${sweepDeg}, rgba(127,127,127,0.28) ${sweepDeg})`
        }
      }, e('span', {
        style: {
          width: '0.45rem',
          height: '0.45rem',
          borderRadius: '50%',
          background: 'var(--vscode-editor-background)'
        }
      })),
      e('span', { key: 'txt', style: { fontFamily: 'monospace', fontSize: '0.75rem', opacity: 0.85 } }, `${Math.ceil(remainingMs / 1000)}s`)
    ]);
  }

  function renderValue(entry) {
    const description = String(entry.description ?? '');
    const label = String(entry.label ?? '');
    const doneRaw = Number(entry.stepsDone);
    const done = Number.isFinite(doneRaw) ? Math.max(0, Math.floor(doneRaw)) : 0;
    const totalRaw = Number(entry.totalSteps);
    const hasTotal = Number.isFinite(totalRaw) && totalRaw > 0;
    const total = hasTotal ? Math.floor(totalRaw) : 0;
    const doneClamped = hasTotal ? Math.min(done, total) : done;
    const ratio = hasTotal ? Math.max(0, Math.min(1, doneClamped / total)) : null;
    const stepText = hasTotal
      ? `${doneClamped} / ${total}`
      : `${done} step${done === 1 ? '' : 's'}`;
    const nodes = [];
    if (description.length > 0) {
      nodes.push(e('div', { key: 'desc', style: { fontWeight: 600 } }, description));
    }
    if (label.length > 0) {
      nodes.push(e('div', { key: 'label', style: { opacity: 0.9 } }, label));
    }
    if (hasTotal) {
      nodes.push(e('div', { key: 'bar-wrap', style: { display: 'inline-flex', alignItems: 'center', gap: '0.45rem' } }, [
        e('span', {
          key: 'bar-outer',
          style: {
            width: '8rem',
            height: '0.38rem',
            borderRadius: '999px',
            background: 'rgba(127,127,127,0.24)',
            overflow: 'hidden',
            display: 'inline-block'
          }
        }, e('span', {
          style: {
            display: 'block',
            height: '100%',
            width: `${(ratio * 100).toFixed(1)}%`,
            background: 'var(--vscode-progressBar-background, #0e70c0)'
          }
        })),
        e('span', { key: 'step', style: { fontFamily: 'monospace', fontSize: '0.75rem', opacity: 0.8 } }, stepText)
      ]));
    } else {
      nodes.push(e('span', { key: 'step', style: { fontFamily: 'monospace', fontSize: '0.75rem', opacity: 0.8 } }, stepText));
    }
    return e('div', { style: { display: 'grid', gap: '0.15rem' } }, nodes);
  }

  const deleteEntry = React.useCallback(async (id) => {
    if (activeSession.current !== session) return;
    if (!Number.isFinite(id)) return;
    if (session.pendingDeleteIds.has(id)) return;
    session.pendingDeleteIds.add(id);
    try {
      await rpc.call('DevWidgets.PTracker.deleteProgressRefRpc', { id });
      if (activeSession.current !== session) return;
      setSnapshot((prev) => prev?.session === session
        ? { ...prev, entries: prev.entries.filter((entry) => Number(entry.id) !== id) }
        : prev);
    } catch (err) {
      if (activeSession.current === session) setError(String(err));
    } finally {
      session.pendingDeleteIds.delete(id);
    }
  }, [rpc, session]);

  const refreshNow = React.useCallback(async (origin = 'manual') => {
    if (activeSession.current !== session || session.inFlight) return;
    session.inFlight = true;
    if (origin === 'manual') setManualLoading(true);
    setError(null);
    try {
      const next = await rpc.call('DevWidgets.PTracker.readProgressViewRpc', {});
      if (activeSession.current !== session) return;
      const nextEntries = Array.isArray(next?.entries) ? next.entries : [];
      const nowNs = Number(next?.nowNs);
      setSnapshot({ session, entries: nextEntries, nowNs: Number.isFinite(nowNs) ? nowNs : 0, atMs: Date.now() });
    } catch (err) {
      if (activeSession.current === session) setError(String(err));
    } finally {
      if (activeSession.current === session && origin === 'manual') setManualLoading(false);
      session.inFlight = false;
    }
  }, [rpc, session]);

  React.useEffect(() => {
    if (!autoEnabled) return;
    const id = setInterval(() => {
      void refreshNow('auto');
    }, Math.max(100, periodMs));
    return () => clearInterval(id);
  }, [autoEnabled, periodMs, refreshNow]);

  React.useEffect(() => {
    void refreshNow('auto');
  }, [refreshNow]);

  React.useEffect(() => {
    for (const entry of entries) {
      const id = Number(entry.id);
      const remainingMs = getRemainingMs(entry);
      if (Number.isFinite(id) && remainingMs !== null && remainingMs <= 0) {
        void deleteEntry(id);
      }
    }
  }, [entries, estimatedNowNs, deleteEntry, settings.autoRemove, RETAIN_DONE_MS]);

  return e('div', { style: { display: 'grid', gap: '0.35rem' } }, [
    e('strong', { key: 'title' }, 'Progress Tracker'),
    e('div', {
      key: 'controls',
      style: {
        display: 'flex',
        alignItems: 'center',
        gap: '0.55rem',
        flexWrap: 'wrap',
        fontSize: '0.85rem'
      }
    }, [
      e('label', { key: 'enabled', style: { display: 'inline-flex', alignItems: 'center', gap: '0.25rem' } }, [
        e('input', {
          key: 'auto',
          type: 'checkbox',
          checked: autoEnabled,
          onChange: (ev) => setAutoEnabled(Boolean(ev.target.checked))
        }),
        'Auto'
      ]),
      e('label', { key: 'period', style: { display: 'inline-flex', alignItems: 'center', gap: '0.25rem' } }, [
        'Every',
        e('input', {
          key: 'period',
          type: 'number',
          min: 100,
          step: 100,
          value: periodMs,
          onChange: (ev) => {
            const n = Number(ev.target.value);
            if (Number.isFinite(n)) setPeriodMs(boundedNat(n, 250, 100, 60000));
          },
          disabled: !autoEnabled,
          style: { width: '4.7rem', padding: '0 0.2rem', lineHeight: '1.2rem' }
        }),
        'ms'
      ]),
      e('button', {
        key: 'btn',
        onClick: () => void refreshNow('manual'),
        disabled: manualLoading,
        style: { padding: '0 0.4rem', lineHeight: '1.2rem' }
      }, manualLoading ? 'Refreshing...' : 'Refresh'),
      panelButton('Reset panel', resetSettings, false, 'Restore the configuration supplied by the Lean file.')
    ]),
    e('details', { key: 'settings' }, [
      e('summary', { key: 'summary' }, 'Progress settings'),
      e('div', { key: 'presets', style: { display: 'flex', flexWrap: 'wrap', gap: '0.4rem' } }, [
        panelButton('Live', () => setSettings({ autoRefresh: true, intervalMs: 250, autoRemove: true, retainDoneMs: 20000 })),
        panelButton('Quiet', () => setSettings({ autoRefresh: true, intervalMs: 1000, autoRemove: true, retainDoneMs: 60000 })),
        panelButton('Manual', () => setSettings((prev) => ({ ...prev, autoRefresh: false, autoRemove: false })))
      ]),
      e('label', { key: 'auto-remove' }, [
        e('input', { key: 'enabled', type: 'checkbox', checked: settings.autoRemove,
          onChange: (ev) => setSettings((prev) => ({ ...prev, autoRemove: Boolean(ev.target.checked) })) }),
        'Remove completed tasks automatically'
      ]),
      e('label', { key: 'retention' }, [
        ' Keep for ',
        e('input', { key: 'seconds', type: 'number', min: 1, max: 3600, value: settings.retainDoneMs / 1000,
          disabled: !settings.autoRemove, style: { width: '4.5rem' },
          onChange: (ev) => setSettings((prev) => ({ ...prev,
            retainDoneMs: boundedNat(Number(ev.target.value) * 1000, 20000, 1000, 3600000) })) }),
        ' seconds'
      ])
    ]),
    e('div', { key: 'rows', style: { display: 'grid', gap: '0.3rem', minWidth: 0, overflowX: 'auto' } }, [
      entries.length === 0
        ? e('em', { key: 'empty' }, 'No tracked progress refs.')
        : e('table', { key: 'table', style: { borderCollapse: 'collapse', width: '100%' } }, [
            e('thead', { key: 'thead' }, e('tr', {}, [
              e('th', { key: 'h-id', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Ref'),
              e('th', { key: 'h-st', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'St'),
              e('th', { key: 'h-value', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Value'),
              e('th', { key: 'h-created', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Age'),
              e('th', { key: 'h-updated', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Updated'),
              e('th', { key: 'h-actions', style: { textAlign: 'right', padding: '0.2rem 0 0.2rem 0' } }, 'Actions')
            ])),
            e('tbody', { key: 'tbody' }, entries.map((entry) => {
              const status = String(entry.status ?? 'running');
              const isClosed = isClosedStatus(status);
              const idNum = Number(entry.id);
              const deleting = session.pendingDeleteIds.has(idNum);
              const createdNs = Number(entry.createdAtNs);
              const updatedNs = Number(entry.lastUpdatedAtNs);
              return e('tr', {
                key: String(entry.id),
                style: {
                  opacity: isClosed ? 0.62 : 1,
                  background: rowBackground(status)
                }
              }, [
                e('td', { key: 'id', style: { padding: '0.2rem 0.5rem 0.2rem 0' } }, `#${entry.id}`),
                e('td', { key: 'status', style: { padding: '0.2rem 0.5rem 0.2rem 0', fontFamily: 'monospace' }, title: statusLabel(status) }, statusIcon(status)),
                e('td', { key: 'value', style: { padding: '0.2rem 0.5rem 0.2rem 0' } }, renderValue(entry)),
                e('td', {
                  key: 'created',
                  style: { padding: '0.2rem 0.5rem 0.2rem 0', fontFamily: 'monospace' },
                  title: `created @ ${formatMonoSeconds(createdNs)}`
                }, formatElapsedSince(createdNs)),
                e('td', {
                  key: 'updated',
                  style: { padding: '0.2rem 0.5rem 0.2rem 0', fontFamily: 'monospace' },
                  title: `updated @ ${formatMonoSeconds(updatedNs)}`
                }, formatElapsedSince(updatedNs)),
                e('td', {
                  key: 'actions',
                  style: {
                    padding: '0.2rem 0 0.2rem 0',
                    display: 'flex',
                    justifyContent: 'flex-end',
                    alignItems: 'center',
                    gap: '0.35rem'
                  }
                }, isClosed ? [
                  renderExpiry(entry),
                  e('button', {
                    key: 'remove',
                    title: 'Remove from view now',
                    onClick: () => void deleteEntry(idNum),
                    disabled: deleting,
                    style: { padding: '0 0.35rem', lineHeight: '1.1rem' }
                  }, deleting ? '...' : '×')
                ] : null)
              ]);
            }))
          ])
    ]),
    error ? e('pre', { key: 'err', style: { color: 'var(--vscode-errorForeground)', margin: 0 } }, error) : null
  ]);
}
"

end DevWidgets.PTracker
