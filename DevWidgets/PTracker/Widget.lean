/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean

open Lean Server

namespace DevWidgets.IorefWidget

/-- In-memory record for one tracked progress ref. -/
structure TrackedProgressRef where
  id : Nat
  valueRef : IO.Ref String
  createdAtNs : Nat
  lastUpdatedAtNs : Nat

/-- JSON-safe snapshot returned to the widget frontend. -/
structure ProgressSnapshot where
  id : Nat
  value : String
  createdAtNs : Nat
  lastUpdatedAtNs : Nat
  deriving ToJson, FromJson

/-- Mutable registry of all currently tracked refs. -/
initialize trackedProgressRefs : IO.Ref (Array TrackedProgressRef) ← IO.mkRef #[]
initialize nextProgressRefId : IO.Ref Nat ← IO.mkRef 0

/-- Creates a new tracked progress ref and returns its unique id. -/
def createProgressRef (initialValue : String := "") : IO Nat := do
  let createdAtNs ← IO.monoNanosNow
  let valueRef ← IO.mkRef initialValue
  let refId ← nextProgressRefId.get
  nextProgressRefId.set (refId + 1)
  let refs ← trackedProgressRefs.get
  trackedProgressRefs.set (refs.push {
    id := refId
    valueRef := valueRef
    createdAtNs := createdAtNs
    lastUpdatedAtNs := createdAtNs
  })
  pure refId

/--
Removes a tracked progress ref by id.

Returns `true` when a ref with this id existed and was removed, and `false`
when no matching ref was present (no-op).
-/
def destroyProgressRef (refId : Nat) : IO Bool := do
  let refs ← trackedProgressRefs.get
  let refs' := refs.filter (fun entry => entry.id != refId)
  trackedProgressRefs.set refs'
  pure (refs'.size != refs.size)

/--
Updates a tracked ref value and refreshes its `lastUpdatedAtNs` timestamp.
Returns `false` when the id is unknown.
-/
def updateProgressRef (refId : Nat) (newValue : String) : IO Bool := do
  let nowNs ← IO.monoNanosNow
  let refs ← trackedProgressRefs.get
  let mut found := false
  let mut refs' := Array.mkEmpty refs.size
  for entry in refs do
    if entry.id == refId then
      entry.valueRef.set newValue
      refs' := refs'.push { entry with lastUpdatedAtNs := nowNs }
      found := true
    else
      refs' := refs'.push entry
  trackedProgressRefs.set refs'
  pure found

/-- Materialize the current registry into JSON-safe snapshots for the widget. -/
private def listProgressSnapshots : IO (Array ProgressSnapshot) := do
  let refs ← trackedProgressRefs.get
  let refs := refs.qsort (fun a b => a.createdAtNs < b.createdAtNs)
  let mut out := Array.mkEmpty refs.size
  for entry in refs do
    let value ← entry.valueRef.get
    out := out.push {
      id := entry.id
      value := value
      createdAtNs := entry.createdAtNs
      lastUpdatedAtNs := entry.lastUpdatedAtNs
    }
  pure out

structure ReadCounterParams where
  deriving ToJson, FromJson

@[server_rpc_method]
meta def readCounterRpc (_ : ReadCounterParams) : RequestM (RequestTask (Array ProgressSnapshot)) :=
  RequestM.asTask do
    listProgressSnapshots

@[widget_module]
def ioRefWidget : Lean.Widget.Module where
  javascript := "
import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';

const e = React.createElement;

export default function IoRefWidget() {
  const rpc = useRpcSession();
  const [entries, setEntries] = React.useState([]);
  const [manualLoading, setManualLoading] = React.useState(false);
  const [error, setError] = React.useState(null);
  const [autoEnabled, setAutoEnabled] = React.useState(true);
  const [periodMs, setPeriodMs] = React.useState(250);
  const inFlight = React.useRef(false);

  function formatMonoSeconds(ns) {
    if (!Number.isFinite(ns)) return 'n/a';
    return `${(ns / 1_000_000_000).toFixed(3)} s`;
  }

  async function refreshNow(origin = 'manual') {
    if (inFlight.current) return;
    inFlight.current = true;
    if (origin === 'manual') setManualLoading(true);
    setError(null);
    try {
      const next = await rpc.call('DevWidgets.IorefWidget.readCounterRpc', {});
      setEntries(Array.isArray(next) ? next : []);
    } catch (err) {
      setError(String(err));
    } finally {
      if (origin === 'manual') setManualLoading(false);
      inFlight.current = false;
    }
  }

  React.useEffect(() => {
    if (!autoEnabled) return;
    const id = setInterval(() => {
      void refreshNow('auto');
    }, Math.max(100, periodMs));
    return () => clearInterval(id);
  }, [autoEnabled, periodMs]);

  return e('div', { style: { display: 'grid', gap: '0.5rem' } }, [
    e('div', { key: 'controls', style: { display: 'grid', gap: '0.35rem' } }, [
      e('label', { key: 'enabled' }, [
        e('input', {
          type: 'checkbox',
          checked: autoEnabled,
          onChange: (ev) => setAutoEnabled(Boolean(ev.target.checked))
        }),
        ' Auto refresh enabled'
      ]),
      e('label', { key: 'period' }, [
        'Period (ms): ',
        e('input', {
          type: 'number',
          min: 100,
          step: 100,
          value: periodMs,
          onChange: (ev) => {
            const n = Number(ev.target.value);
            if (Number.isFinite(n)) setPeriodMs(Math.max(100, Math.floor(n)));
          },
          disabled: !autoEnabled
        })
      ])
    ]),
    e('button', { key: 'btn', onClick: () => void refreshNow('manual'), disabled: manualLoading }, manualLoading ? 'Refreshing...' : 'Refresh now'),
    e('div', { key: 'rows', style: { display: 'grid', gap: '0.35rem' } }, [
      entries.length === 0
        ? e('em', { key: 'empty' }, 'No tracked progress refs.')
        : e('table', { key: 'table', style: { borderCollapse: 'collapse', width: '100%' } }, [
            e('thead', { key: 'thead' }, e('tr', {}, [
              e('th', { key: 'h-id', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Ref'),
              e('th', { key: 'h-value', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Value'),
              e('th', { key: 'h-created', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Created (mono)'),
              e('th', { key: 'h-updated', style: { textAlign: 'left', padding: '0.2rem 0.5rem 0.2rem 0' } }, 'Last updated (mono)')
            ])),
            e('tbody', { key: 'tbody' }, entries.map((entry) =>
              e('tr', { key: String(entry.id) }, [
                e('td', { key: 'id', style: { padding: '0.2rem 0.5rem 0.2rem 0' } }, `#${entry.id}`),
                e('td', { key: 'value', style: { padding: '0.2rem 0.5rem 0.2rem 0' } }, String(entry.value ?? '')),
                e('td', { key: 'created', style: { padding: '0.2rem 0.5rem 0.2rem 0', fontFamily: 'monospace' } }, formatMonoSeconds(Number(entry.createdAtNs))),
                e('td', { key: 'updated', style: { padding: '0.2rem 0.5rem 0.2rem 0', fontFamily: 'monospace' } }, formatMonoSeconds(Number(entry.lastUpdatedAtNs)))
              ])
            ))
          ])
    ]),
    error ? e('pre', { key: 'err', style: { color: 'var(--vscode-errorForeground)' } }, error) : null
  ]);
}
"

end DevWidgets.IorefWidget
