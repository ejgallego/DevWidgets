/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import Std.Sync.Mutex
import Std.Data.TreeMap
import DevWidgets.Lib.Resource

namespace DevWidgets.PTracker

open Lean

/-- In-memory status for one tracked progress ref. -/
inductive ProgressStatus where
  | running
  | done
  | failed
  | cancelled
  deriving Inhabited, BEq, ToJson, FromJson

/-- In-memory state for one tracked progress ref. -/
structure TrackedProgressRef where
  id : Nat
  description : String
  label : String
  stepsDone : Nat
  totalSteps? : Option Nat
  createdAtNs : Nat
  lastUpdatedAtNs : Nat
  status : ProgressStatus := .running
  closedAtNs? : Option Nat := none
  deriving ToJson, FromJson

/-- Shared mutable state for all tracked progress refs. -/
private structure ProgressRegistry where
  nextId : Nat := 0
  refs : Std.TreeMap Nat TrackedProgressRef := {}
  deriving Inhabited

/-- Handle to one tracked progress ref. -/
structure ProgressRef where
  id : Nat

/-- Mutable registry of all currently tracked refs. -/
private initialize progressRegistry : Std.Mutex ProgressRegistry ← Std.Mutex.new {}

/--
Creates a new tracked progress ref and returns a handle to it.

- `totalSteps?`: bounded progress when `some n`, unbounded when `none`.
- `description`: short stable description of the tracked task.
- `initialLabel`: initial status text shown to users.
-/
def ProgressRef.create (totalSteps? : Option Nat) (description : String)
    (initialLabel : String := "") : IO ProgressRef := do
  let createdAtNs ← IO.monoNanosNow
  progressRegistry.atomically do
    let st ← get
    let refId := st.nextId
    let entry := {
      id := refId
      description := description
      label := initialLabel
      stepsDone := 0
      totalSteps? := totalSteps?
      createdAtNs := createdAtNs
      lastUpdatedAtNs := createdAtNs
      status := .running
      closedAtNs? := none
    }
    set {
      st with
        nextId := refId + 1
        refs := st.refs.insert refId entry
    }
    pure { id := refId }

/-- Finish a running task once. A prior terminal outcome is preserved. -/
private def ProgressRef.finish (ref : ProgressRef) (status : ProgressStatus) : IO Unit := do
  let nowNs ← IO.monoNanosNow
  progressRegistry.atomically do
    let st ← get
    match st.refs.get? ref.id with
    | none => pure () -- Another panel may already have removed a closed task.
    | some entry =>
      if entry.status != .running then
        pure ()
      else
        let entry' := { entry with status, closedAtNs? := some nowNs, lastUpdatedAtNs := nowNs }
        set { st with refs := st.refs.insert ref.id entry' }

/-- Close successfully, or explicitly mark cancellation. Repeated closure is harmless. -/
def ProgressRef.close (ref : ProgressRef) (interrupted : Bool := false) : IO Unit :=
  ref.finish (if interrupted then .cancelled else .done)

/-- Mark a task as failed. A previously recorded cancellation is preserved. -/
def ProgressRef.fail (ref : ProgressRef) : IO Unit :=
  ref.finish .failed

/--
Updates progress and refreshes `lastUpdatedAtNs`.

- `stepsDone`: how many steps have happened so far.
- `label?`: optional replacement for current label/status text.
Throws an error if the ref id does not exist or is not running.
-/
def ProgressRef.update (ref : ProgressRef) (stepsDone : Nat)
    (label? : Option String := none) : IO Unit := do
  let nowNs ← IO.monoNanosNow
  progressRegistry.atomically do
    let st ← get
    match st.refs.get? ref.id with
    | none =>
      throw <| IO.userError s!"PTracker.update: unknown ref id {ref.id}"
    | some entry =>
      if entry.status != .running then
        throw <| IO.userError s!"PTracker.update: ref id {ref.id} is not running"
      else
        let stepsDone := match entry.totalSteps? with
          | some total => min stepsDone total
          | none => stepsDone
        let entry' := {
          entry with
            stepsDone := stepsDone
            label := label?.getD entry.label
            lastUpdatedAtNs := nowNs
        }
        set { st with refs := st.refs.insert ref.id entry' }
        pure ()

/--
Create, use, and close a tracked progress ref safely.

An unsuccessful action is marked `failed`. `MonadFinally` does not distinguish
interrupts from other failures. An action that recognizes cancellation can call
`ref.close (interrupted := true)` before propagating it; cleanup preserves that outcome.
Closure records an outcome but does not delete the entry.
-/
def withProgressRef [Monad m] [MonadLiftT IO m] [MonadFinally m]
    (totalSteps? : Option Nat) (description : String) (initialLabel : String := "")
    (act : ProgressRef → m α) : m α := do
  DevWidgets.Lib.withResource
    (liftM <| ProgressRef.create totalSteps? description initialLabel)
    (fun ref failed => do
      liftM <| if failed then ref.fail else ref.close
      pure ())
    act

/-- Lean elaboration variant: distinguish interrupts from other failures, then rethrow unchanged. -/
def withElabProgressRef [Monad m] [MonadLiftT IO m] [MonadFinally m]
    [MonadAlwaysExcept Exception m]
    (totalSteps? : Option Nat) (description : String) (initialLabel : String := "")
    (act : ProgressRef → m α) : m α :=
  withProgressRef totalSteps? description initialLabel fun ref => do
    let _ : MonadExceptOf Exception m := MonadAlwaysExcept.except
    try act ref
    catch e =>
      if e.isInterrupt then liftM <| ref.close (interrupted := true)
      throw e

/-- Materialize the current registry into JSON-safe refs for the widget. -/
def listProgressRefs : IO (Array TrackedProgressRef) := do
  let refs ← progressRegistry.atomically do
    pure (← get).refs
  pure <| refs.foldl (init := #[]) fun out _ entry =>
    out.push entry

/--
Delete a completed progress ref from the registry.

Already absent entries count as successfully deleted, including across panels.
Throws only if the entry is still running.
-/
def deleteProgressRef (refId : Nat) : IO Unit := do
  progressRegistry.atomically do
    let st ← get
    match st.refs.get? refId with
    | none => pure ()
    | some entry =>
      if entry.status == .running then
        throw <| IO.userError s!"PTracker.delete: ref id {refId} is still running"
      else
        set { st with refs := st.refs.erase refId }

/-- Explicit retention policy for callers without a widget. No background thread is started. -/
structure RetentionPolicy where
  /-- Remove terminal entries at least this old, in milliseconds. -/
  maxAgeMs? : Option Nat := none
  /-- Keep at most this many newest terminal entries, independently of their age. -/
  maxCompleted? : Option Nat := none

/-- Apply retention atomically, preserving every running task. Returns the number removed. -/
def pruneProgressRefs (policy : RetentionPolicy) : IO Nat := do
  let nowNs ← IO.monoNanosNow
  progressRegistry.atomically do
    let st ← get
    let completed := st.refs.foldl (init := #[]) fun out _ entry =>
      if entry.status == .running then out else out.push entry
    let completed := completed.qsort fun a b =>
      a.closedAtNs?.getD 0 > b.closedAtNs?.getD 0 ||
        (a.closedAtNs? == b.closedAtNs? && a.id > b.id)
    let mut refs := st.refs
    let mut removed := 0
    for (entry, i) in completed.zipIdx do
      let expired := policy.maxAgeMs?.any fun ms =>
        nowNs - entry.closedAtNs?.getD nowNs >= ms * 1000000
      let excess := policy.maxCompleted?.any (i >= ·)
      if expired || excess then
        refs := refs.erase entry.id
        removed := removed + 1
    set { st with refs }
    return removed

end DevWidgets.PTracker
