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
structure ProgressRegistry where
  nextId : Nat := 0
  refs : Std.TreeMap Nat TrackedProgressRef := {}
  closedCount : Nat := 0
  interruptedCloseCount : Nat := 0
  deriving Inhabited

/-- Handle to one tracked progress ref. -/
structure ProgressRef where
  id : Nat

/-- Mutable registry of all currently tracked refs. -/
initialize progressRegistry : Std.Mutex ProgressRegistry ← Std.Mutex.new {}

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

/--
Closes a tracked progress ref.

Throws an error if the ref id does not exist.
-/
def ProgressRef.close (ref : ProgressRef) {interrupted : Bool} : IO Unit := do
  let nowNs ← IO.monoNanosNow
  progressRegistry.atomically do
    let st ← get
    match st.refs.get? ref.id with
    | none =>
      throw <| IO.userError s!"PTracker.close: unknown ref id {ref.id}"
    | some entry =>
      if entry.status != .running then
        pure ()
      else
        let entry' := {
          entry with
            status := if interrupted then .cancelled else .done
            closedAtNs? := some nowNs
            lastUpdatedAtNs := nowNs
        }
        let interruptedCloseCount :=
          st.interruptedCloseCount + (if interrupted then 1 else 0)
        set {
          st with
            refs := st.refs.insert ref.id entry'
            closedCount := st.closedCount + 1
            interruptedCloseCount := interruptedCloseCount
        }
        pure ()

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

If `k` fails (including with an interrupt), the ref is closed with
`interrupted := true`.
-/
def withProgressRef [Monad m] [MonadLiftT IO m] [MonadFinally m]
    (totalSteps? : Option Nat) (description : String) (initialLabel : String := "")
    (act : ProgressRef → m α) : m α := do
  DevWidgets.Lib.withResource
    (liftM <| ProgressRef.create totalSteps? description initialLabel)
    (fun ref interrupted => do
      liftM <| ref.close (interrupted := interrupted)
      pure ())
    act

/-- Materialize the current registry into JSON-safe refs for the widget. -/
def listProgressRefs : IO (Array TrackedProgressRef) := do
  let refs ← progressRegistry.atomically do
    pure (← get).refs
  pure <| refs.foldl (init := #[]) fun out _ entry =>
    out.push entry

/--
Delete a completed progress ref from the registry.

Throws if the ref id does not exist or if it is still running.
-/
def deleteProgressRef (refId : Nat) : IO Unit := do
  progressRegistry.atomically do
    let st ← get
    match st.refs.get? refId with
    | none =>
      throw <| IO.userError s!"PTracker.delete: unknown ref id {refId}"
    | some entry =>
      if entry.status == .running then
        throw <| IO.userError s!"PTracker.delete: ref id {refId} is still running"
      else
        set { st with refs := st.refs.erase refId }

end DevWidgets.PTracker
