import DevWidgets.PTracker
import Lean

open Lean DevWidgets.PTracker

private def entry (id : Nat) : IO TrackedProgressRef := do
  let some entry := (← listProgressRefs).find? (·.id == id)
    | throw <| IO.userError "missing progress entry"
  return entry

private def assertStatus (id : Nat) (expected : ProgressStatus) : IO Unit := do
  unless (← entry id).status == expected do throw <| IO.userError "unexpected progress outcome"

#eval show IO Unit from do
  let id ← withProgressRef (some 3) "success" "" fun ref => do
    ref.update 10
    pure ref.id
  assertStatus id .done
  unless (← entry id).stepsDone == 3 do throw <| IO.userError "progress was not clamped"
  let closedAt := (← entry id).closedAtNs?
  let ref : ProgressRef := ⟨id⟩
  ref.close (interrupted := true)
  assertStatus id .done
  unless (← entry id).closedAtNs? == closedAt do throw <| IO.userError "closed twice"
  let rejected ← try ref.update 1; pure false catch _ => pure true
  unless rejected do throw <| IO.userError "updated closed task"
  deleteProgressRef id
  deleteProgressRef id
  ref.close -- Scoped cleanup is safe even after explicit closure and another panel's deletion.

#eval show IO Unit from do
  for cancel in [false, true] do
    let idRef ← IO.mkRef 0
    let caught ← try
      withProgressRef none "failure" "" fun ref => do
        idRef.set ref.id
        if cancel then ref.close (interrupted := true)
        throw <| IO.userError "body failure"
      pure false
    catch e => pure (e.toString.contains "body failure")
    unless caught do throw <| IO.userError "action failure was not propagated"
    let id ← idRef.get
    assertStatus id (if cancel then .cancelled else .failed)
    deleteProgressRef id

#eval show IO Unit from do
  let running ← ProgressRef.create none "running"
  let rejected ← try deleteProgressRef running.id; pure false catch _ => pure true
  unless rejected do throw <| IO.userError "deleted running task"
  let first ← ProgressRef.create none "first"
  first.close
  let second ← ProgressRef.create none "second"
  second.fail
  unless (← pruneProgressRefs { maxCompleted? := some 1 }) == 1 do
    throw <| IO.userError "count retention did not remove oldest terminal entry"
  assertStatus running.id .running
  assertStatus second.id .failed
  unless (← pruneProgressRefs { maxAgeMs? := some 0 }) == 1 do
    throw <| IO.userError "age retention did not remove completed entry"
  assertStatus running.id .running
  running.close
  deleteProgressRef running.id

-- CoreM normally bypasses catch clauses for interrupts. The elaboration wrapper only
-- observes the outcome and must rethrow the exact interrupt to its caller.
#eval show CoreM Unit from do
  let idRef ← IO.mkRef 0
  let _ : MonadExceptOf Exception CoreM := MonadAlwaysExcept.except
  let caught ← try
    withElabProgressRef none "cancelled elaboration" "" fun ref => do
      idRef.set ref.id
      throwInterruptException
    pure false
  catch e => pure e.isInterrupt
  unless caught do throwError "interrupt was not propagated"
  let id ← idRef.get
  assertStatus id .cancelled
  deleteProgressRef id
