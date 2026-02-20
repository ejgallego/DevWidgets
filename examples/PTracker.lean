import DevWidgets.PTracker.Widget
import Lean.Widget
import Lean

open DevWidgets.PTracker
open Lean Elab Command

/-- Small CPU burner to keep elaboration busy between progress updates. -/
private def burnWork (n : Nat) : IO UInt64 := do
  let mut x : UInt64 := 1469598103934665603
  for i in [0:n] do
    let k := UInt64.ofNat (i + 1)
    x := (x ^^^ k) * 1099511628211
  return x

/--
Artificially run elaboration in `steps`.
- `work`: CPU work units per step
- `sleepMs`: sleep time per step in milliseconds
Updates one progress ref on each step.
-/
syntax (name := progressElabCmd) "#progress_elab" num num num : command

elab_rules : command
  | `(#progress_elab $steps:num $work:num $sleepMs:num) => do
      let steps := steps.getNat
      let work := work.getNat
      let sleepMs := UInt32.ofNat sleepMs.getNat
      withProgressRef (some steps) "main task" "starting main task" fun mainRef => do
        for i in [0:steps] do
          liftCoreM $ Lean.Core.checkInterrupted
          let _ ← burnWork work
          let done := i + 1
          liftIO <| mainRef.update done (label? := some s!"main step: {done} / {steps}")
          if sleepMs != 0 then
            liftIO <| IO.sleep sleepMs

show_panel_widgets [progressWidget]

#progress_elab 111 54220 102
