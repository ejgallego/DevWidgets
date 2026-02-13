import DevWidgets.PTracker.Widget
import Lean.Widget
import Lean

open DevWidgets.IorefWidget
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
Updates two progress refs on each step so the widget can show multiple values.
-/
syntax (name := progressElabCmd) "#progress_elab" num num num : command

elab_rules : command
  | `(#progress_elab $steps:num $work:num $sleepMs:num) => do
      let steps := steps.getNat
      let work := work.getNat
      let sleepMs := UInt32.ofNat sleepMs.getNat
      let mainRefId ← liftIO <| createProgressRef "starting main task"

      for i in [0:steps] do
        let _ ← burnWork work
        let done := i + 1
        let _ ← liftIO <| updateProgressRef mainRefId s!"main step: {done} / {steps}"
        if sleepMs != 0 then
          liftIO <| IO.sleep sleepMs
      let _ ← liftIO <| destroyProgressRef mainRefId

show_panel_widgets [ioRefWidget]

#progress_elab 222 50000 200
