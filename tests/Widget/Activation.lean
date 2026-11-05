import DevWidgets.CE.API
import DevWidgets.DocString.API
import DevWidgets.InfoTreeExplorer.API
import DevWidgets.PTracker.API
import Lean

open Lean

-- API imports provide methods and widget definitions without activating panels.
#eval show MetaM Unit from do
  unless (← Widget.evalPanelWidgets).isEmpty do
    throwError "API imports must not enable panels"
  for method in [`DevWidgets.CE.irAtPos, `DevWidgets.DocString.docAtPos,
      `DevWidgets.InfoTreeExplorer.infoTreeAtPos, `DevWidgets.PTracker.readProgressViewRpc] do
    unless (Server.userRpcProcedures.find? (← getEnv) method).isSome do
      throwError "API import did not register {method}"

show_panel_widgets [local DevWidgets.CE.compilerExplorerWidget with DevWidgets.CE.Config.verbose]
show_panel_widgets [local DevWidgets.DocString.docStringWidget with DevWidgets.DocString.Config.expanded]
show_panel_widgets [local DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget with DevWidgets.InfoTreeExplorer.Config.focused]
show_panel_widgets [local DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.manual]

#eval show MetaM Unit from do
  let panels ← Widget.evalPanelWidgets
  unless panels.size == 4 do
    throwError "expected four independently configured panels"
  let some progress := panels.find? (·.id == `DevWidgets.PTracker.progressWidget)
    | throwError "missing progress panel"
  let props := progress.props.run' {}
  match props.getObjValAs? Bool "autoRefresh" with
  | .ok false => pure ()
  | _ => throwError "manual progress configuration was not encoded"

show_panel_widgets [-DevWidgets.PTracker.progressWidget]

#eval show MetaM Unit from do
  unless (← Widget.evalPanelWidgets).size == 3 do
    throwError "hiding a panel should leave the other panels enabled"
