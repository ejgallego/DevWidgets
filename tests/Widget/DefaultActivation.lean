import DevWidgets.CE
import DevWidgets.DocString
import DevWidgets.InfoTreeExplorer
import DevWidgets.PTracker
import Lean

open Lean

#eval show MetaM Unit from do
  let panels ← Widget.evalPanelWidgets
  for id in [`DevWidgets.CE.compilerExplorerWidget, `DevWidgets.DocString.docStringWidget,
      `DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget, `DevWidgets.PTracker.progressWidget] do
    unless (panels.filter (·.id == id)).size == 1 do
      throwError "expected exactly one panel for {id}"

section

-- Reconfiguration after short imports must replace, rather than duplicate, a panel.
configure_panel_widget DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.quiet
configure_panel_widget DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.manual
configure_panel_widget DevWidgets.CE.compilerExplorerWidget with DevWidgets.CE.Config.verbose
configure_panel_widget DevWidgets.DocString.docStringWidget with DevWidgets.DocString.Config.expanded
configure_panel_widget DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget with DevWidgets.InfoTreeExplorer.Config.focused

#eval show MetaM Unit from do
  let panels ← Widget.evalPanelWidgets
  unless panels.size == 4 do
    throwError "configuration duplicated or removed another panel"
  let some panel := panels.find? (·.id == `DevWidgets.PTracker.progressWidget)
    | throwError "missing progress panel"
  let .ok false := (panel.props.run' {}).getObjValAs? Bool "autoRemove"
    | throwError "the latest configuration must win"

end

#eval show MetaM Unit from do
  let panels ← Widget.evalPanelWidgets
  unless panels.size == 4 do
    throwError "leaving the section did not restore imported panels"
  let some panel := panels.find? (·.id == `DevWidgets.PTracker.progressWidget)
    | throwError "missing restored progress panel"
  unless (panel.props.run' {}).compress == "{}" do
    throwError "section-local configuration leaked"
