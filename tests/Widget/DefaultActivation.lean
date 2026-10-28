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
