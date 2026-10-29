import DevWidgets.CE.API
import DevWidgets.DocString.API
import DevWidgets.InfoTreeExplorer.API
import DevWidgets.PTracker.API

/-!
The `.API` imports do not activate panels. Enable only the tools needed here.
`configure_panel_widget` replaces existing instances in this file/section only.
-/

configure_panel_widget DevWidgets.CE.compilerExplorerWidget with DevWidgets.CE.Config.verbose
configure_panel_widget DevWidgets.DocString.docStringWidget with DevWidgets.DocString.Config.expanded
configure_panel_widget DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget with
  ({ DevWidgets.InfoTreeExplorer.Config.focused with maxChildren := 15 } : DevWidgets.InfoTreeExplorer.Config)
configure_panel_widget DevWidgets.PTracker.progressWidget with
  ({ DevWidgets.PTracker.Config.quiet with autoRemove := false } : DevWidgets.PTracker.Config)

/-- Move the cursor here to inspect documentation, compiler output, or elaboration. -/
def configuredExample (n : Nat) : Nat := n + 1

-- Hide one panel locally without affecting the other widgets.
show_panel_widgets [-DevWidgets.CE.compilerExplorerWidget]
