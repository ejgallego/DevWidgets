import DevWidgets.CE.API
import DevWidgets.DocString.API
import DevWidgets.InfoTreeExplorer.API
import DevWidgets.PTracker.API

/-!
The `.API` imports do not activate panels. Enable only the tools needed here.
`local` restricts each choice to this file/section instead of downstream imports.
-/

show_panel_widgets [local DevWidgets.CE.compilerExplorerWidget with DevWidgets.CE.Config.verbose]
show_panel_widgets [local DevWidgets.DocString.docStringWidget with DevWidgets.DocString.Config.expanded]
show_panel_widgets [local DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget with
  ({ DevWidgets.InfoTreeExplorer.Config.focused with maxChildren := 15 } : DevWidgets.InfoTreeExplorer.Config)]
show_panel_widgets [local DevWidgets.PTracker.progressWidget with
  ({ DevWidgets.PTracker.Config.quiet with autoRemove := false } : DevWidgets.PTracker.Config)]

/-- Move the cursor here to inspect documentation, compiler output, or elaboration. -/
def configuredExample (n : Nat) : Nat := n + 1

-- Hide one panel locally without affecting the other widgets.
show_panel_widgets [-DevWidgets.CE.compilerExplorerWidget]
