import DevWidgets.CE
import DevWidgets.InfoTreeExplorer
import DevWidgets.PTracker
import DevWidgets.DocString

open Lean

namespace DevWidgets.Tests.Widget.Runtime

-- Exercise the shipped JavaScript against JSON produced by the actual Lean encoders.
#eval show IO Unit from do
  let schema : DevWidgets.CE.CEOptionSchema := {
    display := DevWidgets.CE.CEDisplayOptions.schema
    compiler := DevWidgets.CE.CECompilerOptions.schema
  }
  let analysis : DevWidgets.CE.IRAtPosResponse := .declaration {
    declName := `testDecl, cursorDeclName := `testDecl, hasIR := false
    ir := .unavailable .notCompilableConstant
    lcnf := .unavailable .notCompilableConstant
  }
  let input := Json.mkObj [
    ("ce", toJson DevWidgets.CE.widgetJs),
    ("infoTree", toJson DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget.javascript),
    ("progress", toJson DevWidgets.PTracker.progressWidget.javascript),
    ("docs", toJson DevWidgets.DocString.widgetJs),
    ("ceConfig", toJson DevWidgets.CE.Config.verbose),
    ("treeConfig", toJson DevWidgets.InfoTreeExplorer.Config.focused),
    ("progressConfig", toJson DevWidgets.PTracker.Config.manual),
    ("docConfig", toJson DevWidgets.DocString.Config.expanded),
    ("schema", toJson schema),
    ("analysis", toJson analysis)
  ]
  let out ← IO.Process.output { cmd := "node", args := #["tests/Widget/runtime.mjs"] }
    (some input.compress)
  unless out.exitCode == 0 do
    throw <| IO.userError s!"Widget runtime regression failed:\n{out.stderr}\n{out.stdout}"
  let request ← IO.ofExcept (Json.parse out.stdout)
  let params ← IO.ofExcept (fromJson? request : Except String DevWidgets.InfoTreeExplorer.InfoTreeAtPosParams)
  unless params.uri? == some "file:///workspace/Example.lean" do
    throw <| IO.userError s!"InfoTreeExplorer lost the source URI: {params.uri?}"

end DevWidgets.Tests.Widget.Runtime
