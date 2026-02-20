import DevWidgets.DocString
import DevWidgets.CE
import DevWidgets.InfoTreeExplorer
import Lean

namespace DevWidgets.Tests.Rpc.QualifiedMethodNames

open Lean

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain `{needle}`\n---\n{haystack}\n---"

private def assertNotContains (label haystack needle : String) : CoreM Unit := do
  if haystack.contains needle then
    throwError m!"expected `{label}` to not contain `{needle}`\n---\n{haystack}\n---"

/-
Regression test:
- DocString must call only the fully-qualified RPC method name.
- No fallback probing with unqualified `docAtPos`.
-/
#eval show CoreM Unit from do
  let js := DevWidgets.DocString.widgetJs
  assertContains "DocString widget JS" js "rs.call('DevWidgets.DocString.docAtPos', params)"
  assertNotContains "DocString widget JS" js "for (const method of ['docAtPos', 'DevWidgets.DocString.docAtPos'])"

/-
Regression test:
- CE must call only the fully-qualified RPC method name.
- No fallback probing with unqualified `irAtPos`.
-/
#eval show CoreM Unit from do
  let js := DevWidgets.CE.widgetJs
  assertContains "CE widget JS" js "rs.call('DevWidgets.CE.irAtPos', params)"
  assertNotContains "CE widget JS" js "for (const method of ['irAtPos', 'DevWidgets.CE.irAtPos'])"

/- 
Regression test:
- InfoTreeExplorer must call only the fully-qualified RPC method name.
- No fallback probing with unqualified `infoTreeAtPos`.
-/
#eval show CoreM Unit from do
  let js := DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget.javascript
  assertContains "InfoTreeExplorer widget JS" js "rs.call('DevWidgets.InfoTreeExplorer.infoTreeAtPos', params)"
  assertNotContains "InfoTreeExplorer widget JS" js "for (const method of ['infoTreeAtPos', 'DevWidgets.InfoTreeExplorer.infoTreeAtPos'])"

end DevWidgets.Tests.Rpc.QualifiedMethodNames
