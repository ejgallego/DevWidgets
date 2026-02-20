import DevWidgets.ShowDoc
import DevWidgets.CE
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
- ShowDoc must call only the fully-qualified RPC method name.
- No fallback probing with unqualified `docAtPos`.
-/
#eval show CoreM Unit from do
  let js := DevWidgets.ShowDoc.widgetJs
  assertContains "ShowDoc widget JS" js "rs.call('DevWidgets.ShowDoc.docAtPos', params)"
  assertNotContains "ShowDoc widget JS" js "for (const method of ['docAtPos', 'DevWidgets.ShowDoc.docAtPos'])"

/-
Regression test:
- CE must call only the fully-qualified RPC method name.
- No fallback probing with unqualified `irAtPos`.
-/
#eval show CoreM Unit from do
  let js := DevWidgets.CE.widgetJs
  assertContains "CE widget JS" js "rs.call('DevWidgets.CE.irAtPos', params)"
  assertNotContains "CE widget JS" js "for (const method of ['irAtPos', 'DevWidgets.CE.irAtPos'])"

end DevWidgets.Tests.Rpc.QualifiedMethodNames
