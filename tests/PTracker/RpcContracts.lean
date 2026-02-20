import DevWidgets.PTracker
import Lean

namespace DevWidgets.Tests.PTracker.RpcContracts

open Lean

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain `{needle}`\n---\n{haystack}\n---"

private def assertNotContains (label haystack needle : String) : CoreM Unit := do
  if haystack.contains needle then
    throwError m!"expected `{label}` to not contain `{needle}`\n---\n{haystack}\n---"

#eval show CoreM Unit from do
  let js := DevWidgets.PTracker.progressWidget.javascript
  assertContains "PTracker widget JS" js "rpc.call('DevWidgets.PTracker.readProgressViewRpc', {})"
  assertContains "PTracker widget JS" js "rpc.call('DevWidgets.PTracker.deleteProgressRefRpc', { id })"
  assertContains "PTracker widget JS" js "setInterval(() => {"
  assertNotContains "PTracker widget JS" js "rpc.call('readProgressViewRpc', {})"
  assertNotContains "PTracker widget JS" js "rpc.call('deleteProgressRefRpc', { id })"

end DevWidgets.Tests.PTracker.RpcContracts
