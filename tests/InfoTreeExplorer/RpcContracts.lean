import DevWidgets.InfoTreeExplorer.InfoTreeExplorer
import Lean

namespace DevWidgets.Tests.InfoTreeExplorer.RpcContracts

open Lean

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain `{needle}`\n---\n{haystack}\n---"

private def assertNotContains (label haystack needle : String) : CoreM Unit := do
  if haystack.contains needle then
    throwError m!"expected `{label}` to not contain `{needle}`\n---\n{haystack}\n---"

#eval show CoreM Unit from do
  let js := DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget.javascript
  assertContains "InfoTreeExplorer widget JS" js "rs.call('DevWidgets.InfoTreeExplorer.fetchInfoTreeSummary', props)"
  assertContains "InfoTreeExplorer widget JS" js "setInterval(refresh, 1000)"
  assertNotContains "InfoTreeExplorer widget JS" js "rs.call('fetchInfoTreeSummary', props)"

end DevWidgets.Tests.InfoTreeExplorer.RpcContracts
