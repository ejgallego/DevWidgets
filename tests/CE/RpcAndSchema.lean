import DevWidgets.CE
import DevWidgets.CE.Analysis
import Lean

namespace DevWidgets.Tests.CE.RpcAndSchema

open Lean

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain `{needle}`\n---\n{haystack}\n---"

private def assertNotContains (label haystack needle : String) : CoreM Unit := do
  if haystack.contains needle then
    throwError m!"expected `{label}` to not contain `{needle}`\n---\n{haystack}\n---"

private def hasDescriptorId (id : String) (xs : Array DevWidgets.CE.CEOptionDescriptor) : Bool :=
  xs.any (fun x => x.id == id)

#eval show CoreM Unit from do
  let js := DevWidgets.CE.widgetJs
  assertContains "CE widget JS" js "rs.call('DevWidgets.CE.ceOptionSchema', {})"
  assertContains "CE widget JS" js "rs.call('DevWidgets.CE.irAtPos', params)"
  assertNotContains "CE widget JS" js "rs.call('ceOptionSchema', {})"
  assertNotContains "CE widget JS" js "rs.call('irAtPos', params)"

#eval show CoreM Unit from do
  let display := DevWidgets.CE.CEDisplayOptions.schema
  let compiler := DevWidgets.CE.CECompilerOptions.schema
  unless display.size > 0 do
    throwError "expected non-empty display option schema"
  unless compiler.size > 0 do
    throwError "expected non-empty compiler option schema"
  unless hasDescriptorId "ppExplicit" display do
    throwError "expected display schema to include `ppExplicit`"
  unless hasDescriptorId "explicitRc" compiler do
    throwError "expected compiler schema to include `explicitRc`"

end DevWidgets.Tests.CE.RpcAndSchema
