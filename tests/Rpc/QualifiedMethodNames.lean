import DevWidgets.DocString
import DevWidgets.CE
import DevWidgets.InfoTreeExplorer
import DevWidgets.PTracker
import Lean

namespace DevWidgets.Tests.Rpc.QualifiedMethodNames

open Lean

-- A valid JS method name is not enough: each entry point must register an executable handler.
private unsafe def evalWrapper (env : Environment) (opts : Options) (name : Name) :
    Except String Server.RpcProcedure :=
  env.evalConstCheck Server.RpcProcedure opts ``Server.RpcProcedure name

#eval show CoreM Unit from do
  let env ← getEnv
  for method in [`DevWidgets.CE.ceOptionSchema, `DevWidgets.CE.irAtPos,
      `DevWidgets.DocString.docAtPos, `DevWidgets.InfoTreeExplorer.infoTreeAtPos,
      `DevWidgets.PTracker.readProgressViewRpc, `DevWidgets.PTracker.deleteProgressRefRpc] do
    let some wrapper := Server.userRpcProcedures.find? env method
      | throwError "RPC method {method} is not registered"
    match evalWrapper env (← getOptions) wrapper with
    | .ok _ => pure ()
    | .error error => throwError "RPC method {method} cannot be evaluated: {error}"

end DevWidgets.Tests.Rpc.QualifiedMethodNames
