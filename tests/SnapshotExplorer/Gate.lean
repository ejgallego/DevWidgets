import DevWidgets.SnapshotExplorer

/-! Test-only gate. Keep initializers and the controller in an imported module so
Lean can evaluate them while the fixture's elaborator is blocked. -/
namespace DevWidgets.Tests.SnapshotExplorer
open Lean Server

initialize entered : IO.Ref Bool ← IO.mkRef false
initialize released : IO.Ref Bool ← IO.mkRef false

@[server_rpc_method]
meta def gate (release : Bool) : RequestM (RequestTask Bool) :=
  RequestM.asTask do
    if release then released.set true
    entered.get

elab "snapshot_test_gate" : command => do
  entered.set true
  while !(← released.get) do
    Elab.Command.liftCoreM Core.checkInterrupted
    IO.sleep 5

end DevWidgets.Tests.SnapshotExplorer
