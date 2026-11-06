import DevWidgets.SnapshotExplorer.Observe

namespace DevWidgets.SnapshotExplorer
open Lean Server

@[server_rpc_method]
meta def readSnapshots (params : ReadParams) : RequestM (RequestTask View) :=
  RequestM.asTask do
    let doc ← RequestM.readDoc
    observe doc.meta.uri doc.meta.version doc.meta.text doc.initSnap params

end DevWidgets.SnapshotExplorer
