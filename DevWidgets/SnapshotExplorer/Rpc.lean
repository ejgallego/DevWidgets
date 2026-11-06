import DevWidgets.SnapshotExplorer.Observe

namespace DevWidgets.SnapshotExplorer
open Lean Server

/-- Initialized once per file-worker process. No snapshots or request resources are retained. -/
private initialize workerGeneration : String ←
  return toString ((← IO.getRandomBytes 16).toList)

@[server_rpc_method]
meta def readSnapshots (params : ReadParams) : RequestM (RequestTask View) :=
  RequestM.asTask do
    let doc ← RequestM.readDoc
    observe workerGeneration doc.meta.uri doc.meta.version doc.meta.text doc.initSnap params

end DevWidgets.SnapshotExplorer
