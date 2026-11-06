import DevWidgets.SnapshotExplorer.API

open Lean Language DevWidgets.SnapshotExplorer

private structure ForeignSnapshot where
  deriving TypeName
private instance : ToSnapshotTree ForeignSnapshot where
  toSnapshotTreeM _ := pure { element := { diagnostics := .empty }, children := #[] }

#eval show IO Unit from do
  let params ← IO.ofExcept (fromJson? (Json.mkObj []) : Except String ReadParams)
  unless params.maxNodes?.isNone && params.command?.isNone do
    throw <| IO.userError "empty requests must use default limits"
  let root : Language.Lean.InitialSnapshot := {
    diagnostics := .empty, ictx := Parser.mkInputContext "" "snapshot-test"
    stx := .missing, metaSnap := .finished none { diagnostics := .empty }
    result? := none
  }
  let fatal ← observe "file:///snapshot-test.lean" 1 "".toFileMap root {}
  unless fatal.frontier == .fatal && fatal.commands.isEmpty do
    throw <| IO.userError "failed header must stop discovery"
  let processed : Language.Lean.HeaderProcessedSnapshot := {
    diagnostics := .empty, result? := none
    metaSnap := .finished none { diagnostics := .empty }
  }
  let _ : Nonempty Language.Lean.HeaderProcessedSnapshot := ⟨processed⟩
  let importing ← IO.Promise.new (α := Language.Lean.HeaderProcessedSnapshot)
  let root := { root with result? := some {
    parserState := default
    processedSnap := { stx? := none, cancelTk? := none, task := importing.result! }
  } }
  let waiting ← observe "file:///snapshot-test.lean" 1 "".toFileMap root {}
  unless waiting.frontier == .pending && waiting.commands.isEmpty do
    throw <| IO.userError "pending imports must not block the observer"
  importing.resolve processed
  let env ← mkEmptyEnvironment
  let pending ← IO.Promise.new (α := SnapshotLeaf)
  let cancel ← IO.CancelToken.new
  let child : SnapshotTree := { element := { desc := "unpositioned child", diagnostics := .empty }, children := #[] }
  let reporting : SnapshotTree := {
    element := { diagnostics := .empty }
    children := Array.replicate 300 (.finished none child)
  }
  let snap : Language.Lean.CommandElaboratingSnapshot := {
    diagnostics := .empty
    elabSnap := .finished none (.ofTyped (ForeignSnapshot.mk))
    resultSnap := .finished none {
      diagnostics := .empty
      cmdState := Elab.Command.mkState env {} {}
    }
    infoTreeSnap := { stx? := none, cancelTk? := some cancel, task := pending.result! }
    reportSnap := .finished none reporting
  }
  let (nodes, limited) ← observeCommand "".toFileMap { maxNodes? := some 8 } snap
  unless nodes.size == 8 && limited do
    throw <| IO.userError "node budget did not bound a broad tree"
  unless nodes[0]?.any (·.ready) && nodes[1]?.any (! ·.ready) do
    throw <| IO.userError "main return must not imply complete InfoTree"
  unless nodes[2]?.any (·.unsupported) do
    throw <| IO.userError "unknown snapshots must stay opaque"
  unless nodes.any (·.description == "unpositioned child") do
    throw <| IO.userError "unpositioned reporting tasks were omitted"
  unless !(← cancel.isSet) do
    throw <| IO.userError "observation cancelled elaboration"
  let (shallow, limited) ← observeCommand "".toFileMap { maxDepth? := some 0 } snap
  unless shallow.size == 4 && limited do
    throw <| IO.userError "depth budget did not stop expansion"
  let (one, limited) ← observeCommand "".toFileMap { maxNodes? := some 0 } snap
  unless one.size == 1 && limited do
    throw <| IO.userError "zero budget must clamp to one"
  pending.resolve { diagnostics := .empty }
  let (finished, _) ← observeCommand "".toFileMap {} snap
  unless finished[1]?.any (·.ready) do
    throw <| IO.userError "resolved child did not become available"
  let encoded := toJson nodes
  let decoded ← IO.ofExcept (fromJson? encoded : Except String (Array Node))
  unless (toJson decoded).compress == encoded.compress do
    throw <| IO.userError "snapshot payload did not round trip"
