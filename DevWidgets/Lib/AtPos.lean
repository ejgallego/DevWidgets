/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Data.Lsp
public import Lean.Server.FileWorker.RequestHandling
public import Lean.Server.Rpc.RequestHandling
public section

namespace DevWidgets.Lib

open Lean Server Lsp RequestM

/-- Snapshot and cursor data resolved from a source position. -/
structure SnapshotAtPos where
  snap : Lean.Server.Snapshots.Snapshot
  text : FileMap
  utf8Pos : String.Pos.Raw

/--
Resolve the snapshot containing `pos`, and pass along the corresponding file map
and UTF-8 cursor position.
-/
def withSnapshotAtPos (pos : Lsp.Position)
    (k : SnapshotAtPos → RequestM α) : RequestM (RequestTask α) := do
  withWaitFindSnapAtPos pos fun snap => do
    let text := (← readDoc).meta.text
    k { snap, text, utf8Pos := text.lspPosToUtf8Pos pos }

end DevWidgets.Lib
