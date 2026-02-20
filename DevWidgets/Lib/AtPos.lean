/- 
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Data.Lsp
public import Lean.Elab.InfoTree
public import Lean.Server.FileWorker.RequestHandling
public import Lean.Server.Rpc.RequestHandling
public section

namespace DevWidgets.Lib

open Lean Elab Server Lsp RequestM

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

/-- Constant-under-cursor information resolved from the current info-tree. -/
structure ConstAtPos where
  snap : Lean.Server.Snapshots.Snapshot
  text : FileMap
  utf8Pos : String.Pos.Raw
  info : Elab.InfoWithCtx
  declName : Name
  /--
  Environment used for follow-up analysis:
  * `global = false` => local elaboration environment at the cursor (`info.ctx.env`)
  * `global = true`  => snapshot/global environment (`snap.env`)
  -/
  env : Environment

/-- Extract a constant name from hover info. -/
def constNameAtInfo? (info : Elab.Info) : Option Name :=
  match info with
  | .ofTermInfo ti => ti.expr.getAppFn.constName?
  | .ofDelabTermInfo ti => ti.toTermInfo.expr.getAppFn.constName?
  | .ofFieldInfo fi => some fi.projName
  | _ => none

/--
Resolve declaration info at cursor and pass it to `k`.
If `global = true`, analysis uses `snap.env`; otherwise it uses `info.ctx.env`.
-/
def withConstAtPos (pos : Lsp.Position) (global : Bool := false)
    (k : Option ConstAtPos → RequestM α) : RequestM (RequestTask α) := do
  withSnapshotAtPos pos fun atPos => do
    let info? := atPos.snap.infoTree.hoverableInfoAtM? (m := Id) atPos.utf8Pos (includeStop := true)
    let constAt? := info?.bind fun info =>
      (constNameAtInfo? info.info).map fun declName =>
        let env := if global then atPos.snap.env else info.ctx.env
        { snap := atPos.snap
          text := atPos.text
          utf8Pos := atPos.utf8Pos
          info := info
          declName := declName
          env := env }
    k constAt?

end DevWidgets.Lib
