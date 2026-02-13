/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean.Data.Lsp
import Lean.Server

namespace DevWidgets.DHover

open Lean
open Lean.Server.FileWorker
open Lean Server Lsp RequestM

meta def mkHover (msg : String) (range? : Option Lsp.Range := none) : Hover := {
  contents := { kind := .markdown, value := msg }
  range?
}

meta def stxContainsPos (stx : Syntax) (p : String.Pos.Raw) : Bool :=
  match stx.getRange? with
  | some r => r.start <= p && p < r.stop
  | none => false

meta def stxLspRange? (text : FileMap) (stx : Syntax) : Option Lsp.Range :=
  stx.getRange?.map text.utf8RangeToLspRange

meta partial def rootSubtreeCount : Elab.InfoTree → Nat
  | .context _ t => rootSubtreeCount t
  | .node _ children => children.size
  | .hole _ => 0

meta def infoTag (info : Elab.Info) : String :=
  match info with
  | .ofTacticInfo _ => "tactic"
  | .ofTermInfo _ => "term"
  | .ofPartialTermInfo _ => "partialTerm"
  | .ofCommandInfo _ => "command"
  | .ofMacroExpansionInfo _ => "macroExpansion"
  | .ofOptionInfo _ => "option"
  | .ofErrorNameInfo _ => "errorName"
  | .ofFieldInfo _ => "field"
  | .ofCompletionInfo _ => "completion"
  | .ofUserWidgetInfo _ => "userWidget"
  | .ofCustomInfo _ => "custom"
  | .ofFVarAliasInfo _ => "fvarAlias"
  | .ofFieldRedeclInfo _ => "fieldRedecl"
  | .ofDelabTermInfo _ => "delabTerm"
  | .ofChoiceInfo _ => "choice"
  | .ofDocInfo _ => "doc"
  | .ofDocElabInfo _ => "docElab"

meta def bumpTagCount (tag : String) (counts : List (String × Nat)) : List (String × Nat) :=
  match counts with
  | [] => [(tag, 1)]
  | (tag', n) :: rest =>
    if tag == tag' then
      (tag', n + 1) :: rest
    else
      (tag', n) :: bumpTagCount tag rest

meta def infoTagSummary (tree : Elab.InfoTree) : List (String × Nat) :=
  tree.foldInfo (init := []) fun _ctx info acc =>
    bumpTagCount (infoTag info) acc

meta def formatRange (r : Lsp.Range) : String :=
  s!"{r.start.line}:{r.start.character}..{r.end.line}:{r.end.character}"

structure ContextMatch where
  depth : Nat
  ctx : Elab.ContextInfo
  info : Elab.Info

structure InfoStats where
  infoNodeCount : Nat := 0
  tags : List (String × Nat) := []

meta def contextSummary (ctx : Elab.ContextInfo) : String :=
  s!"module=`{ctx.env.mainModule}`, namespace=`{ctx.currNamespace}`, parentDecl=`{ctx.parentDecl?.getD .anonymous}`, openDecls={ctx.openDecls.length}, autoImplicits={ctx.autoImplicits.size}"

meta def contextMatchSummary (text : FileMap) (m : ContextMatch) : String :=
  let range? := stxLspRange? text m.info.stx
  s!"depth={m.depth}, tag=`{infoTag m.info}`, stxKind=`{m.info.stx.getKind}`, range={range?.map formatRange |>.getD "unknown"}, {contextSummary m.ctx}"

meta partial def contextMatchesAtPos
    (tree : Elab.InfoTree) (pos : String.Pos.Raw)
    (ctx? : Option Elab.ContextInfo := none) (depth : Nat := 0) (acc : Array ContextMatch := #[]) :
    Array ContextMatch :=
  match tree with
  | .hole _ => acc
  | .context inner t =>
    contextMatchesAtPos t pos (inner.mergeIntoOuter? ctx?) depth acc
  | .node info children =>
    let acc :=
      match ctx? with
      | some ctx =>
        if stxContainsPos info.stx pos then acc.push {depth, ctx, info} else acc
      | none => acc
    let ctx' := info.updateContext? ctx?
    children.foldl
      (init := acc)
      (fun acc child => contextMatchesAtPos child pos ctx' (depth + 1) acc)

meta def snapshotSummary (text : FileMap) (snap : Lean.Server.Snapshots.Snapshot) (pos : String.Pos.Raw) : String := Id.run do
  let infoTree := Lean.Server.Snapshots.Snapshot.infoTree snap
  let snapRange? := stxLspRange? text snap.stx
  let stats : InfoStats := infoTree.foldInfo (init := {}) fun _ctx info st =>
    { infoNodeCount := st.infoNodeCount + 1, tags := bumpTagCount (infoTag info) st.tags }
  let subtrees := rootSubtreeCount infoTree
  let tags := stats.tags.toArray.qsort (fun a b => a.1 < b.1)
  let tagsSummary :=
    if tags.isEmpty then
      "_none_"
    else
      String.intercalate ", " (tags.toList.map (fun p => s!"`{p.1}`={p.2}"))
  let ctxMatches := contextMatchesAtPos infoTree pos
  let outerCtx :=
    ctxMatches.foldl (init := none) fun best? m =>
      match best? with
      | none => some m
      | some best => if m.depth < best.depth then some m else best?
  let innerCtx :=
    ctxMatches.foldl (init := none) fun best? m =>
      match best? with
      | none => some m
      | some best => if m.depth > best.depth then some m else best?
  let outerSummary := outerCtx.map (contextMatchSummary text ·) |>.getD "_none_"
  let innerSummary := innerCtx.map (contextMatchSummary text ·) |>.getD "_none_"
  let customInfoNodesAtPos :=
    ctxMatches.foldl (init := 0) fun n m =>
      match m.info with
      | .ofCustomInfo _ => n + 1
      | _ => n
  let msgLog := Lean.Server.Snapshots.Snapshot.msgLog snap
  let hasErrors := msgLog.hasErrors
  let hasErrorsStr := toString hasErrors
  let snapshotRange := snapRange?.map formatRange |>.getD "unknown"
  let endPos := toString (Lean.Server.Snapshots.Snapshot.endPos snap)
  let moduleName := toString (Lean.Server.Snapshots.Snapshot.env snap).mainModule
  let messageCount := toString msgLog.toArray.size
  let infotreeSummary := s!"root subtrees={subtrees}, info nodes={stats.infoNodeCount}"
  let stxKind := toString snap.stx.getKind
  return s!"**VersoBlueprint Snapshot**
`status=found` | `errors={hasErrorsStr}` | `custom@cursor={customInfoNodesAtPos}`

- `syntax kind`: `{stxKind}`
- `snapshot range (lsp)`: `{snapshotRange}`
- `end position (utf8)`: `{endPos}`
- `module`: `{moduleName}`
- `messages`: `{messageCount}`
- `infotree`: `{infotreeSummary}`
- `infotree tags`: {tagsSummary}
- `outer context`: {outerSummary}
- `innermost context`: {innerSummary}"

meta def snapshotHover (params : HoverParams) : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos)
    (notFoundX := pure <| .pure <| some <| mkHover "**VersoBlueprint Snapshot**\n\n`status=not found`") fun snap => do
      let range? := stxLspRange? text snap.stx
      pure <| .pure <| some <| mkHover (snapshotSummary text snap pos) range?

meta def mergeHover (mine prev : Option Hover) : Option Hover :=
  match mine, prev with
  | none, h => h
  | h, none => h
  | some mine, some prev =>
    some {
      contents := {
        kind := .markdown
        value := s!"{mine.contents.value}\n\n---\n\n{prev.contents.value}"
      }
      range? := mine.range? <|> prev.range?
    }

meta def mergeRequestTasks (mine prev : RequestTask (Option Hover)) :
    RequestM (RequestTask (Option Hover)) := do
  pure <| mine.bindCostly fun
    | .error _ => prev
    | .ok mine =>
      prev.bindCostly fun
        | .error _ => .mk <| .pure <| pure mine
        | .ok prev => .mk <| .pure <| pure <| mergeHover mine prev

meta def handleHover (params : HoverParams) (prev : RequestTask (Option Hover)) :
    RequestM (RequestTask (Option Hover)) := do
  mergeRequestTasks (← snapshotHover params) prev

meta initialize
  chainLspRequestHandler "textDocument/hover" HoverParams (Option Hover) handleHover

end DevWidgets.DHover
