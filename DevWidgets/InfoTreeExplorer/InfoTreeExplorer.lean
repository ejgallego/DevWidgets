/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import Lean.Data.Lsp
import Lean.Server
import Lean.Widget.UserWidget
-- import ProofWidgets.Component.Panel.Basic

namespace DevWidgets.InfoTreeExplorer

open Lean
open Lean Elab Command
open Lean.Server.FileWorker
open Lean Server Lsp RequestM
-- open ProofWidgets

structure ExplorerProps where
  title : String := "InfoTree Explorer"
  deriving Server.RpcEncodable

structure ExplorerCapture where
  summary : String := "No infotree summary captured yet. Move the cursor in a Lean file to populate this panel."
  tree : Option Json := none
  stxTree : Option Json := none
  deriving Inhabited, Server.RpcEncodable

initialize explorerCaptureRef : IO.Ref ExplorerCapture ← IO.mkRef {}

meta def stxContainsPos (stx : Syntax) (p : String.Pos.Raw) : Bool :=
  match stx.getRange? with
  | some r => r.start <= p && p < r.stop
  | none => false

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

meta def spaces : Nat → String
  | 0 => ""
  | n + 1 => " " ++ spaces n

meta def indent (depth : Nat) : String := spaces (2 * depth)

meta def formatRange (text : FileMap) (stx : Syntax) : String :=
  match stx.getRange? with
  | none => "unknown"
  | some r =>
    let lsp := text.utf8RangeToLspRange r
    s!"{lsp.start.line}:{lsp.start.character}..{lsp.end.line}:{lsp.end.character}"

meta def completionStx : Elab.CompletionInfo → Syntax
  | .dot termInfo _ => termInfo.stx
  | .id stx .. => stx
  | .dotId stx .. => stx
  | .fieldId stx .. => stx
  | .namespaceId stx => stx
  | .option stx => stx
  | .errorName stx _ => stx
  | .endSection stx .. => stx
  | .tactic stx => stx

meta def infoStx? : Elab.Info → Option Syntax
  | .ofTacticInfo i => some i.stx
  | .ofTermInfo i => some i.stx
  | .ofPartialTermInfo i => some i.stx
  | .ofCommandInfo i => some i.stx
  | .ofMacroExpansionInfo i => some i.stx
  | .ofOptionInfo i => some i.stx
  | .ofErrorNameInfo i => some i.stx
  | .ofFieldInfo i => some i.stx
  | .ofCompletionInfo i => some (completionStx i)
  | .ofUserWidgetInfo i => some i.stx
  | .ofCustomInfo i => some i.stx
  | .ofFVarAliasInfo _ => none
  | .ofFieldRedeclInfo i => some i.stx
  | .ofDelabTermInfo i => some i.stx
  | .ofChoiceInfo i => some i.stx
  | .ofDocInfo i => some i.stx
  | .ofDocElabInfo i => some i.stx

meta def infoContainsPos (info : Elab.Info) (pos : String.Pos.Raw) : Bool :=
  match infoStx? info with
  | some stx => stxContainsPos stx pos
  | none => false

meta def partialCtxTag : Elab.PartialContextInfo → String
  | .commandCtx _ => "commandCtx"
  | .parentDeclCtx parent => s!"parentDecl={parent}"
  | .autoImplicitCtx implicits => s!"autoImplicit={implicits.size}"

meta def infoNodeLabel (text : FileMap) (info : Elab.Info) : String :=
  let tag := infoTag info
  let kind :=
    match infoStx? info with
    | some stx => s!"{stx.getKind}"
    | none => "no-stx"
  let range :=
    match infoStx? info with
    | some stx => formatRange text stx
    | none => "unknown"
  let elaborator :=
    match info.toElabInfo? with
    | some i => s!" elab={i.elaborator}"
    | none => ""
  s!"{tag} [{kind}] @{range}{elaborator}"

meta def listMaxByLength (xs : List (List String)) : List String :=
  xs.foldl (init := []) fun best x =>
    if best.length < x.length then x else best

meta partial def pathToCursor (text : FileMap) (pos : String.Pos.Raw) : Elab.InfoTree → List String
  | .hole id => [s!"hole {id.name}"]
  | .context pc tree =>
    let child := pathToCursor text pos tree
    if child.isEmpty then [] else s!"context[{partialCtxTag pc}]" :: child
  | .node info children =>
    let childBest := listMaxByLength <| children.toList.map (pathToCursor text pos)
    if !childBest.isEmpty then
      infoNodeLabel text info :: childBest
    else if infoContainsPos info pos then
      [infoNodeLabel text info]
    else
      []

meta def focusedNodeDetail (text : FileMap) (info : Elab.Info) : String :=
  let header := infoNodeLabel text info
  let elaborator :=
    match info.toElabInfo? with
    | some i => s!" elaborator={i.elaborator}"
    | none => ""
  let extra :=
    match info with
    | .ofCustomInfo i => s!" customType={i.value.typeName}"
    | .ofDocElabInfo i => s!" docName={i.name} docKind={reprStr i.kind}"
    | .ofOptionInfo i => s!" option={i.optionName}"
    | .ofErrorNameInfo i => s!" errorName={i.errorName}"
    | .ofFieldInfo i => s!" field={i.fieldName}"
    | .ofUserWidgetInfo i => s!" widgetId={i.id}"
    | _ => ""
  s!"{header}{elaborator}{extra}"

meta def truncateStr (max : Nat) (s : String) : String :=
  if s.length <= max then s else (s.take max).toString ++ " ..."

meta def elaborationOutputPreview : Elab.Info → String
  | .ofTermInfo i => truncateStr 220 s!"term expr={reprStr i.expr}"
  | .ofPartialTermInfo i =>
    let exp := i.expectedType?.map reprStr |>.getD "none"
    truncateStr 220 s!"partial-term expectedType={exp}"
  | .ofCommandInfo i => s!"command stx={i.stx.getKind}"
  | .ofMacroExpansionInfo i =>
    s!"macro output={i.output.getKind} from={i.stx.getKind}"
  | .ofTacticInfo i =>
    s!"tactic goalsBefore={i.goalsBefore.length} goalsAfter={i.goalsAfter.length}"
  | .ofCompletionInfo _ => "completion candidate"
  | .ofCustomInfo i => s!"custom payloadType={i.value.typeName}"
  | .ofDocInfo i => s!"doc stx={i.stx.getKind}"
  | .ofDocElabInfo i => s!"doc-elab name={i.name} kind={reprStr i.kind}"
  | other => truncateStr 220 s!"{infoTag other}"

meta def renderContainmentPath (nodes : List String) : String :=
  let rec go (depth : Nat) : List String → List String
    | [] => []
    | n :: rest =>
      let line := s!"{indent depth}- {n}"
      line :: go (depth + 1) rest
  if nodes.isEmpty then
    "- _none_"
  else
    String.intercalate "\n" (go 0 nodes)

meta def takeMax (max : Nat) (xs : List α) : List α := xs.take max

meta def flattenLists (xss : List (List α)) : List α :=
  xss.foldr (· ++ ·) []

meta partial def focusedPathsWithInfo (text : FileMap) (pos : String.Pos.Raw) :
    Elab.InfoTree → List (Elab.Info × List String)
  | .hole _ => []
  | .context pc tree =>
    (focusedPathsWithInfo text pos tree).map fun (info, path) =>
      (info, s!"context[{partialCtxTag pc}]" :: path)
  | .node info children =>
    let childPaths :=
      flattenLists <| children.toList.map (focusedPathsWithInfo text pos)
    let childPaths :=
      childPaths.map fun (i, path) => (i, infoNodeLabel text info :: path)
    if !childPaths.isEmpty then
      childPaths
    else if infoContainsPos info pos then
      [(info, [infoNodeLabel text info])]
    else
      []

meta def treeJsonExt (label : String) (children : Array Json := #[]) (extra : List (String × Json) := []) : Json :=
  Json.mkObj <| [("label", Json.str label), ("children", Json.arr children)] ++ extra

meta def treeJson (label : String) (children : Array Json := #[]) : Json :=
  treeJsonExt label children

inductive CtxDiffMode where
  | lite
  | full

def ctxDiffModeDefault : CtxDiffMode := .lite

meta def short (max : Nat) (s : String) : String :=
  if s.length <= max then s else (s.take max).toString ++ "..."

meta def envStructuralFingerprint (env : Environment) : String :=
  s!"imports={env.allImportedModuleNames.size}, consts={env.constants.toList.length}"

meta def cmdEnvStructuralFingerprint (env? : Option Environment) : String :=
  match env? with
  | none => "none"
  | some env => envStructuralFingerprint env

meta def fileMapFingerprint (fm : FileMap) : String :=
  s!"bytes={fm.source.length}, hash={hash fm.source}"

meta def mctxFingerprint (mctx : MetavarContext) : String :=
  s!"depth={mctx.depth}, lDepth={mctx.levelAssignDepth}, mvarCtr={mctx.mvarCounter}, decls={mctx.decls.toList.length}, eAssign={mctx.eAssignment.toList.length}, lAssign={mctx.lAssignment.toList.length}, dAssign={mctx.dAssignment.toList.length}"

meta def optionsFingerprint (opts : Options) : String :=
  s!"hasTrace={opts.hasTrace}, hash={hash (toString opts)}"

meta def openDeclsFingerprint (ods : List OpenDecl) : String :=
  s!"count={ods.length}, hash={hash (String.intercalate "|" (ods.map toString))}"

meta def ngenFingerprint (ngen : NameGenerator) : String :=
  s!"prefix={ngen.namePrefix}, idx={ngen.idx}"

meta def commandCtxDiffFieldsLite (parent curr : Elab.CommandContextInfo) : List String := Id.run do
  let mut diffs : List String := []
  -- Keep this branch cheap: avoid expensive traversals / serialization.
  if parent.currNamespace != curr.currNamespace then
    diffs := s!"namespace {parent.currNamespace} -> {curr.currNamespace}" :: diffs
  if parent.env.allImportedModuleNames.size != curr.env.allImportedModuleNames.size then
    diffs := s!"env.imports {parent.env.allImportedModuleNames.size} -> {curr.env.allImportedModuleNames.size}" :: diffs
  if parent.cmdEnv?.isSome != curr.cmdEnv?.isSome then
    diffs := s!"cmdEnv? {parent.cmdEnv?.isSome} -> {curr.cmdEnv?.isSome}" :: diffs
  if parent.fileMap.source.length != curr.fileMap.source.length then
    diffs := s!"fileBytes {parent.fileMap.source.length} -> {curr.fileMap.source.length}" :: diffs
  if parent.mctx.depth != curr.mctx.depth then
    diffs := s!"mctx.depth {parent.mctx.depth} -> {curr.mctx.depth}" :: diffs
  if parent.mctx.levelAssignDepth != curr.mctx.levelAssignDepth then
    diffs := s!"mctx.levelAssignDepth {parent.mctx.levelAssignDepth} -> {curr.mctx.levelAssignDepth}" :: diffs
  if parent.mctx.mvarCounter != curr.mctx.mvarCounter then
    diffs := s!"mctx.mvarCounter {parent.mctx.mvarCounter} -> {curr.mctx.mvarCounter}" :: diffs
  if parent.options.hasTrace != curr.options.hasTrace then
    diffs := s!"options.hasTrace {parent.options.hasTrace} -> {curr.options.hasTrace}" :: diffs
  if parent.openDecls.length != curr.openDecls.length then
    diffs := s!"openDecls.length {parent.openDecls.length} -> {curr.openDecls.length}" :: diffs
  if parent.ngen.idx != curr.ngen.idx || parent.ngen.namePrefix != curr.ngen.namePrefix then
    diffs := s!"ngen {ngenFingerprint parent.ngen} -> {ngenFingerprint curr.ngen}" :: diffs
  diffs.reverse

meta def commandCtxDiffFieldsFull (parent curr : Elab.CommandContextInfo) : List String := Id.run do
  let mut diffs : List String := []
  if parent.currNamespace != curr.currNamespace then
    diffs := s!"namespace {parent.currNamespace} -> {curr.currNamespace}" :: diffs
  let pEnv := envStructuralFingerprint parent.env
  let cEnv := envStructuralFingerprint curr.env
  if pEnv != cEnv then
    diffs := s!"env {short 120 pEnv} -> {short 120 cEnv}" :: diffs
  let pCmdEnv := cmdEnvStructuralFingerprint parent.cmdEnv?
  let cCmdEnv := cmdEnvStructuralFingerprint curr.cmdEnv?
  if pCmdEnv != cCmdEnv then
    diffs := s!"cmdEnv? {short 120 pCmdEnv} -> {short 120 cCmdEnv}" :: diffs
  let pFM := fileMapFingerprint parent.fileMap
  let cFM := fileMapFingerprint curr.fileMap
  if pFM != cFM then
    diffs := s!"fileMap {pFM} -> {cFM}" :: diffs
  let pMctx := mctxFingerprint parent.mctx
  let cMctx := mctxFingerprint curr.mctx
  if pMctx != cMctx then
    diffs := s!"mctx {short 140 pMctx} -> {short 140 cMctx}" :: diffs
  let pOpts := optionsFingerprint parent.options
  let cOpts := optionsFingerprint curr.options
  if pOpts != cOpts then
    diffs := s!"options {pOpts} -> {cOpts}" :: diffs
  let pOpen := openDeclsFingerprint parent.openDecls
  let cOpen := openDeclsFingerprint curr.openDecls
  if parent.openDecls != curr.openDecls then
    diffs := s!"openDecls {pOpen} -> {cOpen}" :: diffs
  let pNgen := ngenFingerprint parent.ngen
  let cNgen := ngenFingerprint curr.ngen
  if pNgen != cNgen then
    diffs := s!"ngen {pNgen} -> {cNgen}" :: diffs
  diffs.reverse

meta def commandCtxDiffFields (mode : CtxDiffMode) (parent curr : Elab.CommandContextInfo) : List String :=
  match mode with
  | .lite => commandCtxDiffFieldsLite parent curr
  | .full => commandCtxDiffFieldsFull parent curr

structure CommandCtxDelta where
  changed : Bool
  summary : String
  tooltip : String := ""
  mainModuleChanged : Bool := false
deriving Inhabited

meta def commandCtxMainModuleDetails (parent curr : Elab.CommandContextInfo) : List String := Id.run do
  let mut details : List String := []
  if parent.env.mainModule != curr.env.mainModule then
    details := s!"env.mainModule: {parent.env.mainModule} -> {curr.env.mainModule}" :: details
  let pCmd := parent.cmdEnv?.map (·.mainModule)
  let cCmd := curr.cmdEnv?.map (·.mainModule)
  if pCmd != cCmd then
    details := s!"cmdEnv?.mainModule: {reprStr pCmd} -> {reprStr cCmd}" :: details
  details.reverse

meta def commandCtxDelta (parent? : Option Elab.CommandContextInfo) (curr : Elab.CommandContextInfo) : CommandCtxDelta :=
  match parent? with
  | none => { changed := false, summary := "no immediate ancestor", tooltip := "no immediate ancestor" }
  | some parent =>
    let mode := ctxDiffModeDefault
    let diffs := commandCtxDiffFields mode parent curr
    let mmDetails := commandCtxMainModuleDetails parent curr
    let mmChanged := !mmDetails.isEmpty
    if diffs.isEmpty then
      { changed := false, summary := "identical to immediate ancestor", tooltip := "identical to immediate ancestor" }
    else
      let modeTag := match mode with | .lite => "lite" | .full => "full"
      let summary :=
        if mmChanged then
          s!"changed [{modeTag}] (mainModule): {String.intercalate "; " diffs}"
        else
          s!"changed [{modeTag}]: {String.intercalate "; " diffs}"
      let tooltip :=
        if mmChanged then
          summary ++ "\n" ++ String.intercalate "\n" mmDetails
        else
          summary
      { changed := true, summary, tooltip, mainModuleChanged := mmChanged }

meta def stxLabel (text : FileMap) (stx : Syntax) : String :=
  let range := formatRange text stx
  match stx with
  | .node _ kind args => s!"syntax.node {kind} (children={args.size}) @{range}"
  | .atom _ val => s!"syntax.atom \"{truncateStr 40 val}\" @{range}"
  | .ident _ _ val _ => s!"syntax.ident {val} @{range}"
  | .missing => "syntax.missing"

meta partial def infoTreeToExplorerTree
    (text : FileMap)
    (maxChildren : Nat := 30)
    : Nat → Option Elab.CommandContextInfo → Elab.InfoTree → Json
  | _, _, .hole id =>
    treeJson s!"hole {id.name}"
  | depth, parentCommandCtx?, .context pc tree =>
    match pc with
    | .commandCtx ctx =>
      let delta := commandCtxDelta parentCommandCtx? ctx
      treeJsonExt
        s!"context[commandCtx] ({delta.summary})"
        #[infoTreeToExplorerTree text maxChildren (depth + 1) (some ctx) tree]
        [ ("nodeType", Json.str "commandCtx")
        , ("commandCtxChanged", Json.bool delta.changed)
        , ("commandCtxMainModuleChanged", Json.bool delta.mainModuleChanged)
        , ("commandCtxDiff", Json.str delta.tooltip)
        ]
    | .parentDeclCtx parentDecl =>
      treeJson s!"context[parentDecl={parentDecl}]"
        #[infoTreeToExplorerTree text maxChildren (depth + 1) parentCommandCtx? tree]
    | .autoImplicitCtx implicits =>
      treeJson s!"context[autoImplicit={implicits.size}]"
        #[infoTreeToExplorerTree text maxChildren (depth + 1) parentCommandCtx? tree]
  | depth, parentCommandCtx?, .node info children =>
    let renderedChildren :=
      children.toList.take maxChildren |>.map (infoTreeToExplorerTree text maxChildren (depth + 1) parentCommandCtx?)
    let childArray := renderedChildren.toArray
    let childArray :=
      if children.size > maxChildren then
        childArray.push <| treeJson s!"... ({children.size - maxChildren} more children)"
      else
        childArray
    treeJson (infoNodeLabel text info) childArray

meta partial def stxToExplorerTree
    (text : FileMap)
    (maxChildren : Nat := 40)
    : Nat → Syntax → Json
  | _depth, .missing =>
    treeJson "syntax.missing"
  | _depth, stx@(.atom ..) =>
    treeJson (stxLabel text stx)
  | _depth, stx@(.ident ..) =>
    treeJson (stxLabel text stx)
  | depth, stx@(.node _ _ args) =>
    let renderedChildren :=
      args.toList.take maxChildren |>.map (stxToExplorerTree text maxChildren (depth + 1))
    let childArray := renderedChildren.toArray
    let childArray :=
      if args.size > maxChildren then
        childArray.push <| treeJson s!"... ({args.size - maxChildren} more children)"
      else
        childArray
    treeJson (stxLabel text stx) childArray

meta def sampleForTag (text : FileMap) (tree : Elab.InfoTree) (tag : String) (max : Nat) : List String :=
  tree.foldInfo (init := []) fun _ctx info acc =>
    if infoTag info == tag && acc.length < max then
      acc ++ [infoNodeLabel text info]
    else
      acc

meta def captureSummaryText
    (text : FileMap)
    (uri : DocumentUri)
    (position : Lsp.Position)
    (snap : Lean.Server.Snapshots.Snapshot)
    (pos : String.Pos.Raw)
    : String :=
  let infoTree := Lean.Server.Snapshots.Snapshot.infoTree snap
  let infoNodeCount := infoTree.foldInfo (init := 0) fun _ctx _info n => n + 1
  let subtrees := rootSubtreeCount infoTree
  let tags := (infoTagSummary infoTree).toArray.qsort (fun a b => a.1 < b.1)
  let tagsSummary :=
    if tags.isEmpty then
      "_none_"
    else
      String.intercalate ", " <| tags.toList.map fun (tag, n) => s!"`{tag}`={n}"
  let path := pathToCursor text pos infoTree
  let pathStr := renderContainmentPath path
  let focused := takeMax 8 <| focusedPathsWithInfo text pos infoTree
  let focusedStr :=
    if focused.isEmpty then
      "- _none_"
    else
      let rec chains (i : Nat) : List (Elab.Info × List String) → List String
        | [] => []
        | (info, chainPath) :: rest =>
          let header := s!"- chain {i}"
          let pathLines := (renderContainmentPath chainPath).splitOn "\n"
          let details := s!"  detail: {focusedNodeDetail text info}"
          let output := s!"  output: {elaborationOutputPreview info}"
          header :: pathLines ++ [details, output] ++ chains (i + 1) rest
      String.intercalate "\n" (chains 1 focused)
  let heatmapRows :=
    tags.toList.map fun (tag, n) =>
      let samples := sampleForTag text infoTree tag 2
      let sampleTxt :=
        if samples.isEmpty then "no samples"
        else String.intercalate " | " samples
      s!"- `{tag}`: {n}  (samples: {sampleTxt})"
  let heatmapStr :=
    if heatmapRows.isEmpty then "- _none_"
    else String.intercalate "\n" heatmapRows
  let customAtPos : List Unit :=
    infoTree.deepestNodes fun _ctxt info _arr =>
      match info with
      | .ofCustomInfo ⟨stx, _data⟩ =>
        if stxContainsPos stx pos then some () else none
      | _ => none
  s!"**InfoTree Explorer**\n\n## Snapshot\n- uri: `{reprStr uri}`\n- cursor: `{position.line}:{position.character}`\n- syntax kind: `{snap.stx.getKind}`\n- end position (utf8): `{Lean.Server.Snapshots.Snapshot.endPos snap}`\n- module: `{(Lean.Server.Snapshots.Snapshot.env snap).mainModule}`\n- messages: `{(Lean.Server.Snapshots.Snapshot.msgLog snap).toArray.size}`\n- has errors: `{(Lean.Server.Snapshots.Snapshot.msgLog snap).hasErrors}`\n- infotree: root subtrees=`{subtrees}`, info nodes=`{infoNodeCount}`\n- infotree tags: {tagsSummary}\n- custom info nodes at cursor: `{customAtPos.length}`\n\n## Path To Cursor (outer -> inner)\n{pathStr}\n\n## Focused Nodes At Cursor (containment chains)\n{focusedStr}\n\n## Tag Heatmap + Samples\n{heatmapStr}"

meta def captureSummary
    (text : FileMap)
    (uri : DocumentUri)
    (position : Lsp.Position)
    (snap : Lean.Server.Snapshots.Snapshot)
    (pos : String.Pos.Raw)
    : ExplorerCapture :=
  let infoTree := Lean.Server.Snapshots.Snapshot.infoTree snap
  let summary := captureSummaryText text uri position snap pos
  let tree := infoTreeToExplorerTree text 30 0 none infoTree
  let stxTree := stxToExplorerTree text 40 0 snap.stx
  { summary, tree := some tree, stxTree := some stxTree }

meta def captureFromHover (params : HoverParams) : RequestM (RequestTask ExplorerCapture) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos params.position
  bindWaitFindSnap doc (·.endPos + ' ' >= pos)
    (notFoundX := do
      let summary := s!"**InfoTree Explorer**\n\n- status: `snapshot not found`\n- uri: `{reprStr params.textDocument.uri}`\n- cursor: `{params.position.line}:{params.position.character}`"
      pure <| .pure { summary }) fun snap => do
      let capture := captureSummary text params.textDocument.uri params.position snap pos
      pure <| .pure capture

meta def captureHoverHandler (params : HoverParams) (prev : RequestTask (Option Hover)) :
    RequestM (RequestTask (Option Hover)) := do
  let mine ← captureFromHover params
  RequestM.bindTaskCostly mine fun result =>
    match result with
    | Except.error _ => pure prev
    | Except.ok capture => do
      let _ ← (explorerCaptureRef.set capture : IO Unit)
      pure prev

meta initialize
  chainLspRequestHandler "textDocument/hover" HoverParams (Option Hover) captureHoverHandler

@[server_rpc_method]
def fetchInfoTreeSummary (_props : ExplorerProps) : RequestM (RequestTask ExplorerCapture) :=
  RequestM.asTask do
    return (← explorerCaptureRef.get)

@[widget_module]
def infoTreeExplorerWidget : Lean.Widget.Module where
  javascript := "
    import { RpcContext, mapRpcError } from '@leanprover/infoview'
    import * as React from 'react';

    const e = React.createElement;

    function styleForNode(node) {
      const label = node.label || '';
      const base = {
        display: 'inline-block',
        padding: '0.08rem 0.35rem',
        borderRadius: '4px',
        border: '1px solid var(--vscode-editorWidget-border)',
        fontFamily: 'var(--vscode-editor-font-family, monospace)',
        fontSize: '11px'
      };
      if (node.nodeType === 'commandCtx') {
        if (node.commandCtxChanged) {
          if (node.commandCtxMainModuleChanged) {
            return {
              ...base,
              background: 'rgba(220, 90, 90, 0.22)',
              border: '1px solid rgba(220, 90, 90, 0.6)',
              color: 'var(--vscode-editorError-foreground)'
            };
          }
          return {
            ...base,
            background: 'rgba(215, 140, 60, 0.22)',
            border: '1px solid rgba(215, 140, 60, 0.5)',
            color: 'var(--vscode-editorWarning-foreground)'
          };
        }
        return {
          ...base,
          background: 'rgba(110, 180, 130, 0.18)',
          color: 'var(--vscode-testing-iconPassed)'
        };
      }
      if (label.startsWith('context[')) {
        return { ...base, background: 'rgba(120, 140, 170, 0.18)', color: 'var(--vscode-symbolIcon-classForeground)' };
      }
      if (label.startsWith('tactic ')) {
        return { ...base, background: 'rgba(80, 180, 120, 0.18)', color: 'var(--vscode-symbolIcon-methodForeground)' };
      }
      if (label.startsWith('term ')) {
        return { ...base, background: 'rgba(90, 150, 210, 0.18)', color: 'var(--vscode-symbolIcon-variableForeground)' };
      }
      if (label.startsWith('command ')) {
        return { ...base, background: 'rgba(210, 150, 70, 0.18)', color: 'var(--vscode-symbolIcon-keywordForeground)' };
      }
      if (label.startsWith('custom ')) {
        return { ...base, background: 'rgba(190, 120, 210, 0.18)', color: 'var(--vscode-symbolIcon-operatorForeground)' };
      }
      if (label.startsWith('syntax.node ')) {
        return { ...base, background: 'rgba(100, 170, 220, 0.16)', color: 'var(--vscode-symbolIcon-moduleForeground)' };
      }
      if (label.startsWith('syntax.ident ')) {
        return { ...base, background: 'rgba(120, 200, 130, 0.16)', color: 'var(--vscode-symbolIcon-variableForeground)' };
      }
      if (label.startsWith('syntax.atom ')) {
        return { ...base, background: 'rgba(220, 170, 90, 0.16)', color: 'var(--vscode-symbolIcon-stringForeground)' };
      }
      return { ...base, background: 'rgba(128, 128, 128, 0.12)', color: 'var(--vscode-foreground)' };
    }

    function TreeNode({ node, depth, forceOpen }) {
      const kids = node.children || [];
      const tooltip = node.commandCtxDiff || null;
      if (kids.length === 0) {
        return e('li', { style: { margin: '0.08rem 0' } },
          e('span', { style: styleForNode(node), title: tooltip }, node.label)
        );
      }
      const open = forceOpen === null ? depth < 2 : forceOpen;
      return e('li', null,
        e('details', { open, style: { margin: '0.08rem 0' } },
          e('summary', { style: { cursor: 'pointer' } },
            e('span', { style: styleForNode(node), title: tooltip }, node.label)
          ),
          e('ul', { style: { marginLeft: '0.55rem', marginTop: '0.2rem', paddingLeft: '0.45rem' } },
            ...kids.map((child, i) => e(TreeNode, { node: child, depth: depth + 1, forceOpen, key: i }))
          )
        )
      );
    }

    function asciiTree(node, prefix = '') {
      const kids = node.children || [];
      const lines = [prefix + '- ' + node.label];
      for (const child of kids) {
        lines.push(...asciiTree(child, prefix + '  '));
      }
      return lines;
    }

    export default function (props) {
      const rs = React.useContext(RpcContext);
      const [payload, setPayload] = React.useState({
        summary: 'Waiting for snapshot data...',
        tree: null,
        stxTree: null
      });
      const [forceOpen, setForceOpen] = React.useState(null);
      const [showAscii, setShowAscii] = React.useState(false);

      const refresh = React.useCallback(() => {
        rs.call('DevWidgets.InfoTreeExplorer.fetchInfoTreeSummary', props)
          .then(setPayload)
          .catch(err => setPayload({
            summary: 'RPC error: ' + mapRpcError(err).message,
            tree: null,
            stxTree: null
          }));
      }, [rs, props]);

      React.useEffect(() => {
        refresh();
        const timer = setInterval(refresh, 1000);
        return () => clearInterval(timer);
      }, [refresh]);

      return e('details', { open: true, style: { marginTop: '0.5rem' } },
        e('summary', null, props.title),
        e('div', { style: { margin: '0.5rem 0' } },
          e('button', { onClick: refresh }, 'Refresh now')
        ),
        e('pre', {
          style: {
            whiteSpace: 'pre-wrap',
            fontFamily: 'var(--vscode-editor-font-family, monospace)',
            fontSize: '12px',
            lineHeight: '1.4',
            maxHeight: '32rem',
            overflow: 'auto',
            border: '1px solid var(--vscode-editorWidget-border)',
            padding: '0.5rem'
          }
        }, payload.summary),
        e('details', { open: true, style: { marginTop: '0.6rem' } },
          e('summary', null, 'Expandable Trees'),
          e('div', { style: { marginTop: '0.35rem', marginBottom: '0.25rem', display: 'flex', gap: '0.4rem' } },
            e('button', { onClick: () => setForceOpen(true) }, 'Expand all'),
            e('button', { onClick: () => setForceOpen(false) }, 'Collapse all'),
            e('button', { onClick: () => setForceOpen(null) }, 'Default'),
            e('button', { onClick: () => setShowAscii(!showAscii) }, showAscii ? 'Hide ASCII' : 'Show ASCII')
          ),
          e('div', { style: { display: 'flex', gap: '0.6rem', alignItems: 'flex-start', flexWrap: 'wrap' } },
            e('div', { style: { flex: '1 1 24rem', minWidth: '20rem' } },
              e('div', { style: { marginBottom: '0.25rem', fontWeight: '600' } }, 'InfoTree'),
              payload.tree
                ? e('ul', {
                    style: {
                      marginTop: '0.4rem',
                      paddingLeft: '0.65rem',
                      maxHeight: '36rem',
                      overflow: 'auto',
                      border: '1px solid var(--vscode-editorWidget-border)',
                      borderRadius: '6px',
                      background: 'var(--vscode-editor-background)',
                      paddingTop: '0.4rem',
                      paddingBottom: '0.4rem',
                      listStyle: 'none'
                    }
                  }, e(TreeNode, { node: payload.tree, depth: 0, forceOpen }))
                : e('div', { style: { marginTop: '0.4rem' } }, 'No InfoTree captured yet.')
            ),
            e('div', { style: { flex: '1 1 24rem', minWidth: '20rem' } },
              e('div', { style: { marginBottom: '0.25rem', fontWeight: '600' } }, 'Snapshot Syntax (stx)'),
              payload.stxTree
                ? e('ul', {
                    style: {
                      marginTop: '0.4rem',
                      paddingLeft: '0.65rem',
                      maxHeight: '36rem',
                      overflow: 'auto',
                      border: '1px solid var(--vscode-editorWidget-border)',
                      borderRadius: '6px',
                      background: 'var(--vscode-editor-background)',
                      paddingTop: '0.4rem',
                      paddingBottom: '0.4rem',
                      listStyle: 'none'
                    }
                  }, e(TreeNode, { node: payload.stxTree, depth: 0, forceOpen }))
                : e('div', { style: { marginTop: '0.4rem' } }, 'No snapshot syntax captured yet.')
            )
          ),
          showAscii && payload.tree
            ? e('pre', {
                style: {
                  marginTop: '0.5rem',
                  whiteSpace: 'pre',
                  fontFamily: 'var(--vscode-editor-font-family, monospace)',
                  fontSize: '11px',
                  lineHeight: '1.3',
                  maxHeight: '20rem',
                  overflow: 'auto',
                  border: '1px solid var(--vscode-editorWidget-border)',
                  borderRadius: '6px',
                  padding: '0.45rem',
                  background: 'var(--vscode-editor-background)'
                }
              }, asciiTree(payload.tree).join('\\n'))
            : null
        )
      );
    }
  "

syntax (name := infoTreeExplorerCmd) "#infotree_explorer" : command

@[command_elab infoTreeExplorerCmd]
def elabInfoTreeExplorer : CommandElab := fun
  | stx@`(#infotree_explorer) => do
    liftCoreM <| Widget.savePanelWidgetInfo
      infoTreeExplorerWidget.javascriptHash
      (rpcEncode ({ title := "InfoTree Explorer" } : ExplorerProps))
      stx
  | _ => throwUnsupportedSyntax

end DevWidgets.InfoTreeExplorer
