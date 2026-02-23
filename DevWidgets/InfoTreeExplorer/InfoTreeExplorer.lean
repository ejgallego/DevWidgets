/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import Lean.Data.Lsp
import Lean.Server
import Lean.Widget.UserWidget
import DevWidgets.Lib.AtPos
-- import ProofWidgets.Component.Panel.Basic

namespace DevWidgets.InfoTreeExplorer

open Lean
open Lean Elab
open Lean.Server.FileWorker
open Lean Server Lsp RequestM
-- open ProofWidgets

structure InfoTreeAtPosParams where
  pos : Lsp.Position
  uri? : Option DocumentUri := none
  deriving FromJson, ToJson

structure ExplorerCapture where
  summary : String := "No infotree summary captured yet. Move the cursor in a Lean file to populate this panel."
  tree : Option Json := none
  stxTree : Option Json := none
  facts : Array (String × String) := #[]
  cursorPath : Array String := #[]
  focused : Array String := #[]
  deriving Inhabited, Server.RpcEncodable

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

meta def infoStx? : Elab.Info → Option Syntax
  | .ofFVarAliasInfo _ => none
  | info => some info.stx

meta def infoContainsPos (info : Elab.Info) (pos : String.Pos.Raw) : Bool :=
  info.contains pos

meta def infoKindAndRange (text : FileMap) (info : Elab.Info) : String × String :=
  match infoStx? info with
  | some stx => (s!"{stx.getKind}", formatRange text stx)
  | none => ("no-stx", "unknown")

meta def partialCtxTag : Elab.PartialContextInfo → String
  | .commandCtx _ => "commandCtx"
  | .parentDeclCtx parent => s!"parentDecl={parent}"
  | .autoImplicitCtx implicits => s!"autoImplicit={implicits.size}"

meta def infoNodeLabel (text : FileMap) (info : Elab.Info) : String :=
  let tag := infoTag info
  let (kind, range) := infoKindAndRange text info
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

meta partial def focusedPathsWithInfo (text : FileMap) (pos : String.Pos.Raw) :
    Elab.InfoTree → List (Elab.Info × List String)
  | .hole _ => []
  | .context pc tree =>
    (focusedPathsWithInfo text pos tree).map fun (info, path) =>
      (info, s!"context[{partialCtxTag pc}]" :: path)
  | .node info children =>
    let childPaths :=
      (children.toList.map (focusedPathsWithInfo text pos)).foldr (· ++ ·) []
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
    : Option Elab.CommandContextInfo → Elab.InfoTree → Json
  | _, .hole id =>
    treeJson s!"hole {id.name}"
  | parentCommandCtx?, .context pc tree =>
    match pc with
    | .commandCtx ctx =>
      let delta := commandCtxDelta parentCommandCtx? ctx
      treeJsonExt
        s!"context[commandCtx] ({delta.summary})"
        #[infoTreeToExplorerTree text maxChildren (some ctx) tree]
        [ ("nodeType", Json.str "commandCtx")
        , ("commandCtxChanged", Json.bool delta.changed)
        , ("commandCtxMainModuleChanged", Json.bool delta.mainModuleChanged)
        , ("commandCtxDiff", Json.str delta.tooltip)
        ]
    | .parentDeclCtx parentDecl =>
      treeJson s!"context[parentDecl={parentDecl}]"
        #[infoTreeToExplorerTree text maxChildren parentCommandCtx? tree]
    | .autoImplicitCtx implicits =>
      treeJson s!"context[autoImplicit={implicits.size}]"
        #[infoTreeToExplorerTree text maxChildren parentCommandCtx? tree]
  | parentCommandCtx?, .node info children =>
    let renderedChildren :=
      children.toList.take maxChildren |>.map (infoTreeToExplorerTree text maxChildren parentCommandCtx?)
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
    : Syntax → Json
  | .missing =>
    treeJson "syntax.missing"
  | stx@(.atom ..) =>
    treeJson (stxLabel text stx)
  | stx@(.ident ..) =>
    treeJson (stxLabel text stx)
  | stx@(.node _ _ args) =>
    let renderedChildren :=
      args.toList.take maxChildren |>.map (stxToExplorerTree text maxChildren)
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

meta def renderTagSummary (tags : Array (String × Nat)) : String :=
  if tags.isEmpty then
    "_none_"
  else
    String.intercalate ", " <| tags.toList.map fun (tag, n) => s!"`{tag}`={n}"

meta def renderFocusedChains
    (text : FileMap)
    (focused : List (Elab.Info × List String))
    : String :=
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

meta def renderTagHeatmap
    (text : FileMap)
    (tree : Elab.InfoTree)
    (tags : Array (String × Nat))
    : String :=
  let heatmapRows :=
    tags.toList.map fun (tag, n) =>
      let samples := sampleForTag text tree tag 2
      let sampleTxt :=
        if samples.isEmpty then "no samples"
        else String.intercalate " | " samples
      s!"- `{tag}`: {n}  (samples: {sampleTxt})"
  if heatmapRows.isEmpty then "- _none_" else String.intercalate "\n" heatmapRows

meta def customInfoNodesAtPosCount (tree : Elab.InfoTree) (pos : String.Pos.Raw) : Nat :=
  let customAtPos : List Unit :=
    tree.deepestNodes fun _ctxt info _arr =>
      match info with
      | .ofCustomInfo ⟨stx, _data⟩ =>
        if stxContainsPos stx pos then some () else none
      | _ => none
  customAtPos.length

meta def focusedPreviewItems
    (text : FileMap)
    (focused : List (Elab.Info × List String))
    : Array String :=
  let rec go (i : Nat) : List (Elab.Info × List String) → List String
    | [] => []
    | (info, chainPath) :: rest =>
      let path := String.intercalate " > " chainPath
      let detail := focusedNodeDetail text info
      let output := elaborationOutputPreview info
      let item := s!"{i}. {detail}\n   path: {path}\n   output: {output}"
      item :: go (i + 1) rest
  (go 1 focused).toArray

meta def snapshotFacts
    (position : Lsp.Position)
    (snap : Lean.Server.Snapshots.Snapshot)
    (subtrees infoNodeCount tagKinds customAtPosCount : Nat)
    : Array (String × String) :=
  let env := Lean.Server.Snapshots.Snapshot.env snap
  let msgLog := Lean.Server.Snapshots.Snapshot.msgLog snap
  #[ ("Cursor", s!"{position.line + 1}:{position.character + 1}")
   , ("Module", toString env.mainModule)
   , ("Messages", toString msgLog.toArray.size)
   , ("Has errors", toString msgLog.hasErrors)
   , ("Info nodes", toString infoNodeCount)
   , ("Root subtrees", toString subtrees)
   , ("Tag kinds", toString tagKinds)
   , ("Custom nodes @ cursor", toString customAtPosCount)
   ]

meta def captureSummaryText
    (text : FileMap)
    (uri? : Option DocumentUri)
    (position : Lsp.Position)
    (snap : Lean.Server.Snapshots.Snapshot)
    (pos : String.Pos.Raw)
    : String :=
  let infoTree := Lean.Server.Snapshots.Snapshot.infoTree snap
  let infoNodeCount := infoTree.foldInfo (init := 0) fun _ctx _info n => n + 1
  let subtrees := rootSubtreeCount infoTree
  let tags := (infoTagSummary infoTree).toArray.qsort (fun a b => a.1 < b.1)
  let tagsSummary := renderTagSummary tags
  let path := pathToCursor text pos infoTree
  let pathStr := renderContainmentPath path
  let focused := (focusedPathsWithInfo text pos infoTree).take 8
  let focusedStr := renderFocusedChains text focused
  let heatmapStr := renderTagHeatmap text infoTree tags
  let customAtPosCount := customInfoNodesAtPosCount infoTree pos
  s!"**InfoTree Explorer**\n\n## Snapshot\n- uri: `{reprStr uri?}`\n- cursor: `{position.line}:{position.character}`\n- syntax kind: `{snap.stx.getKind}`\n- end position (utf8): `{Lean.Server.Snapshots.Snapshot.endPos snap}`\n- module: `{(Lean.Server.Snapshots.Snapshot.env snap).mainModule}`\n- messages: `{(Lean.Server.Snapshots.Snapshot.msgLog snap).toArray.size}`\n- has errors: `{(Lean.Server.Snapshots.Snapshot.msgLog snap).hasErrors}`\n- infotree: root subtrees=`{subtrees}`, info nodes=`{infoNodeCount}`\n- infotree tags: {tagsSummary}\n- custom info nodes at cursor: `{customAtPosCount}`\n\n## Path To Cursor (outer -> inner)\n{pathStr}\n\n## Focused Nodes At Cursor (containment chains)\n{focusedStr}\n\n## Tag Heatmap + Samples\n{heatmapStr}"

meta def captureSummary
    (text : FileMap)
    (uri? : Option DocumentUri)
    (position : Lsp.Position)
    (snap : Lean.Server.Snapshots.Snapshot)
    (pos : String.Pos.Raw)
    : ExplorerCapture :=
  let infoTree := Lean.Server.Snapshots.Snapshot.infoTree snap
  let infoNodeCount := infoTree.foldInfo (init := 0) fun _ctx _info n => n + 1
  let subtrees := rootSubtreeCount infoTree
  let tags := (infoTagSummary infoTree).toArray
  let path := pathToCursor text pos infoTree
  let focusedNodes := (focusedPathsWithInfo text pos infoTree).take 6
  let customAtPosCount := customInfoNodesAtPosCount infoTree pos
  let summary := captureSummaryText text uri? position snap pos
  let tree := infoTreeToExplorerTree text 30 none infoTree
  let stxTree := stxToExplorerTree text 40 snap.stx
  { summary
  , tree := some tree
  , stxTree := some stxTree
  , facts := snapshotFacts position snap subtrees infoNodeCount tags.size customAtPosCount
  , cursorPath := path.toArray
  , focused := focusedPreviewItems text focusedNodes
  }

private def infoTreeAtPosImpl (params : InfoTreeAtPosParams) : RequestM (RequestTask ExplorerCapture) := do
  DevWidgets.Lib.withSnapshotAtPos params.pos fun atPos => do
    return captureSummary atPos.text params.uri? params.pos atPos.snap atPos.utf8Pos

@[implemented_by infoTreeAtPosImpl]
meta opaque infoTreeAtPos (params : InfoTreeAtPosParams) : RequestM (RequestTask ExplorerCapture)

attribute [server_rpc_method] infoTreeAtPos

@[widget_module]
def infoTreeExplorerWidget : Lean.Widget.Module where
  javascript := "
    import { useAsync, useRpcSession, mapRpcError } from '@leanprover/infoview'
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
            return Object.assign({}, base, {
              background: 'rgba(220, 90, 90, 0.22)',
              border: '1px solid rgba(220, 90, 90, 0.6)',
              color: 'var(--vscode-editorError-foreground)'
            });
          }
          return Object.assign({}, base, {
            background: 'rgba(215, 140, 60, 0.22)',
            border: '1px solid rgba(215, 140, 60, 0.5)',
            color: 'var(--vscode-editorWarning-foreground)'
          });
        }
        return Object.assign({}, base, {
          background: 'rgba(110, 180, 130, 0.18)',
          color: 'var(--vscode-testing-iconPassed)'
        });
      }
      if (label.startsWith('context[')) {
        return Object.assign({}, base, { background: 'rgba(120, 140, 170, 0.18)', color: 'var(--vscode-symbolIcon-classForeground)' });
      }
      if (label.startsWith('tactic ')) {
        return Object.assign({}, base, { background: 'rgba(80, 180, 120, 0.18)', color: 'var(--vscode-symbolIcon-methodForeground)' });
      }
      if (label.startsWith('term ')) {
        return Object.assign({}, base, { background: 'rgba(90, 150, 210, 0.18)', color: 'var(--vscode-symbolIcon-variableForeground)' });
      }
      if (label.startsWith('command ')) {
        return Object.assign({}, base, { background: 'rgba(210, 150, 70, 0.18)', color: 'var(--vscode-symbolIcon-keywordForeground)' });
      }
      if (label.startsWith('custom ')) {
        return Object.assign({}, base, { background: 'rgba(190, 120, 210, 0.18)', color: 'var(--vscode-symbolIcon-operatorForeground)' });
      }
      if (label.startsWith('syntax.node ')) {
        return Object.assign({}, base, { background: 'rgba(100, 170, 220, 0.16)', color: 'var(--vscode-symbolIcon-moduleForeground)' });
      }
      if (label.startsWith('syntax.ident ')) {
        return Object.assign({}, base, { background: 'rgba(120, 200, 130, 0.16)', color: 'var(--vscode-symbolIcon-variableForeground)' });
      }
      if (label.startsWith('syntax.atom ')) {
        return Object.assign({}, base, { background: 'rgba(220, 170, 90, 0.16)', color: 'var(--vscode-symbolIcon-stringForeground)' });
      }
      return Object.assign({}, base, { background: 'rgba(128, 128, 128, 0.12)', color: 'var(--vscode-foreground)' });
    }

    function collectOpenPathKeys(root, labels) {
      const keys = new Set();
      if (!root || !Array.isArray(labels) || labels.length === 0) return keys;
      const matches = (treeLabel, pathLabel) => {
        if (treeLabel === pathLabel) return true;
        // commandCtx labels include a dynamic changed-suffix in the tree
        return typeof treeLabel === 'string' && treeLabel.startsWith(pathLabel + ' (');
      };
      const visit = (node, idx, pathKey) => {
        const label = node && typeof node.label === 'string' ? node.label : '';
        if (!matches(label, labels[idx])) return false;
        keys.add(pathKey);
        if (idx + 1 >= labels.length) return true;
        const kids = Array.isArray(node.children) ? node.children : [];
        for (let i = 0; i < kids.length; i++) {
          if (visit(kids[i], idx + 1, pathKey + '.' + i)) return true;
        }
        keys.delete(pathKey);
        return false;
      };
      visit(root, 0, 'r');
      return keys;
    }

    function collectFocusedPathCounts(root, focusedEntries) {
      const counts = new Map();
      if (!root || !Array.isArray(focusedEntries)) return counts;
      for (const entry of focusedEntries) {
        if (!entry || typeof entry.path !== 'string' || entry.path === '') continue;
        const labels = entry.path.split(' > ').map(s => s.trim()).filter(Boolean);
        if (labels.length === 0) continue;
        const keys = collectOpenPathKeys(root, labels);
        for (const k of keys) {
          counts.set(k, (counts.get(k) || 0) + 1);
        }
      }
      return counts;
    }

    function TreeNode({ node, depth, forceOpen, autoOpenKeys, pathKey, focusedPathCounts, highlightFocused }) {
      const kids = node.children || [];
      const tooltip = node.commandCtxDiff || null;
      const focusCount = focusedPathCounts.get(pathKey) || 0;
      const nodeStyle = Object.assign(
        {},
        styleForNode(node),
        highlightFocused && focusCount > 0
          ? {
              boxShadow: 'inset 0 0 0 1px rgba(90, 150, 210, 0.85)',
              background: 'rgba(70, 140, 210, 0.24)'
            }
          : {}
      );
      if (kids.length === 0) {
        return e('li', { style: { margin: '0.08rem 0' } },
          e('span', { style: nodeStyle, title: tooltip }, node.label),
          highlightFocused && focusCount > 0
            ? e('span', {
                style: {
                  marginLeft: '0.3rem',
                  border: '1px solid var(--vscode-editorWidget-border)',
                  borderRadius: '999px',
                  padding: '0.02rem 0.28rem',
                  fontSize: '0.64rem',
                  color: 'var(--vscode-descriptionForeground)'
                }
              }, 'focus x' + focusCount)
            : null
        );
      }
      const open = forceOpen === null ? (depth === 0 || autoOpenKeys.has(pathKey)) : forceOpen;
      return e('li', null,
        e('details', { open, style: { margin: '0.08rem 0' } },
          e('summary', { style: { cursor: 'pointer' } },
            e('span', { style: nodeStyle, title: tooltip }, node.label),
            highlightFocused && focusCount > 0
              ? e('span', {
                  style: {
                    marginLeft: '0.3rem',
                    border: '1px solid var(--vscode-editorWidget-border)',
                    borderRadius: '999px',
                    padding: '0.02rem 0.28rem',
                    fontSize: '0.64rem',
                    color: 'var(--vscode-descriptionForeground)'
                  }
                }, 'focus x' + focusCount)
              : null
          ),
          e('ul', { style: { marginLeft: '0.55rem', marginTop: '0.2rem', paddingLeft: '0.45rem' } },
            kids.map((child, i) => e(TreeNode, {
              node: child,
              depth: depth + 1,
              forceOpen,
              autoOpenKeys,
              pathKey: pathKey + '.' + i,
              focusedPathCounts,
              highlightFocused,
              key: i
            }))
          )
        )
      );
    }

    function asciiTree(node, prefix = '') {
      const kids = node.children || [];
      const lines = [prefix + '- ' + node.label];
      for (const child of kids) {
        lines.push.apply(lines, asciiTree(child, prefix + '  '));
      }
      return lines;
    }

    function parseFocusedItem(item) {
      if (typeof item !== 'string') return null;
      const lines = item.split('\\n').map(s => s.trim()).filter(Boolean);
      if (lines.length === 0) return null;
      const title = lines[0];
      let path = '';
      let output = '';
      for (const line of lines.slice(1)) {
        if (line.startsWith('path: ')) path = line.slice(6);
        if (line.startsWith('output: ')) output = line.slice(8);
      }
      return { title, path, output };
    }

    export default function (props) {
      const rs = useRpcSession();
      const [forceOpen, setForceOpen] = React.useState(null);

      const capture = useAsync(async () => {
        if (!props?.pos) {
          return {
            summary: 'No cursor position available yet.',
            tree: null,
            stxTree: null
          };
        }
        const params = { pos: props.pos, 'uri?': props?.pos?.uri ?? null };
        return await rs.call('DevWidgets.InfoTreeExplorer.infoTreeAtPos', params);
      }, [rs, props?.pos?.uri, props?.pos?.line, props?.pos?.character]);

      const payload =
        capture.state === 'resolved' && capture.value
          ? capture.value
          : capture.state === 'rejected'
            ? { summary: 'RPC error: ' + mapRpcError(capture.error).message, tree: null, stxTree: null, facts: [], cursorPath: [], focused: [] }
            : { summary: 'Waiting for snapshot data...', tree: null, stxTree: null, facts: [], cursorPath: [], focused: [] };
      const facts = Array.isArray(payload.facts) ? payload.facts : [];
      const cursorPath = Array.isArray(payload.cursorPath) ? payload.cursorPath : [];
      const focused = Array.isArray(payload.focused) ? payload.focused : [];
      const parsedFocused = React.useMemo(
        () => focused.map(parseFocusedItem).filter(x => x !== null),
        [focused]
      );
      const focusedHitsByLabel = React.useMemo(() => {
        const m = new Map();
        for (const f of parsedFocused) {
          if (!f || !f.path) continue;
          for (const seg of f.path.split(' > ')) {
            const key = seg.trim();
            if (key === '') continue;
            m.set(key, (m.get(key) || 0) + 1);
          }
        }
        return m;
      }, [parsedFocused]);

      const boxStyle = {
        marginTop: '0.35rem',
        paddingLeft: '0.65rem',
        maxHeight: '36rem',
        overflow: 'auto',
        border: '1px solid var(--vscode-editorWidget-border)',
        borderRadius: '8px',
        background: 'var(--vscode-editor-background)',
        paddingTop: '0.45rem',
        paddingBottom: '0.45rem',
        listStyle: 'none'
      };
      const cursorLabel = props?.pos
        ? 'L' + (props.pos.line + 1) + ':' + (props.pos.character + 1)
        : 'cursor unknown';
      const factMap = Object.fromEntries(facts.map(pair => [pair[0], pair[1]]));
      const headerChips = [
        ['cursor', cursorLabel],
        ['module', factMap['Module']],
        ['nodes', factMap['Info nodes']],
        ['subtrees', factMap['Root subtrees']],
        ['tags', factMap['Tag kinds']],
        ['custom', factMap['Custom nodes @ cursor']],
        ['msgs', factMap['Messages']],
        ['errors', factMap['Has errors']]
      ].filter((pair) => pair[1] !== undefined && pair[1] !== null && pair[1] !== '');
      const highlightFocused = parsedFocused.length > 2;
      const focusedPathCounts = React.useMemo(
        () => collectFocusedPathCounts(payload.tree, parsedFocused),
        [payload.tree, parsedFocused]
      );
      const autoOpenKeys = React.useMemo(
        () => {
          const keys = collectOpenPathKeys(payload.tree, cursorPath);
          if (highlightFocused) {
            for (const k of focusedPathCounts.keys()) keys.add(k);
          }
          return keys;
        },
        [payload.tree, cursorPath, highlightFocused, focusedPathCounts]
      );

      return e('details', { open: true, style: { marginTop: '0.5rem' } },
        e('summary', null, 'InfoTree Explorer'),
        e('div', {
          style: {
            marginTop: '0.42rem',
            marginBottom: '0.35rem',
            display: 'flex',
            alignItems: 'center',
            gap: '0.3rem',
            whiteSpace: 'nowrap',
            overflowX: 'auto',
            paddingBottom: '0.08rem'
          }
        },
          e('span', {
            style: {
              fontWeight: '700',
              letterSpacing: '0.02em',
              marginRight: '0.15rem'
            }
          }, 'Explorer'),
          ...headerChips.map((pair, i) =>
            e('span', {
              key: i,
              style: {
                border: '1px solid var(--vscode-editorWidget-border)',
                borderRadius: '999px',
                padding: '0.08rem 0.42rem',
                background: pair[0] === 'errors' && String(pair[1]) === 'true'
                  ? 'rgba(220, 90, 90, 0.2)'
                  : 'var(--vscode-editor-background)',
                fontSize: '0.74rem',
                lineHeight: '1.2'
              }
            }, pair[0] + ': ' + pair[1])
          )
        ),
        e('details', { open: true, style: { marginTop: '0.5rem' } },
          e('summary', { style: { fontWeight: '600', cursor: 'pointer' } }, 'Path to Cursor'),
          cursorPath.length > 0
            ? e('ul', {
                style: {
                  marginTop: '0.32rem',
                  marginBottom: '0.35rem',
                  paddingLeft: '0.2rem',
                  listStyle: 'none'
                }
              },
              ...cursorPath.map((item, i) =>
                e('li', {
                  key: i,
                  style: {
                    display: 'flex',
                    alignItems: 'flex-start',
                    gap: '0.38rem',
                    margin: '0.13rem 0',
                    paddingLeft: (0.08 + i * 0.32) + 'rem'
                  }
                },
                  e('span', {
                    style: {
                      width: '1rem',
                      color: 'var(--vscode-descriptionForeground)',
                      fontFamily: 'var(--vscode-editor-font-family, monospace)',
                      fontSize: '0.75rem',
                      paddingTop: '0.12rem',
                      textAlign: 'center'
                    }
                  }, i + 1 === cursorPath.length ? '└' : '├'),
                  e('span', {
                    style: Object.assign({}, styleForNode({ label: item }), {
                      whiteSpace: 'normal',
                      padding: '0.05rem 0.3rem'
                    })
                  }, item),
                  focusedHitsByLabel.get(item)
                    ? e('span', {
                        style: {
                          border: '1px solid var(--vscode-editorWidget-border)',
                          borderRadius: '999px',
                          padding: '0.05rem 0.28rem',
                          fontSize: '0.66rem',
                          color: 'var(--vscode-descriptionForeground)',
                          marginTop: '0.1rem'
                        }
                      }, 'focus x' + focusedHitsByLabel.get(item))
                    : null
                  )
              )
            )
            : e('div', { style: { marginTop: '0.4rem', color: 'var(--vscode-descriptionForeground)' } }, 'No cursor path captured.'),
          parsedFocused.length > 0
            ? e('div', { style: { marginTop: '0.3rem' } },
                e('div', {
                  style: {
                    fontWeight: '600',
                    marginBottom: '0.2rem',
                    fontSize: '0.78rem',
                    color: 'var(--vscode-descriptionForeground)'
                  }
                }, 'Focused preview in path context'),
                e('div', {
                  style: {
                    display: 'grid',
                    gap: '0.22rem'
                  }
                },
                ...parsedFocused.slice(0, 3).map((f, i) =>
                  e('div', {
                    key: i,
                    style: {
                      border: '1px solid var(--vscode-editorWidget-border)',
                      borderRadius: '7px',
                      padding: '0.2rem 0.35rem',
                      background: 'var(--vscode-editor-background)'
                    }
                  },
                    e('div', { style: { fontSize: '0.74rem', fontWeight: '600' } }, f.title),
                    f.output
                      ? e('div', {
                          style: {
                            marginTop: '0.12rem',
                            fontSize: '0.72rem',
                            color: 'var(--vscode-descriptionForeground)',
                            whiteSpace: 'nowrap',
                            overflow: 'hidden',
                            textOverflow: 'ellipsis'
                          }
                        }, f.output)
                      : null
                  )
                ))
              )
            : null,
          focused.length > 0
            ? e('details', { open: false, style: { marginTop: '0.32rem' } },
                e('summary', { style: { cursor: 'pointer' } }, 'Focused details (' + focused.length + ')'),
                parsedFocused.length > 0
                  ? e('div', {
                      style: {
                        marginTop: '0.22rem',
                        display: 'grid',
                        gap: '0.3rem'
                      }
                    },
                    parsedFocused.map((f, i) =>
                      e('div', {
                        key: i,
                        style: {
                          border: '1px solid var(--vscode-editorWidget-border)',
                          borderRadius: '8px',
                          padding: '0.28rem 0.4rem',
                          background: 'var(--vscode-editor-background)'
                        }
                      },
                        e('div', { style: { fontSize: '0.75rem', fontWeight: '700' } }, f.title),
                        f.path
                          ? e('div', {
                              style: {
                                marginTop: '0.12rem',
                                fontSize: '0.71rem',
                                color: 'var(--vscode-descriptionForeground)',
                                whiteSpace: 'pre-wrap'
                              }
                            }, 'path: ' + f.path)
                          : null,
                        f.output
                          ? e('div', {
                              style: {
                                marginTop: '0.12rem',
                                fontSize: '0.71rem',
                                color: 'var(--vscode-descriptionForeground)',
                                whiteSpace: 'pre-wrap'
                              }
                            }, 'output: ' + f.output)
                          : null
                      )
                    ),
                    e('details', { open: false, style: { marginTop: '0.2rem' } },
                      e('summary', { style: { cursor: 'pointer', fontSize: '0.74rem' } }, 'Raw focused entries'),
                      e('ul', {
                        style: {
                          marginTop: '0.22rem',
                          paddingLeft: '1rem',
                          whiteSpace: 'pre-wrap',
                          lineHeight: '1.3'
                        }
                      }, focused.map((item, i) => e('li', { key: i, style: { marginBottom: '0.35rem' } }, item)))
                    )
                  )
                  : e('ul', {
                      style: {
                        marginTop: '0.22rem',
                        paddingLeft: '1rem',
                        whiteSpace: 'pre-wrap',
                        lineHeight: '1.3'
                      }
                    }, focused.map((item, i) => e('li', { key: i, style: { marginBottom: '0.35rem' } }, item)))
              )
            : null
        ),
        e('div', { style: { marginTop: '0.2rem', marginBottom: '0.5rem', display: 'flex', gap: '0.4rem', flexWrap: 'wrap' } },
          e('button', { onClick: () => setForceOpen(true) }, 'Expand all'),
          e('button', { onClick: () => setForceOpen(false) }, 'Collapse all'),
          e('button', { onClick: () => setForceOpen(null) }, 'Focus path')
        ),
        e('details', { open: true, style: { marginTop: '0.4rem' } },
          e('summary', { style: { fontWeight: '600', cursor: 'pointer' } }, 'InfoTree'),
          payload.tree
            ? e('ul', { style: boxStyle }, e(TreeNode, {
                node: payload.tree,
                depth: 0,
                forceOpen,
                autoOpenKeys,
                pathKey: 'r',
                focusedPathCounts,
                highlightFocused
              }))
            : e('div', { style: { marginTop: '0.45rem' } }, 'No InfoTree captured yet.')
        ),
        e('details', { open: false, style: { marginTop: '0.55rem' } },
          e('summary', { style: { fontWeight: '600', cursor: 'pointer' } }, 'Snapshot Syntax (stx)'),
          payload.stxTree
            ? e('ul', { style: boxStyle }, e(TreeNode, {
                node: payload.stxTree,
                depth: 0,
                forceOpen,
                autoOpenKeys: new Set(),
                pathKey: 'r',
                focusedPathCounts: new Map(),
                highlightFocused: false
              }))
            : e('div', { style: { marginTop: '0.45rem' } }, 'No snapshot syntax captured yet.')
        ),
        e('details', { open: false, style: { marginTop: '0.55rem' } },
          e('summary', { style: { fontWeight: '600', cursor: 'pointer' } }, 'ASCII Tree'),
          payload.tree
            ? e('pre', {
                style: {
                  marginTop: '0.45rem',
                  whiteSpace: 'pre',
                  fontFamily: 'var(--vscode-editor-font-family, monospace)',
                  fontSize: '11px',
                  lineHeight: '1.35',
                  maxHeight: '20rem',
                  overflow: 'auto',
                  border: '1px solid var(--vscode-editorWidget-border)',
                  borderRadius: '8px',
                  padding: '0.45rem',
                  background: 'var(--vscode-editor-background)'
                }
              }, asciiTree(payload.tree).join('\\n'))
            : e('div', { style: { marginTop: '0.45rem' } }, 'No InfoTree captured yet.')
        )
      );
    }
  "

end DevWidgets.InfoTreeExplorer
