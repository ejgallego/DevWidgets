/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

import Lean
import DevWidgets.Lib.Panel
import Lean.Data.Lsp
import Lean.Server
import Lean.Widget.UserWidget
import DevWidgets.Lib.AtPos

namespace DevWidgets.InfoTreeExplorer

open Lean
open Lean Elab
open Lean.Server.FileWorker
open Lean Server Lsp RequestM

structure InfoTreeAtPosParams where
  pos : Lsp.Position
  maxChildren? : Option Nat := none
  maxDepth? : Option Nat := none
  maxNodes? : Option Nat := none
  deriving FromJson, ToJson

/-- Limits for inspection and rendering. These do not change Lean's elaboration info collection. -/
structure Config where
  maxChildren : Nat := 30
  maxDepth : Nat := 32
  /-- Maximum nodes inspected per tree, including context wrappers. -/
  maxNodes : Nat := 4096
  deriving FromJson, ToJson

/-- A compact tree for following local elaboration. -/
def Config.focused : Config := { maxChildren := 10, maxDepth := 12, maxNodes := 1024 }

/-- More context for investigating complex elaboration. -/
def Config.detailed : Config := { maxChildren := 60, maxDepth := 48, maxNodes := 8192 }

/-- Bound client-supplied rendering limits. -/
def Config.bounded (config : Config) : Config := {
  maxChildren := max 1 (min 100 config.maxChildren)
  maxDepth := max 1 (min 64 config.maxDepth)
  maxNodes := max 1 (min 16384 config.maxNodes)
}

/-- Presentation-independent focused node data. Paths contain labels, not a delimited string. -/
structure FocusedPreview where
  title : String
  path : Array String
  output : String
  deriving Inhabited, ToJson, FromJson, Server.RpcEncodable

structure ExplorerCapture where
  summary : String := "No infotree summary captured yet. Move the cursor in a Lean file to populate this panel."
  tree : Option Json := none
  stxTree : Option Json := none
  facts : Array (String × String) := #[]
  cursorPath : Array String := #[]
  focused : Array FocusedPreview := #[]
  truncated : Bool := false
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
  | .ofChoiceResolutionInfo _ => "choiceResolution"
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
  | .hole _ => []
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
    let diffs := commandCtxDiffFieldsLite parent curr
    let mmDetails := commandCtxMainModuleDetails parent curr
    let mmChanged := !mmDetails.isEmpty
    if diffs.isEmpty then
      { changed := false, summary := "identical to immediate ancestor", tooltip := "identical to immediate ancestor" }
    else
      let summary :=
        if mmChanged then
          s!"changed [lite] (mainModule): {String.intercalate "; " diffs}"
        else
          s!"changed [lite]: {String.intercalate "; " diffs}"
      let tooltip :=
        if mmChanged then
          summary ++ "\n" ++ String.intercalate "\n" mmDetails
        else
          summary
      { changed := true, summary, tooltip, mainModuleChanged := mmChanged }

meta def stxLabel (text : FileMap) (stx : Syntax) : String :=
  let range := formatRange text stx
  match stx with
  | .node _ kind args =>
    if kind == `DevWidgets.truncated then "... (capture limit reached)"
    else s!"syntax.node {kind} (children={args.size}) @{range}"
  | .atom _ val => s!"syntax.atom \"{truncateStr 40 val}\" @{range}"
  | .ident _ _ val _ => s!"syntax.ident {val} @{range}"
  | .missing => "syntax.missing"

meta partial def infoTreeToExplorerTree
    (text : FileMap)
    (maxChildren : Nat := 30)
    (parentCommandCtx? : Option Elab.CommandContextInfo) (tree : Elab.InfoTree)
    (maxDepth : Nat := 32) : Json :=
  if maxDepth == 0 then treeJson "... (depth limit reached)" else
  match tree with
  | .hole id =>
    if id.name == `DevWidgets.truncated then treeJson "... (capture limit reached)"
    else treeJson s!"hole {id.name}"
  | .context pc tree =>
    match pc with
    | .commandCtx ctx =>
      let delta := commandCtxDelta parentCommandCtx? ctx
      treeJsonExt
        s!"context[commandCtx] ({delta.summary})"
        #[infoTreeToExplorerTree text maxChildren (some ctx) tree (maxDepth - 1)]
        [ ("nodeType", Json.str "commandCtx")
        , ("commandCtxChanged", Json.bool delta.changed)
        , ("commandCtxMainModuleChanged", Json.bool delta.mainModuleChanged)
        , ("commandCtxDiff", Json.str delta.tooltip)
        ]
    | .parentDeclCtx parentDecl =>
      treeJson s!"context[parentDecl={parentDecl}]"
        #[infoTreeToExplorerTree text maxChildren parentCommandCtx? tree (maxDepth - 1)]
    | .autoImplicitCtx implicits =>
      treeJson s!"context[autoImplicit={implicits.size}]"
        #[infoTreeToExplorerTree text maxChildren parentCommandCtx? tree (maxDepth - 1)]
  | .node info children =>
    let renderedChildren :=
      children.toList.take maxChildren |>.map (fun child => infoTreeToExplorerTree text maxChildren parentCommandCtx? child (maxDepth - 1))
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
    (stx : Syntax) (maxDepth : Nat := 32) : Json :=
  if maxDepth == 0 then treeJson "... (depth limit reached)" else
  match stx with
  | .missing =>
    treeJson "syntax.missing"
  | stx@(.atom ..) =>
    treeJson (stxLabel text stx)
  | stx@(.ident ..) =>
    treeJson (stxLabel text stx)
  | stx@(.node _ _ args) =>
    let renderedChildren :=
      args.toList.take maxChildren |>.map (fun child => stxToExplorerTree text maxChildren child (maxDepth - 1))
    let childArray := renderedChildren.toArray
    let childArray :=
      if args.size > maxChildren then
        childArray.push <| treeJson s!"... ({args.size - maxChildren} more children)"
      else
        childArray
    treeJson (stxLabel text stx) childArray

meta def customInfoNodesAtPosCount (tree : Elab.InfoTree) (pos : String.Pos.Raw) : Nat :=
  let customAtPos : List Unit :=
    tree.deepestNodes fun _ctxt info _arr =>
      match info with
      | .ofCustomInfo ⟨stx, _data⟩ =>
        if stxContainsPos stx pos then some () else none
      | _ => none
  customAtPos.length

meta def focusedPreviewItems
    (text : FileMap) (focused : List (Elab.Info × List String)) : Array FocusedPreview :=
  focused.toArray.map fun (info, path) =>
    { title := focusedNodeDetail text info, path := path.toArray, output := elaborationOutputPreview info }

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

private structure CaptureBudget where
  remaining : Nat
  truncated : Bool := false

private def takeCaptureNode : StateM CaptureBudget Bool := do
  let st ← get
  if st.remaining == 0 then
    modify fun s => { s with truncated := true }
    return false
  modify fun s => { s with remaining := s.remaining - 1 }
  return true

/-- Bound traversal before collecting facts, paths, or rendering. Never descend beyond `depth`. -/
private def limitInfoTree (tree : Elab.InfoTree) (depth : Nat) : StateM CaptureBudget Elab.InfoTree := do
  let truncated : Elab.InfoTree := .hole ⟨`DevWidgets.truncated⟩
  match depth with
  | 0 =>
    modify fun s => { s with truncated := true }
    return truncated
  | depth + 1 =>
    unless ← takeCaptureNode do return truncated
    match tree with
    | .hole _ => return tree
    | .context ctx child => return .context ctx (← limitInfoTree child depth)
    | .node info children =>
      let mut out := PersistentArray.empty
      for child in children do
        if (← get).remaining == 0 then
          modify fun s => { s with truncated := true }
          out := out.push truncated
          break
        out := out.push (← limitInfoTree child depth)
      return .node info out

private def limitSyntax (stx : Syntax) (depth : Nat) : StateM CaptureBudget Syntax := do
  match depth with
  | 0 =>
    modify fun s => { s with truncated := true }
    return .node .none `DevWidgets.truncated #[]
  | depth + 1 =>
    unless ← takeCaptureNode do return .node .none `DevWidgets.truncated #[]
    match stx with
    | .node info kind children =>
      let mut out := #[]
      for child in children do
        if (← get).remaining == 0 then
          modify fun s => { s with truncated := true }
          out := out.push (.node .none `DevWidgets.truncated #[])
          break
        out := out.push (← limitSyntax child depth)
      return .node info kind out
    | _ => return stx

/-- Returns a bounded copy and whether information was omitted. -/
meta def boundedInfoTree (tree : Elab.InfoTree) (config : Config) : Elab.InfoTree × Bool :=
  let config := config.bounded
  let (tree, state) := (limitInfoTree tree config.maxDepth).run { remaining := config.maxNodes }
  (tree, state.truncated)

meta def captureSummary
    (text : FileMap)
    (position : Lsp.Position)
    (snap : Lean.Server.Snapshots.Snapshot)
    (pos : String.Pos.Raw)
    (config : Config := {}) : ExplorerCapture :=
  let config := config.bounded
  let (infoTree, infoTruncated) := boundedInfoTree (Lean.Server.Snapshots.Snapshot.infoTree snap) config
  let (stx, syntaxBudget) := (limitSyntax snap.stx config.maxDepth).run { remaining := config.maxNodes }
  let infoNodeCount := infoTree.foldInfo (init := 0) fun _ctx _info n => n + 1
  let subtrees := rootSubtreeCount infoTree
  let tags := (infoTagSummary infoTree).toArray
  let path := pathToCursor text pos infoTree
  let focusedNodes := (focusedPathsWithInfo text pos infoTree).take 6
  let customAtPosCount := customInfoNodesAtPosCount infoTree pos
  let truncated := infoTruncated || syntaxBudget.truncated
  let summary := if truncated then "Partial capture: node or depth limit reached. Increase the limits for more context." else ""
  let tree := infoTreeToExplorerTree text config.maxChildren none infoTree config.maxDepth
  let stxTree := stxToExplorerTree text config.maxChildren stx config.maxDepth
  { summary, truncated
  , tree := some tree
  , stxTree := some stxTree
  , facts := snapshotFacts position snap subtrees infoNodeCount tags.size customAtPosCount
  , cursorPath := path.toArray
  , focused := focusedPreviewItems text focusedNodes
  }

private def infoTreeAtPosImpl (params : InfoTreeAtPosParams) : RequestM (RequestTask ExplorerCapture) := do
  DevWidgets.Lib.withSnapshotAtPos params.pos fun atPos => do
    return captureSummary atPos.text params.pos atPos.snap atPos.utf8Pos {
      maxChildren := params.maxChildren?.getD 30
      maxDepth := params.maxDepth?.getD 32
      maxNodes := params.maxNodes?.getD 4096
    }

@[implemented_by infoTreeAtPosImpl]
meta opaque infoTreeAtPos (params : InfoTreeAtPosParams) : RequestM (RequestTask ExplorerCapture)

attribute [server_rpc_method] infoTreeAtPos

@[widget_module]
def infoTreeExplorerWidget : Lean.Widget.Module where
  javascript := DevWidgets.Lib.Panel.javascript ++ "
    import { useAsyncPersistent, useRpcSession, mapRpcError } from '@leanprover/infoview'
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
        fontSize: '12px'
      };
      if (node.nodeType === 'commandCtx') {
        if (node.commandCtxChanged) {
          if (node.commandCtxMainModuleChanged) {
            return Object.assign({}, base, {
              background: 'rgba(220, 90, 90, 0.22)',
              border: '1px solid rgba(220, 90, 90, 0.6)',
              color: 'var(--vscode-editor-foreground)'
            });
          }
          return Object.assign({}, base, {
            background: 'rgba(215, 140, 60, 0.22)',
            border: '1px solid rgba(215, 140, 60, 0.5)',
            color: 'var(--vscode-editor-foreground)'
          });
        }
        return Object.assign({}, base, {
          background: 'rgba(110, 180, 130, 0.18)',
          color: 'var(--vscode-editor-foreground)'
        });
      }
      if (label.startsWith('context[')) {
        return Object.assign({}, base, { background: 'rgba(120, 140, 170, 0.18)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('tactic ')) {
        return Object.assign({}, base, { background: 'rgba(80, 180, 120, 0.18)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('term ')) {
        return Object.assign({}, base, { background: 'rgba(90, 150, 210, 0.18)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('command ')) {
        return Object.assign({}, base, { background: 'rgba(210, 150, 70, 0.18)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('custom ')) {
        return Object.assign({}, base, { background: 'rgba(190, 120, 210, 0.18)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('syntax.node ')) {
        return Object.assign({}, base, { background: 'rgba(100, 170, 220, 0.16)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('syntax.ident ')) {
        return Object.assign({}, base, { background: 'rgba(120, 200, 130, 0.16)', color: 'var(--vscode-editor-foreground)' });
      }
      if (label.startsWith('syntax.atom ')) {
        return Object.assign({}, base, { background: 'rgba(220, 170, 90, 0.16)', color: 'var(--vscode-editor-foreground)' });
      }
      return Object.assign({}, base, { background: 'rgba(128, 128, 128, 0.12)', color: 'var(--vscode-editor-foreground)' });
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
        if (!entry || !Array.isArray(entry.path) || entry.path.length === 0) continue;
        const labels = entry.path;
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

    export default function (props) {
      const rs = useRpcSession();
      const control = useCursorControls(props?.pos);
      const [limits, setLimits, resetLimits] = usePanelSettings({
        maxChildren: boundedNat(props?.maxChildren, 30, 1, 100),
        maxDepth: boundedNat(props?.maxDepth, 32, 1, 64),
        maxNodes: boundedNat(props?.maxNodes, 4096, 1, 16384)
      });
      const [forceOpen, setForceOpen] = React.useState(null);

      const liveCapture = useAsyncPersistent(async () => {
        if (control.pinned) return undefined;
        if (!props?.pos) {
          return {
            summary: 'No cursor position available yet.',
            tree: null,
            stxTree: null
          };
        }
        const params = { pos: props.pos, ...limits };
        const value = await rs.call('DevWidgets.InfoTreeExplorer.infoTreeAtPos', params);
        return { ...value, sourcePos: { ...props.pos } };
      }, [rs, props?.pos?.uri, props?.pos?.line, props?.pos?.character, control.pinned, control.revision, limits.maxChildren, limits.maxDepth, limits.maxNodes]);
      const capture = control.view(liveCapture);

      const payload =
        capture.state === 'resolved' && capture.value
          ? capture.value
          : capture.state === 'rejected'
            ? { summary: 'RPC error: ' + mapRpcError(capture.error).message, tree: null, stxTree: null, facts: [], cursorPath: [], focused: [] }
            : { summary: 'Waiting for snapshot data...', tree: null, stxTree: null, facts: [], cursorPath: [], focused: [] };
      const facts = Array.isArray(payload.facts) ? payload.facts : [];
      const cursorPath = Array.isArray(payload.cursorPath) ? payload.cursorPath : [];
      const focused = Array.isArray(payload.focused) ? payload.focused : [];
      const parsedFocused = focused;
      const focusedHitsByLabel = React.useMemo(() => {
        const m = new Map();
        for (const f of parsedFocused) {
          if (!f || !f.path) continue;
          for (const seg of f.path) {
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
      // Persistent results retain their own position while the next request is loading.
      const resultPos = payload.sourcePos || control.pos;
      const cursorLabel = resultPos
        ? 'L' + (resultPos.line + 1) + ':' + (resultPos.character + 1)
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
        cursorToolbar(control, capture, () => { resetLimits(); setForceOpen(null); }, resultPos),
        (payload.truncated || !control.pos || capture.state !== 'resolved' || (!payload.tree && !payload.stxTree))
          ? e('div', {
              role: capture.state === 'rejected' ? 'alert' : 'status',
              style: { whiteSpace: 'pre-wrap', color: capture.state === 'rejected'
                ? 'var(--vscode-errorForeground)' : 'var(--vscode-descriptionForeground)' }
            }, control.pos ? payload.summary : 'Move the cursor into a declaration to inspect elaboration.')
          : null,
        e('details', {},
          e('summary', {}, 'Tree settings'),
          e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: '0.5rem', alignItems: 'center' } },
            panelButton('Focused', () => setLimits({ maxChildren: 10, maxDepth: 12, maxNodes: 1024 }), control.pinned),
            panelButton('Detailed', () => setLimits({ maxChildren: 60, maxDepth: 48, maxNodes: 8192 }), control.pinned),
            e('label', {}, 'Children per node ', e('input', {
              type: 'number', min: 1, max: 100, value: limits.maxChildren, disabled: control.pinned,
              onChange: (ev) => setLimits((prev) => ({ ...prev, maxChildren: boundedNat(Number(ev.target.value), 30, 1, 100) })),
              style: { width: '4rem' }
            })),
            e('label', {}, 'Tree depth ', e('input', {
              type: 'number', min: 1, max: 64, value: limits.maxDepth, disabled: control.pinned,
              onChange: (ev) => setLimits((prev) => ({ ...prev, maxDepth: boundedNat(Number(ev.target.value), 32, 1, 64) })),
              style: { width: '4rem' }
            })),
            e('label', {}, 'Nodes per tree ', e('input', {
              type: 'number', min: 1, max: 16384, value: limits.maxNodes, disabled: control.pinned,
              onChange: (ev) => setLimits((prev) => ({ ...prev, maxNodes: boundedNat(Number(ev.target.value), 4096, 1, 16384) })),
              style: { width: '5rem' }
            }))
          )
        ),
        e('details', {}, e('summary', {}, 'Snapshot details · ' + cursorLabel),
          e('div', {
            style: {
              marginTop: '0.42rem',
              marginBottom: '0.35rem',
              display: 'flex',
              alignItems: 'center',
              gap: '0.3rem',
              flexWrap: 'wrap',
              overflowWrap: 'anywhere',
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
          )
        ),
        parsedFocused.length > 0
          ? e('div', { style: { marginTop: '0.3rem' } },
              e('div', {
                style: {
                  fontWeight: '600',
                  marginBottom: '0.2rem',
                  fontSize: '0.78rem',
                  color: 'var(--vscode-descriptionForeground)'
                }
              }, 'At cursor'),
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
                          whiteSpace: 'pre-wrap',
                          overflowWrap: 'anywhere'
                        }
                      }, f.output)
                    : null
                )
              ))
            )
          : null,
        e('details', { style: { marginTop: '0.5rem' } },
          e('summary', { style: { fontWeight: '600', cursor: 'pointer' } }, 'Path to cursor'),
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
                            }, 'path: ' + f.path.join(' > '))
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
                  )
                  : null
              )
            : null
        ),
        e('details', { style: { marginTop: '0.4rem' } },
          e('summary', { style: { fontWeight: '600', cursor: 'pointer' } }, 'InfoTree'),
        e('div', { style: { marginTop: '0.2rem', marginBottom: '0.5rem', display: 'flex', gap: '0.4rem', flexWrap: 'wrap' } },
          e('button', { onClick: () => setForceOpen(true) }, 'Expand all'),
          e('button', { onClick: () => setForceOpen(false) }, 'Collapse all'),
          e('button', { onClick: () => setForceOpen(null) }, 'Focus path')
        ),
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
