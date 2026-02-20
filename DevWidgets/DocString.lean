/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Widget.UserWidget
public import Lean.Server.FileWorker.RequestHandling
public import Lean.Server.Rpc.RequestHandling
public import Lean.DocString
public import Lean.Elab.DocString.Builtin
meta import Lean.Widget.Commands
public section

namespace DevWidgets.DocString

open Lean Widget Elab

structure DocAtPosParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure DocAtPosResponse where
  ident? : Option Name := none
  declName? : Option Name := none
  doc? : Option String := none
  docHtml? : Option String := none
  docFormat : String := "none"
  message : String := "No identifier under cursor."
  deriving FromJson, ToJson

private def constNameAtInfo (info : Elab.Info) : Option Name :=
  match info with
  | .ofTermInfo ti => ti.expr.getAppFn.constName?
  | .ofDelabTermInfo ti => ti.toTermInfo.expr.getAppFn.constName?
  | .ofFieldInfo fi => some fi.projName
  | _ => none

private def identAtPos? (stx : Syntax) (pos : String.Pos.Raw) : Option Name :=
  match stx.findStack? (fun stx => stx.getRange?.any (·.contains pos)) with
  | none => none
  | some stack =>
    stack.foldl (init := none) fun ident? (stx, _) =>
      match stx with
      | .ident _ _ id _ => some id
      | _ => ident?

private def isDocCommentKind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Command.docComment

private def isVersoCommentBodyKind (kind : Name) : Bool :=
  kind == ``Lean.Parser.Command.versoCommentBody

private def stxSpanContainsPos (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  match stx.getPos? (canonicalOnly := true), stx.getTailPos? (canonicalOnly := true) with
  | some startPos, some endPos => startPos <= pos && pos <= endPos
  | _, _ => false

private partial def firstSyntaxByKind? (kind : Name) (stx : Syntax) : Option Syntax :=
  match stx with
  | Syntax.node _ k args =>
    if k == kind then
      some stx
    else
      args.foldl (init := none) fun found? arg =>
        match found? with
        | some _ => found?
        | none => firstSyntaxByKind? kind arg
  | _ => none

private partial def smallestNodeByKindContainingPos? (kind : Name) (pos : String.Pos.Raw) (stx : Syntax) :
    Option Syntax :=
  match stx with
  | Syntax.node _ k args =>
    let inSpan := stxSpanContainsPos stx pos || stx.getRange?.any (·.contains pos (includeStop := true))
    if !inSpan then
      none
    else
      let child? :=
        args.foldl (init := none) fun found? arg =>
          match found? with
          | some _ => found?
          | none => smallestNodeByKindContainingPos? kind pos arg
      match child? with
      | some stx => some stx
      | none =>
        if k == kind then some stx else none
  | _ => none

private def declarationAtPos? (stx : Syntax) (pos : String.Pos.Raw) : Option Syntax := do
  match stx.findStack? (fun stx => stx.getRange?.any (·.contains pos (includeStop := true))) with
  | some stack =>
    stack.foldl (init := none) fun cmd? (stx, _) =>
      if stx.getKind == ``Lean.Parser.Command.declaration then some stx else cmd?
  | none =>
    smallestNodeByKindContainingPos? ``Lean.Parser.Command.declaration pos stx

private def docCommentAtPos? (stx : Syntax) (pos : String.Pos.Raw) :
    Option (TSyntax ``Lean.Parser.Command.docComment) :=
  match stx.findStack? (fun stx => stx.getRange?.any (·.contains pos (includeStop := true))) with
  | some stack =>
    let stackHit :=
      stack.foldl (init := none) fun doc? (stx, _) =>
        if isDocCommentKind stx.getKind then
          some ⟨stx⟩
        else
          doc?
    stackHit <|> (do
      let decl ← declarationAtPos? stx pos
      let docComment ← firstSyntaxByKind? ``Lean.Parser.Command.docComment decl
      if stxSpanContainsPos docComment pos then some ⟨docComment⟩ else none)
  | none =>
    none

private def docCommentAtOrNearPos? (stx : Syntax) (pos : String.Pos.Raw) :
    Option (String.Pos.Raw × TSyntax ``Lean.Parser.Command.docComment) :=
  let p1 := pos + ' '
  let p2 := p1 + ' '
  let p3 := p2 + ' '
  [pos, p1, p2, p3].findSome? fun p =>
    (docCommentAtPos? stx p).map (p, ·)

private def extractDocCommentPreview?
    (source : String)
    (docComment : TSyntax ``Lean.Parser.Command.docComment) :
    Option (String × String) := do
  match docComment.raw with
  | Syntax.node _ _ args =>
    let body ← args[1]?
    let startPos ← body.getPos? (canonicalOnly := true)
    let endPos ← body.getTailPos? (canonicalOnly := true)
    let text := String.Pos.Raw.extract source startPos (endPos.unoffsetBy ⟨2⟩)
    let fmt := if isVersoCommentBodyKind body.getKind then "verso-preview" else "markdown-preview"
    some (fmt, text.removeLeadingSpaces)
  | _ => none

private structure ParentDeclCandidate where
  decl : Name
  size : Nat

private def parentDeclAtPos? (infoTree : Elab.InfoTree) (pos : String.Pos.Raw) : Option Name :=
  let best? :=
    infoTree.foldInfo (init := (none : Option ParentDeclCandidate)) fun ctx info best? =>
      match ctx.parentDecl?, info.stx.getRange? (canonicalOnly := true) with
      | some decl, some r =>
        if !r.contains pos (includeStop := true) then
          best?
        else
          let cand : ParentDeclCandidate := { decl, size := r.start.byteDistance r.stop }
          match best? with
          | none => some cand
          | some best =>
            if cand.size <= best.size then some cand else some best
      | _, _ => best?
  best?.map (·.decl)

private partial def firstDeclIdName? (stx : Syntax) : Option Name :=
  match stx with
  | Syntax.node _ kind args =>
    if kind == ``Lean.Parser.Command.declId then
      match args[0]? with
      | some (Syntax.ident _ _ id _) => some id
      | _ => none
    else
      args.foldl (init := none) fun found? arg =>
        match found? with
        | some _ => found?
        | none => firstDeclIdName? arg
  | _ => none

private def declIdAtPos? (stx : Syntax) (pos : String.Pos.Raw) : Option Name := do
  let stack ← stx.findStack? (fun stx => stx.getRange?.any (·.contains pos (includeStop := true)))
  let declaration? :=
    stack.foldl (init := none) fun cmd? (stx, _) =>
      if stx.getKind == ``Lean.Parser.Command.declaration then some stx else cmd?
  firstDeclIdName? =<< declaration?

private def appendNameCandidate (acc : List Name) (n? : Option Name) : List Name :=
  match n? with
  | some n =>
    if acc.contains n then acc else acc ++ [n]
  | none => acc

private def declarationNameCandidates (currNs : Name) (fromCtx? fromStx? : Option Name) : List Name :=
  let fromStxInNs? := fromStx?.bind fun n =>
    if n.isAtomic then some (currNs ++ n) else none
  [fromCtx?, fromStx?, fromStxInNs?] |>.foldl appendNameCandidate []

private def identifierNameCandidates (fromInfo? ident? : Option Name) : List Name :=
  [fromInfo?, ident?] |>.foldl appendNameCandidate []

namespace Testing

/-- Testing hook: find a declaration id around a cursor position. -/
def declIdAtPos? (stx : Syntax) (pos : String.Pos.Raw) : Option Name :=
  DevWidgets.DocString.declIdAtPos? stx pos

/-- Testing hook: detect whether a cursor position is inside a doc comment. -/
def isInDocComment (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  (DevWidgets.DocString.docCommentAtPos? stx pos).isSome

/-- Testing hook: detect whether a cursor/nearby position is inside a doc comment. -/
def isInDocCommentNear (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  (DevWidgets.DocString.docCommentAtOrNearPos? stx pos).isSome

/-- Testing hook: declaration candidate ordering/dedup used by the resolver. -/
def declarationCandidates (currNs : Name) (fromCtx? fromStx? : Option Name) : List Name :=
  DevWidgets.DocString.declarationNameCandidates currNs fromCtx? fromStx?

/-- Testing hook: identifier candidate ordering/dedup used by the resolver. -/
def identifierCandidates (fromInfo? ident? : Option Name) : List Name :=
  DevWidgets.DocString.identifierNameCandidates fromInfo? ident?

end Testing

open Server RequestM

private def htmlEscape (s : String) : String :=
  s
    |>.replace "&" "&amp;"
    |>.replace "<" "&lt;"
    |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;"
    |>.replace "'" "&#39;"

private def renderHighlightClass (hl : Lean.Doc.DocHighlight) : String :=
  match hl with
  | .const .. => "lean-const"
  | .var .. => "lean-var"
  | .field .. => "lean-field"
  | .option .. => "lean-option"
  | .keyword => "lean-kw"
  | .literal .. => "lean-lit"

private def renderHighlightTitle? (hl : Lean.Doc.DocHighlight) : Option String :=
  match hl with
  | .const n sig => some s!"{n}\n{sig}"
  | .var n _ ty => some s!"{n} : {ty}"
  | .field n sig => some s!"{n}\n{sig}"
  | .option n declName => some s!"option {n}\ndeclared by {declName}"
  | .keyword => none
  | .literal kind ty? =>
    let typeSuffix := ty?.map (fun t => s!"\n{t}") |>.getD ""
    some s!"{kind}{typeSuffix}"

private def renderDocCodeChunk (chunk : String × Option Lean.Doc.DocHighlight) : String :=
  let (txt, hl?) := chunk
  let txt := htmlEscape txt
  match hl? with
  | none => txt
  | some hl =>
    let cls := renderHighlightClass hl
    let titleAttr := (renderHighlightTitle? hl).map (fun t => s!" title=\"{htmlEscape t}\"") |>.getD ""
    s!"<span class=\"lean-token {cls}\"{titleAttr}>{txt}</span>"

private def renderDocCodeBody (code : Lean.Doc.DocCode) : String :=
  String.join <| code.code.toList.map renderDocCodeChunk

private def renderDocCodeHtml (code : Lean.Doc.DocCode) : String :=
  let body := renderDocCodeBody code
  s!"<pre class=\"lean-code\"><code class=\"language-lean\">{body}</code></pre>"

private def renderDocCodeInlineHtml (code : Lean.Doc.DocCode) (cls := "lean-term") : String :=
  let body := renderDocCodeBody code
  s!"<code class=\"lean-ref {cls}\">{body}</code>"

private def renderSpecialInline? (container : ElabInline) (body : String) : Option String :=
  if let some c := container.val.get? (α := Lean.Doc.Data.Const) then
    some s!"<code class=\"lean-ref lean-const\" title=\"{htmlEscape (toString c.name)}\">{body}</code>"
  else if let some t := container.val.get? (α := Lean.Doc.Data.LeanTerm) then
    some (renderDocCodeInlineHtml t.term "lean-term")
  else if let some v := container.val.get? (α := Lean.Doc.Data.Local) then
    let title := s!"{v.name} : {v.type}"
    some s!"<code class=\"lean-ref lean-var\" title=\"{htmlEscape title}\">{body}</code>"
  else if let some f := container.val.get? (α := Lean.Doc.Data.Tactic) then
    some s!"<code class=\"lean-ref lean-tactic\" title=\"{htmlEscape (toString f.name)}\">{body}</code>"
  else if let some c := container.val.get? (α := Lean.Doc.Data.ConvTactic) then
    some s!"<code class=\"lean-ref lean-tactic\" title=\"{htmlEscape (toString c.name)}\">{body}</code>"
  else if let some o := container.val.get? (α := Lean.Doc.Data.Option) then
    some s!"<code class=\"lean-ref lean-option\" title=\"{htmlEscape (toString o.name)}\">{body}</code>"
  else if let some o := container.val.get? (α := Lean.Doc.Data.SetOption) then
    some (renderDocCodeInlineHtml o.term "lean-option")
  else if let some s := container.val.get? (α := Lean.Doc.Data.SyntaxCat) then
    some s!"<code class=\"lean-ref lean-syntax\" title=\"{htmlEscape (toString s.name)}\">{body}</code>"
  else if let some s := container.val.get? (α := Lean.Doc.Data.Syntax) then
    some s!"<code class=\"lean-ref lean-syntax\" title=\"{htmlEscape (toString s.category)}\">{body}</code>"
  else if let some m := container.val.get? (α := Lean.Doc.Data.ModuleName) then
    some s!"<code class=\"lean-ref lean-module\" title=\"{htmlEscape (toString m.module)}\">{body}</code>"
  else
    none

private def renderSpecialBlock? (container : ElabBlock) : Option String :=
  if let some b := container.val.get? (α := Lean.Doc.Data.LeanBlock) then
    some (renderDocCodeHtml b.commands)
  else if let some t := container.val.get? (α := Lean.Doc.Data.LeanTerm) then
    some (renderDocCodeHtml t.term)
  else if let some o := container.val.get? (α := Lean.Doc.Data.SetOption) then
    some (renderDocCodeHtml o.term)
  else
    none

mutual
  private partial def renderInlineHtml (inl : Doc.Inline ElabInline) : String :=
    match inl with
    | .text s => htmlEscape s
    | .emph content => s!"<em>{renderInlinesHtml content}</em>"
    | .bold content => s!"<strong>{renderInlinesHtml content}</strong>"
    | .code s => s!"<code>{htmlEscape s}</code>"
    | .math .inline s => s!"<code class=\"math-inline\">{htmlEscape s}</code>"
    | .math .display s => s!"<div class=\"math-display\">{htmlEscape s}</div>"
    | .linebreak _ => " "
    | .link content url =>
      s!"<a href=\"{htmlEscape url}\">{renderInlinesHtml content}</a>"
    | .footnote name content =>
      s!"<sup class=\"footnote-ref\">{htmlEscape name}</sup><span class=\"footnote-body\">{renderInlinesHtml content}</span>"
    | .image alt url =>
      s!"<img alt=\"{htmlEscape alt}\" src=\"{htmlEscape url}\" />"
    | .concat content => renderInlinesHtml content
    | .other container content =>
      let body := renderInlinesHtml content
      (renderSpecialInline? container body).getD body

  private partial def renderInlinesHtml (inls : Array (Doc.Inline ElabInline)) : String :=
    String.join <| inls.toList.map renderInlineHtml

  private partial def renderListItemHtml (item : Doc.ListItem (Doc.Block ElabInline ElabBlock)) : String :=
    s!"<li>{renderBlocksHtml item.contents}</li>"

  private partial def renderDescItemHtml
      (item : Doc.DescItem (Doc.Inline ElabInline) (Doc.Block ElabInline ElabBlock)) : String :=
    s!"<dt>{renderInlinesHtml item.term}</dt><dd>{renderBlocksHtml item.desc}</dd>"

  private partial def renderBlockHtml (blk : Doc.Block ElabInline ElabBlock) : String :=
    match blk with
    | .para contents => s!"<p>{renderInlinesHtml contents}</p>"
    | .code content => s!"<pre><code>{htmlEscape content}</code></pre>"
    | .ul items =>
      s!"<ul>{String.join <| items.toList.map renderListItemHtml}</ul>"
    | .ol start items =>
      let attrs := if start == 1 then "" else s!" start=\"{start}\""
      s!"<ol{attrs}>{String.join <| items.toList.map renderListItemHtml}</ol>"
    | .dl items =>
      s!"<dl>{String.join <| items.toList.map renderDescItemHtml}</dl>"
    | .blockquote items =>
      s!"<blockquote>{renderBlocksHtml items}</blockquote>"
    | .concat content => renderBlocksHtml content
    | .other container content =>
      let fallback := renderBlocksHtml content
      (renderSpecialBlock? container).getD fallback

  private partial def renderBlocksHtml (blocks : Array (Doc.Block ElabInline ElabBlock)) : String :=
    String.join <| blocks.toList.map renderBlockHtml

  private partial def renderPartHtml (depth : Nat) (part : Doc.Part ElabInline ElabBlock Empty) : String :=
    let level := min 6 (depth + 1)
    s!"<section><h{level}>{renderInlinesHtml part.title}</h{level}>{renderBlocksHtml part.content}{renderPartsHtml (depth + 1) part.subParts}</section>"

  private partial def renderPartsHtml (depth : Nat) (parts : Array (Doc.Part ElabInline ElabBlock Empty)) : String :=
    String.join <| parts.toList.map (renderPartHtml depth)
end

/-- Render a Verso docstring to HTML for the DocString widget. -/
def renderVersoDocHtml (doc : VersoDocString) : String :=
  s!"<div class=\"verso-doc\">{renderBlocksHtml doc.text}{renderPartsHtml 1 doc.subsections}</div>"

private def docAtNameCore? (env : Environment) (declName : Name) :
    IO (Option (String × Option String × Option String)) := do
  match (← findInternalDocString? env declName) with
  | some (.inl md) => pure (some ("markdown", some md, none))
  | some (.inr verso) => pure (some ("verso", none, some (renderVersoDocHtml verso)))
  | none => pure none

private def docAtName? (env : Environment) (declName : Name) :
    IO (Option (String × Option String × Option String)) := do
  let task ← IO.asTask (prio := .dedicated) do
    docAtNameCore? env declName
  match (← IO.wait task) with
  | .ok doc? => pure doc?
  | .error _ => pure none

private def docAtNames? (env : Environment) (candidates : List Name) :
    IO (Option (Name × String × Option String × Option String)) := do
  for declName in candidates do
    if let some (fmt, md?, html?) ← docAtName? env declName then
      return some (declName, fmt, md?, html?)
  return none

private def docAtPosImpl (params : DocAtPosParams) : RequestM (RequestTask DocAtPosResponse) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos params.pos
  bindWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := throw ⟨.invalidParams, s!"no snapshot found at {params.pos}"⟩) fun snap => do
      RequestM.mapTaskCostly (findInfoTreeAtPos doc hoverPos (includeStop := true)) fun infoTree? => do
        let nearDocComment? := docCommentAtOrNearPos? snap.stx hoverPos
        let probePos := nearDocComment?.map (·.1) |>.getD hoverPos
        let inDocComment? := nearDocComment?.map (·.2)
        let info? := infoTree?.bind (fun t => t.hoverableInfoAtM? (m := Id) hoverPos (includeStop := true))
        let infoName? := info?.bind (fun i => constNameAtInfo i.info)
        let identName? := identAtPos? snap.stx hoverPos

        -- 1) Identifier-first lookup (narrowest infotree info, then syntax identifier fallback).
        let identCandidates := identifierNameCandidates infoName? identName?
        if let some (declName, docFormat, doc?, docHtml?) ← docAtNames? snap.env identCandidates then
          return {
            ident? := identName?
            declName? := some declName
            doc? := doc?
            docHtml? := docHtml?
            docFormat := docFormat
            message := s!"Docstring found for `{declName}` ({docFormat})."
          }

        -- 2) Declaration-level lookup (inside declaration body or docstring).
        let fromCtx? := infoTree?.bind (fun t => parentDeclAtPos? t probePos)
        let fromStx? := declIdAtPos? snap.stx probePos
        let currNs := snap.cmdState.scopes.head!.currNamespace
        let declarationCandidates := declarationNameCandidates currNs fromCtx? fromStx?
        if let some (declName, docFormat, doc?, docHtml?) ← docAtNames? snap.env declarationCandidates then
          return {
            ident? := identName?
            declName? := some declName
            doc? := doc?
            docHtml? := docHtml?
            docFormat := docFormat
            message :=
              if inDocComment?.isSome then
                s!"Live preview from elaborated docstring for `{declName}`."
              else
                s!"Docstring found for declaration `{declName}` ({docFormat})."
          }

        -- 3) Raw doc-comment fallback only when the cursor is inside a doc comment.
        if let some docComment := inDocComment? then
          if let some (docFormat, docText) := extractDocCommentPreview? text.source docComment then
            return {
              ident? := identName?
              doc? := some docText
              docFormat := docFormat
              message := "Elaborated preview unavailable; showing raw docstring preview."
            }

        -- 4) Nothing relevant at cursor.
        let msg := match identName?, declarationCandidates.head? with
          | some identName, _ => s!"No docstring found for `{identName}`."
          | none, some declName => s!"No docstring found for declaration `{declName}`."
          | none, none => "No identifier or documented declaration under cursor."
        return {
          ident? := identName?
          docFormat := "none"
          message := msg
        }

@[implemented_by docAtPosImpl]
meta opaque docAtPos (params : DocAtPosParams) : RequestM (RequestTask DocAtPosResponse)

attribute [server_rpc_method] docAtPos

def widgetJs : String := r#"
import * as React from 'react'
import { useAsync, useRpcSession, mapRpcError } from '@leanprover/infoview'

const MARKED_CDN = 'https://cdn.jsdelivr.net/npm/marked@15.0.12/marked.min.js'

function fmtPos(pos) {
  if (!pos) return 'unknown'
  const file = typeof pos.uri === 'string' ? pos.uri.split('/').pop() : '<file>'
  return `${file}:${pos.line + 1}:${pos.character + 1}`
}

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/\"/g, '&quot;')
    .replace(/'/g, '&#39;')
}

function loadMarkedFromCdn() {
  if (typeof window === 'undefined') return Promise.resolve(null)
  if (window.marked && typeof window.marked.parse === 'function') {
    return Promise.resolve(window.marked)
  }
  return new Promise((resolve, reject) => {
    const existing = document.querySelector('script[data-docstring-marked="1"]')
    if (existing) {
      existing.addEventListener('load', () => resolve(window.marked || null), { once: true })
      existing.addEventListener('error', () => reject(new Error('Failed to load marked.js')), { once: true })
      return
    }
    const script = document.createElement('script')
    script.src = MARKED_CDN
    script.async = true
    script.dataset.docstringMarked = '1'
    script.onload = () => resolve(window.marked || null)
    script.onerror = () => reject(new Error('Failed to load marked.js'))
    document.head.appendChild(script)
  })
}

function fallbackMarkdownHtml(rawDoc) {
  return `<pre><code>${escapeHtml(rawDoc)}</code></pre>`
}

export default function DocStringWidget(props) {
  const rs = useRpcSession()
  const current = fmtPos(props?.pos)
  const [markedApi, setMarkedApi] = React.useState(null)

  React.useEffect(() => {
    let cancelled = false
    loadMarkedFromCdn()
      .then((api) => {
        if (!cancelled) setMarkedApi(api)
      })
      .catch(() => {
        if (!cancelled) setMarkedApi(null)
      })
    return () => { cancelled = true }
  }, [])

  const docState = useAsync(async () => {
    if (!props?.pos) return undefined
    const params = { pos: props.pos }
    return await rs.call('DevWidgets.DocString.docAtPos', params)
  }, [rs, props?.pos?.uri, props?.pos?.line, props?.pos?.character])

  const c = {
    border: 'var(--vscode-editorWidget-border, #555)',
    fg: 'var(--vscode-editor-foreground, #ddd)',
    bg: 'var(--vscode-editor-background, #1e1e1e)',
    muted: 'var(--vscode-descriptionForeground, #9aa1a8)',
    panel: 'var(--vscode-textCodeBlock-background, #111)',
    err: 'var(--vscode-errorForeground, #f14c4c)'
  }

  const renderedHtml = React.useMemo(() => {
    if (!(docState.state === 'resolved' && docState.value)) return ''
    const fmt = String(docState.value.docFormat || 'none')
    const rawDoc = typeof docState.value.doc === 'string' ? docState.value.doc : ''
    const versoHtml = typeof docState.value.docHtml === 'string' ? docState.value.docHtml : ''
    if (fmt === 'verso') {
      return versoHtml === '' ? '<p>(no rendered Verso doc)</p>' : versoHtml
    }
    if (fmt === 'markdown') {
      if (rawDoc === '') return '<p>(no docstring)</p>'
      if (markedApi && typeof markedApi.parse === 'function') {
        try {
          return markedApi.parse(rawDoc)
        } catch (_err) {
          return fallbackMarkdownHtml(rawDoc)
        }
      }
      return fallbackMarkdownHtml(rawDoc)
    }
    if (rawDoc !== '' && markedApi && typeof markedApi.parse === 'function') {
      try {
        return markedApi.parse(rawDoc)
      } catch (_err) {
        return fallbackMarkdownHtml(rawDoc)
      }
    }
    return rawDoc === '' ? '<p>(no docstring)</p>' : fallbackMarkdownHtml(rawDoc)
  }, [docState, markedApi])

  const panelStyle = {
    border: `1px solid ${c.border}`,
    borderRadius: '8px',
    marginTop: '0.4rem',
    overflow: 'hidden',
    background: c.bg
  }

  const header = React.createElement(
    'div',
    {
      style: {
        padding: '0.55rem 0.65rem',
        borderBottom: `1px solid ${c.border}`,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'space-between'
      }
    },
    React.createElement('div', { style: { fontWeight: 700, letterSpacing: '0.02em', color: c.fg } }, 'DocString'),
    React.createElement('div', { style: { fontSize: '0.82em', color: c.muted } }, 'Rendered HTML')
  )

  let body
  if (docState.state === 'resolved' && docState.value) {
    const ident = docState.value.ident || '<none>'
    const decl = docState.value.declName || ident
    const docFormat = String(docState.value.docFormat || 'none')
    body = React.createElement(
      React.Fragment,
      null,
      React.createElement('div', { style: { marginBottom: '0.4rem', color: c.fg, fontWeight: 600 } }, String(decl)),
      React.createElement(
        'div',
        { style: { marginBottom: '0.45rem', color: c.muted, fontSize: '0.9em', whiteSpace: 'pre-wrap' } },
        docState.value.message || ''
      ),
      React.createElement(
        'div',
        { style: { marginBottom: '0.45rem', color: c.muted, fontSize: '0.82em' } },
        `format: ${docFormat}`
      ),
      React.createElement(
        'div',
        {
          style: {
            margin: 0,
            padding: '0.6rem',
            borderRadius: '6px',
            border: `1px solid ${c.border}`,
            background: c.panel,
            maxHeight: '18rem',
            overflow: 'auto',
            color: c.fg,
            fontSize: '12px',
            lineHeight: '1.45'
          },
          className: 'docstring-rendered',
          dangerouslySetInnerHTML: { __html: renderedHtml }
        },
        null
      )
    )
  } else if (docState.state === 'rejected') {
    body = React.createElement(
      'div',
      { style: { color: c.err, whiteSpace: 'pre-wrap' } },
      mapRpcError(docState.error).message
    )
  } else {
    body = React.createElement(
      'div',
      { style: { color: c.muted } },
      'Reading docstring at cursor...'
    )
  }

  const footer = React.createElement(
    'div',
    {
      style: {
        borderTop: `1px solid ${c.border}`,
        padding: '0.35rem 0.65rem',
        color: c.muted,
        fontSize: '0.86em'
      }
    },
    `Cursor: ${current}`
  )

  return React.createElement(
    'div',
    panelStyle,
    header,
    React.createElement(
      'style',
      null,
      `
      .docstring-rendered p { margin: 0.35rem 0; }
      .docstring-rendered ul, .docstring-rendered ol { margin: 0.35rem 0 0.35rem 1.25rem; padding: 0; }
      .docstring-rendered li { margin: 0.15rem 0; }
      .docstring-rendered h1, .docstring-rendered h2, .docstring-rendered h3,
      .docstring-rendered h4, .docstring-rendered h5, .docstring-rendered h6 {
        margin: 0.45rem 0 0.2rem 0;
        line-height: 1.25;
      }
      .docstring-rendered code {
        font-family: var(--vscode-editor-font-family, ui-monospace, SFMono-Regular, Menlo, Consolas, monospace);
        background: rgba(255,255,255,0.06);
        border-radius: 4px;
        padding: 0.02rem 0.24rem;
      }
      .docstring-rendered .lean-ref {
        border: 1px solid rgba(255,255,255,0.08);
      }
      .docstring-rendered pre {
        margin: 0.4rem 0;
        padding: 0.45rem 0.55rem;
        background: rgba(0,0,0,0.18);
        border: 1px solid ${c.border};
        border-radius: 6px;
        overflow: auto;
      }
      .docstring-rendered pre code { background: transparent; padding: 0; }
      .docstring-rendered .lean-code {
        background: var(--vscode-textCodeBlock-background, rgba(0,0,0,0.18));
      }
      .docstring-rendered .lean-token {
        border-radius: 3px;
      }
      .docstring-rendered .lean-kw {
        color: var(--vscode-symbolIcon-keywordForeground, #c586c0);
      }
      .docstring-rendered .lean-const {
        color: var(--vscode-symbolIcon-functionForeground, #dcdcaa);
      }
      .docstring-rendered .lean-var {
        color: var(--vscode-symbolIcon-variableForeground, #9cdcfe);
      }
      .docstring-rendered .lean-field {
        color: var(--vscode-symbolIcon-propertyForeground, #4fc1ff);
      }
      .docstring-rendered .lean-option {
        color: var(--vscode-symbolIcon-constantForeground, #d19a66);
      }
      .docstring-rendered .lean-lit {
        color: var(--vscode-editorInfo-foreground, #ce9178);
      }
      .docstring-rendered .lean-tactic {
        color: var(--vscode-symbolIcon-methodForeground, #b5cea8);
      }
      .docstring-rendered .lean-term {
        color: var(--vscode-editor-foreground, #d4d4d4);
      }
      .docstring-rendered .lean-syntax {
        color: var(--vscode-symbolIcon-classForeground, #4ec9b0);
      }
      .docstring-rendered .lean-module {
        color: var(--vscode-symbolIcon-moduleForeground, #d7ba7d);
      }
      .docstring-rendered a { color: var(--vscode-textLink-foreground, #3794ff); }
      .docstring-rendered blockquote {
        margin: 0.4rem 0;
        padding: 0.15rem 0.55rem;
        border-left: 3px solid ${c.border};
        color: ${c.muted};
      }
      `
    ),
    React.createElement('div', { style: { padding: '0.65rem' } }, body),
    footer
  )
}
"#

@[widget_module]
abbrev docStringWidget : Widget.Module where
  javascript := widgetJs

end DevWidgets.DocString

open DevWidgets.DocString in
show_panel_widgets [docStringWidget]
