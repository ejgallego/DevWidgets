/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.DocString
public import Lean.Elab.DocString.Builtin
public section

namespace DevWidgets.DocString

open Lean Elab

/-- Response format tag for elaborated Verso docstrings. -/
def versoDocFormat : String := "verso"

/-- Response format tag for raw Verso doc-comment previews. -/
def versoPreviewDocFormat : String := "verso-preview"

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

end DevWidgets.DocString
