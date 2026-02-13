/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Widget.UserWidget
public import Lean.Server.FileWorker.RequestHandling
public import Lean.Server.Rpc.RequestHandling
public import Lean.Compiler.LCNF.Main
public section

namespace DevWidgets.CE

open Lean Widget Elab

structure IRAtPosParams where
  pos : Lsp.Position
  deriving FromJson, ToJson

structure IRAtPosResponse where
  declName? : Option Name := none
  hasIR : Bool := false
  irCode? : Option String := none
  lcnfCode? : Option String := none
  message : String := "No declaration under cursor."
  deriving FromJson, ToJson

private def constNameAtInfo (info : Elab.Info) : Option Name :=
  match info with
  | .ofTermInfo ti => ti.expr.getAppFn.constName?
  | .ofDelabTermInfo ti => ti.toTermInfo.expr.getAppFn.constName?
  | .ofFieldInfo fi => some fi.projName
  | _ => none

private def hasIRCode (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ | .opaqueInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

private def compileIRCode? (declName : Name) : CoreM (Option String) := do
  try
    let sccs ← Lean.Compiler.LCNF.compile #[declName]
    let mut lines : Array String := #[]
    for scc in sccs do
      for d in scc do
        lines := lines.push (toString d)
    if lines.isEmpty then
      return none
    else
      return some <| String.intercalate "\n\n" lines.toList
  catch _ =>
    return none

private def compileLCNFCode? (declName : Name) : CoreM (Option String) := do
  try
    let decl ← Lean.Compiler.LCNF.CompilerM.run <| Lean.Compiler.LCNF.toDecl declName
    let fmt ← Lean.Compiler.LCNF.ppDecl' decl
    return some fmt.pretty
  catch _ =>
    return none

open Server RequestM
private def irAtPosImpl (params : IRAtPosParams) : RequestM (RequestTask IRAtPosResponse) := do
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc ← readDoc
    let hoverPos := doc.meta.text.lspPosToUtf8Pos params.pos
    let info? := snap.infoTree.hoverableInfoAtM? (m := Id) hoverPos (includeStop := true)
    let some info := info?
      | return { message := "No declaration under cursor." }
    let some declName := constNameAtInfo info.info
      | return { message := "No declaration under cursor." }
    let env := info.ctx.env
    let hasIR := (env.find? declName).map hasIRCode |>.getD false
    let irCode? ← if hasIR then
      RequestM.runCoreM snap do
        withEnv env do
          compileIRCode? declName
    else
      pure (none : Option String)
    let lcnfCode? ← if hasIR then
      RequestM.runCoreM snap do
        withEnv env do
          compileLCNFCode? declName
    else
      pure (none : Option String)
    let msg := if hasIR then s!"{declName} has IR code." else s!"{declName} has no IR code."
    return { declName? := some declName, hasIR, irCode?, lcnfCode?, message := msg }

@[implemented_by irAtPosImpl]
meta opaque irAtPos (params : IRAtPosParams) : RequestM (RequestTask IRAtPosResponse)

attribute [server_rpc_method] irAtPos

def widgetJs : String := r#"
import * as React from 'react'
import { useAsync, useRpcSession, mapRpcError } from '@leanprover/infoview'

function fmtPos(pos) {
  if (!pos) return 'unknown'
  const file = typeof pos.uri === 'string' ? pos.uri.split('/').pop() : '<file>'
  return `${file}:${pos.line + 1}:${pos.character + 1}`
}

const CODE_KEYWORDS = new Set([
  'def', 'extern', 'let', 'ret', 'case', 'of', 'jmp', 'set', 'uset', 'sset', 'setTag',
  'inc', 'dec', 'del', 'default', 'unreachable', 'fun', 'in', 'reuse', 'reset',
  'pap', 'app', 'proj', 'uproj', 'sproj', 'box', 'unbox', 'ctor'
])

function classifyToken(tok) {
  if (/^".*"$/.test(tok)) return 'str'
  if (/^[0-9]+$/.test(tok)) return 'num'
  if (CODE_KEYWORDS.has(tok)) return 'kw'
  if (/^[A-Za-z_][A-Za-z0-9_'.]*$/.test(tok)) return 'id'
  return 'punct'
}

function tokenizeLine(line) {
  const re = /("([^"\\]|\\.)*"|[A-Za-z_][A-Za-z0-9_'.]*|[0-9]+|→|:=|[-=><!&|+*/()[\]{}.,;:])/g
  const out = []
  let idx = 0
  let m
  while ((m = re.exec(line)) !== null) {
    const start = m.index
    if (start > idx) out.push({ t: line.slice(idx, start), k: 'ws' })
    out.push({ t: m[0], k: classifyToken(m[0]) })
    idx = re.lastIndex
  }
  if (idx < line.length) out.push({ t: line.slice(idx), k: 'ws' })
  return out
}

function lineIndent(line) {
  let n = 0
  for (const ch of line) {
    if (ch === ' ') n += 1
    else if (ch === '\t') n += 2
    else break
  }
  return n
}

function computeIndentFoldRanges(lines) {
  const ranges = new Map()
  const n = lines.length
  for (let i = 0; i < n; i++) {
    const line = lines[i]
    if (!line || line.trim() === '') continue
    const base = lineIndent(line)

    let j = i + 1
    while (j < n && lines[j].trim() === '') j++
    if (j >= n) continue
    if (lineIndent(lines[j]) <= base) continue

    let end = j
    let k = j + 1
    while (k < n) {
      const lk = lines[k]
      if (lk.trim() === '') {
        end = k
        k++
        continue
      }
      if (lineIndent(lk) <= base) break
      end = k
      k++
    }
    if (end > i) ranges.set(i, end)
  }
  return ranges
}

function renderIndentFoldedCode(key, text, emptyText, c, foldState, setFoldState) {
  const boxStyle = {
    margin: 0,
    padding: '0.6rem',
    borderRadius: '6px',
    border: `1px solid ${c.border}`,
    background: c.panel,
    maxHeight: '18rem',
    overflow: 'auto',
    color: c.fg,
    fontFamily: 'var(--vscode-editor-font-family, ui-monospace, SFMono-Regular, Menlo, Consolas, monospace)',
    fontSize: 'var(--vscode-editor-font-size, 12px)',
    lineHeight: '1.45'
  }
  if (!text) {
    return React.createElement(
      'div',
      {
        key,
        style: { ...boxStyle, color: c.muted, whiteSpace: 'pre-wrap' }
      },
      emptyText
    )
  }

  const lines = text.split('\n')
  const ranges = computeIndentFoldRanges(lines)
  const styleByKind = {
    kw: { color: c.kw, fontWeight: 600 },
    id: { color: c.id },
    num: { color: c.num },
    str: { color: c.str },
    punct: { color: c.punct },
    ws: { color: c.fg }
  }
  const rendered = []
  let i = 0
  while (i < lines.length) {
    const lineIdx = i
    const line = lines[lineIdx]
    const end = ranges.get(lineIdx)
    const isFoldable = end !== undefined
    const collapsed = isFoldable && foldState[lineIdx] === true
    const hiddenCount = collapsed ? Math.max(0, end - i) : 0

    rendered.push(React.createElement(
      'div',
      { key: `${key}-ln-${lineIdx}`, style: { display: 'flex', alignItems: 'baseline', whiteSpace: 'pre' } },
      React.createElement(
        'span',
        { style: { display: 'inline-block', width: '1.2rem', color: c.muted, userSelect: 'none' } },
        isFoldable ? React.createElement(
          'button',
          {
            onClick: () => setFoldState(prev => ({ ...prev, [lineIdx]: !prev[lineIdx] })),
            style: {
              cursor: 'pointer',
              border: 'none',
              background: 'transparent',
              color: c.muted,
              padding: 0,
              lineHeight: 1,
              fontSize: '0.9em'
            },
            title: collapsed ? 'Unfold block' : 'Fold block'
          },
          collapsed ? '▸' : '▾'
        ) : ' '
      ),
      React.createElement(
        'span',
        null,
        ...tokenizeLine(line).map((tok, j) =>
          React.createElement('span', { key: `${key}-tk-${lineIdx}-${j}`, style: styleByKind[tok.k] }, tok.t)
        ),
        collapsed ? React.createElement(
          'span',
          { style: { color: c.muted } },
          `  ... ${hiddenCount} lines`
        ) : null
      )
    ))

    if (collapsed) i = end + 1
    else i += 1
  }

  return React.createElement('div', { key, style: boxStyle }, ...rendered)
}

export default function ClickPositionWidget(props) {
  const rs = useRpcSession()
  const current = fmtPos(props?.pos)
  const [irFoldState, setIrFoldState] = React.useState({})
  const [lcnfFoldState, setLcnfFoldState] = React.useState({})

  const irState = useAsync(async () => {
    if (!props?.pos) return undefined
    const params = { pos: props.pos }
    let lastError
    for (const method of ['irAtPos', 'DevWidgets.CE.irAtPos']) {
      try {
        return await rs.call(method, params)
      } catch (err) {
        lastError = err
      }
    }
    throw lastError
  }, [rs, props?.pos?.uri, props?.pos?.line, props?.pos?.character])

  const c = {
    border: 'var(--vscode-editorWidget-border, #555)',
    fg: 'var(--vscode-editor-foreground, #ddd)',
    bg: 'var(--vscode-editor-background, #1e1e1e)',
    muted: 'var(--vscode-descriptionForeground, #9aa1a8)',
    ok: 'var(--vscode-testing-iconPassed, #73c991)',
    warn: 'var(--vscode-testing-iconQueued, #cca700)',
    err: 'var(--vscode-errorForeground, #f14c4c)',
    panel: 'var(--vscode-textCodeBlock-background, #111)',
    kw: '#c678dd',
    id: '#61afef',
    num: '#e5c07b',
    str: '#98c379',
    punct: '#abb2bf'
  }

  const sectionTitle = (key, text) =>
    React.createElement('div', { key, style: { fontWeight: 600, marginBottom: '0.3rem', color: c.fg } }, text)

  const codePanel = (key, text, emptyText, foldState, setFoldState) =>
    renderIndentFoldedCode(key, text, emptyText, c, foldState, setFoldState)

  let content
  if (irState.state === 'resolved' && irState.value) {
    const decl = irState.value.declName || '<none>'
    const hasIR = !!irState.value.hasIR
    const irCode = typeof irState.value.irCode === 'string' ? irState.value.irCode : ''
    const lcnfCode = typeof irState.value.lcnfCode === 'string' ? irState.value.lcnfCode : ''
    content = React.createElement(
      React.Fragment,
      null,
      React.createElement(
        'div',
        {
          style: {
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'space-between',
            gap: '0.5rem',
            marginBottom: '0.55rem'
          }
        },
        React.createElement('div', { style: { fontWeight: 600, color: c.fg } }, decl),
        React.createElement(
          'span',
          {
            style: {
              padding: '0.1rem 0.45rem',
              borderRadius: '999px',
              fontSize: '0.8em',
              border: `1px solid ${hasIR ? c.ok : c.warn}`,
              color: hasIR ? c.ok : c.warn
            }
          },
          hasIR ? 'IR available' : 'No IR'
        )
      ),
      React.createElement('div', { style: { color: c.muted, marginBottom: '0.6rem' } }, irState.value.message || ''),
      sectionTitle('irTitle', 'IR'),
      codePanel('irCode', irCode, hasIR ? 'IR generation unavailable for this object.' : 'No IR for object at cursor.', irFoldState, setIrFoldState),
      React.createElement('div', { style: { height: '0.6rem' } }),
      sectionTitle('lcnfTitle', 'LCNF'),
      codePanel('lcnfCode', lcnfCode, hasIR ? 'LCNF generation unavailable for this object.' : 'No LCNF for object at cursor.', lcnfFoldState, setLcnfFoldState)
    )
  } else if (irState.state === 'rejected') {
    content = React.createElement(
      'div',
      { style: { marginTop: '0.5rem', color: c.err } },
      `IR check failed: ${mapRpcError(irState.error).message}`
    )
  } else {
    content = React.createElement('div', { style: { marginTop: '0.5rem', color: c.muted } }, 'Checking code at cursor...')
  }

  return React.createElement(
    'div',
    {
      style: {
        border: `1px solid ${c.border}`,
        borderRadius: '8px',
        marginTop: '0.4rem',
        overflow: 'hidden',
        background: c.bg
      }
    },
    React.createElement(
      'div',
      {
        style: {
          padding: '0.55rem 0.65rem',
          borderBottom: `1px solid ${c.border}`,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'space-between',
          background: 'linear-gradient(180deg, rgba(255,255,255,0.04), rgba(255,255,255,0))'
        }
      },
      React.createElement('div', { style: { fontWeight: 700, letterSpacing: '0.02em', color: c.fg } }, 'CE Code Inspector'),
      React.createElement('div', { style: { fontSize: '0.82em', color: c.muted } }, 'IR + LCNF')
    ),
    React.createElement(
      'div',
      { style: { padding: '0.65rem' } },
      content
    ),
    React.createElement(
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
  )
}
"#

/-- Panel widget that tracks the current cursor position in the Lean file. -/
@[widget_module]
abbrev clickPositionWidget : Widget.Module where
  javascript := widgetJs

end DevWidgets.CE
