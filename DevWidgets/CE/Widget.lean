/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Widget.UserWidget
public import DevWidgets.CE.Analysis
public section

namespace DevWidgets.CE

open Lean Widget

def widgetJs : String := r#"
import * as React from 'react'
import { useAsync, useRpcSession, mapRpcError } from '@leanprover/infoview'

function fmtPos(pos) {
  if (!pos) return 'unknown'
  const file = typeof pos.uri === 'string' ? pos.uri.split('/').pop() : '<file>'
  return `${file}:${pos.line + 1}:${pos.character + 1}`
}

function decodeCodeContent(content) {
  if (!content || typeof content !== 'object') return ''
  if (content.text && typeof content.text === 'object' && typeof content.text.content === 'string') {
    return content.text.content
  }
  if (content.lines && typeof content.lines === 'object') {
    const xs = Array.isArray(content.lines.code)
      ? content.lines.code
      : (Array.isArray(content.lines.lines) ? content.lines.lines : [])
    return xs.map((x) => decodeCodeContent(x)).join('\n')
  }
  return ''
}

function decodeReason(reason) {
  if (typeof reason === 'string') return reason
  if (!reason || typeof reason !== 'object') return 'unknown'
  const ks = Object.keys(reason)
  if (ks.length === 0) return 'unknown'
  const k = ks[0]
  const v = reason[k]
  if (v && typeof v === 'object' && typeof v.message === 'string') return `${k}: ${v.message}`
  return `${k}: ${JSON.stringify(v)}`
}

function prettyUnavailableReason(reason) {
  if (typeof reason !== 'string' || reason.length === 0) return 'unknown'
  if (reason.startsWith('compilationFailed:')) {
    return reason.slice('compilationFailed:'.length).trim()
  }
  if (reason === 'compilerDoesNotGenerateCode') return 'compiler reports this declaration does not generate code'
  if (reason === 'notCompilableConstant') return 'declaration is not compilable to IR/LCNF'
  if (reason === 'notFoundInEnvironment') return 'code not found in local/imported environment'
  if (reason === 'compilationReturnedNoCode') return 'compiler returned no code for this declaration'
  return reason
}

function decodeCodeResult(result) {
  if (!result || typeof result !== 'object') {
    return { available: false, text: '', source: 'unavailable', reason: 'unknown' }
  }
  if (result.available && typeof result.available === 'object') {
    return {
      available: true,
      text: decodeCodeContent(result.available.content),
      source: typeof result.available.origin === 'string' ? result.available.origin : 'unknown',
      reason: ''
    }
  }
  if (result.unavailable && typeof result.unavailable === 'object') {
    return {
      available: false,
      text: '',
      source: 'unavailable',
      reason: decodeReason(result.unavailable.reason)
    }
  }
  return { available: false, text: '', source: 'unavailable', reason: 'unknown' }
}

function codeStatus(kind, result) {
  const k = typeof kind === 'string' ? kind : 'Code'
  if (!result?.available) {
    return { label: `${k}: unavailable`, tone: 'warn' }
  }
  switch (result.source) {
    case 'localEnvironment':
      return { label: `${k}: cached (local)`, tone: 'ok' }
    case 'importedEnvironment':
      return { label: `${k}: cached (imported)`, tone: 'ok' }
    case 'recompiledDueToOptions':
      return { label: `${k}: re-compiled (options)`, tone: 'warn' }
    case 'recompiledForced':
      return { label: `${k}: re-compiled (forced)`, tone: 'warn' }
    case 'compiledFromScratch':
      return { label: `${k}: compiled from scratch`, tone: 'muted' }
    case 'compiledFromScratchForced':
      return { label: `${k}: compiled from scratch (forced)`, tone: 'warn' }
    default:
      return { label: `${k}: available`, tone: 'ok' }
  }
}

function recompileTooltip(diffs) {
  if (!Array.isArray(diffs) || diffs.length === 0) return 'Recompiled due to compiler option differences.'
  const forced = diffs.includes('forced by header checkbox')
  const optionDiffs = diffs.filter((d) => d !== 'forced by header checkbox')
  if (forced && optionDiffs.length === 0) {
    return 'Recompiled because "Force recompilation" is enabled.'
  }
  if (forced) {
    return `Recompiled because "Force recompilation" is enabled.\nAdditional option differences:\n${optionDiffs.map((d) => `- ${d}`).join('\n')}`
  }
  return `Recompiled because these options differ from cursor context:\n${optionDiffs.map((d) => `- ${d}`).join('\n')}`
}

function shouldShowRecompileTooltip(source) {
  return source === 'recompiledDueToOptions' || source === 'recompiledForced' || source === 'compiledFromScratchForced'
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
  const [showAdvanced, setShowAdvanced] = React.useState(false)
  const [forceRecompile, setForceRecompile] = React.useState(false)
  const [lcnfRecompileViaPipeline, setLcnfRecompileViaPipeline] = React.useState(true)

  const fallbackSchema = React.useMemo(() => ({
    display: [
      { id: 'ppLetVarTypes', kind: 'toggle', label: 'LCNF let var types', description: 'Include type annotations on let bindings.', 'defaultBool?': false, leanOption: 'pp.letVarTypes' },
      { id: 'ppFunBinderTypes', kind: 'toggle', label: 'LCNF binder types', description: 'Include type annotations on function parameters.', 'defaultBool?': false, leanOption: 'pp.funBinderTypes' },
      { id: 'ppExplicit', kind: 'toggle', label: 'Explicit arguments', description: 'Show implicit arguments when available.', 'defaultBool?': false, leanOption: 'pp.explicit' },
      { id: 'ppAll', kind: 'toggle', label: 'All details', description: 'Include extra details in printed terms.', 'defaultBool?': false, leanOption: 'pp.all' },
      { id: 'ppFullNames', kind: 'toggle', label: 'Full names', description: 'Avoid abbreviated names in output.', 'defaultBool?': false, leanOption: 'pp.fullNames' },
      { id: 'ppPrivateNames', kind: 'toggle', label: 'Private names', description: 'Display private/internal names explicitly.', 'defaultBool?': false, leanOption: 'pp.privateNames' },
      { id: 'ppUniverses', kind: 'toggle', label: 'Universes', description: 'Include universe levels in names and types.', 'defaultBool?': false, leanOption: 'pp.universes' }
    ],
    compiler: [
      { id: 'explicitRc', kind: 'toggle', label: 'IR explicit RC', description: 'Inspect pre reset/reuse-expansion IR.', 'defaultBool?': false, leanOption: 'compiler.reuse' },
      { id: 'compilerExtractClosed', kind: 'toggle', label: 'Extract closed terms', description: 'Cache/evaluate closed terms at initialization.', 'defaultBool?': true, leanOption: 'compiler.extract_closed' },
      { id: 'compilerCheck', kind: 'toggle', label: 'Compiler step check', description: 'Type-check code after compiler steps (debug).', 'defaultBool?': false, leanOption: 'compiler.check' },
      { id: 'compilerCheckTypes', kind: 'toggle', label: 'LCNF type check', description: 'Check type compatibility after LCNF passes (debug).', 'defaultBool?': false, leanOption: 'compiler.checkTypes' },
      { id: 'compilerSmall', kind: 'natChoice', label: 'small', description: 'Inline threshold for tiny declarations.', 'defaultNat?': 1, natChoices: [0, 1, 2, 4, 8], leanOption: 'compiler.small' },
      { id: 'compilerMaxRecInline', kind: 'natChoice', label: 'maxRecInline', description: 'Max recursive inlining for [inline].', 'defaultNat?': 1, natChoices: [1, 2, 4, 8, 16], leanOption: 'compiler.maxRecInline' },
      { id: 'compilerMaxRecInlineIfReduce', kind: 'natChoice', label: 'maxRecInlineIfReduce', description: 'Max recursive inlining for [inline_if_reduce].', 'defaultNat?': 16, natChoices: [8, 16, 32, 64], leanOption: 'compiler.maxRecInlineIfReduce' },
      { id: 'compilerMaxRecSpecialize', kind: 'natChoice', label: 'maxRecSpecialize', description: 'Max recursive specialization depth.', 'defaultNat?': 64, natChoices: [16, 32, 64, 128, 256], leanOption: 'compiler.maxRecSpecialize' }
    ]
  }), [])

  const schemaState = useAsync(async () => {
    return await rs.call('DevWidgets.CE.ceOptionSchema', {})
  }, [rs])

  const schemaValue = (schemaState.state === 'resolved' && schemaState.value) ? schemaState.value : fallbackSchema
  const displayDescriptors = Array.isArray(schemaValue?.display) ? schemaValue.display : fallbackSchema.display
  const compilerDescriptors = Array.isArray(schemaValue?.compiler) ? schemaValue.compiler : fallbackSchema.compiler
  const allDescriptors = [...displayDescriptors, ...compilerDescriptors]

  const descriptorDefaults = React.useMemo(() => {
    const out = {}
    for (const d of allDescriptors) {
      if (!d || typeof d !== 'object' || typeof d.id !== 'string') continue
      if (d.kind === 'toggle') {
        out[d.id] = !!d['defaultBool?']
      } else if (d.kind === 'natChoice') {
        const choices = Array.isArray(d.natChoices) ? d.natChoices.map((n) => Number(n)).filter(Number.isFinite) : []
        const def = Number.isFinite(Number(d['defaultNat?'])) ? Number(d['defaultNat?']) : (choices.length > 0 ? choices[0] : 0)
        out[d.id] = def
      }
    }
    return out
  }, [allDescriptors])

  const [optionValues, setOptionValues] = React.useState({
    explicitRc: false,
    ppLetVarTypes: false,
    ppFunBinderTypes: false,
    ppExplicit: false,
    ppAll: false,
    ppFullNames: false,
    ppPrivateNames: false,
    ppUniverses: false,
    compilerExtractClosed: true,
    compilerCheck: false,
    compilerCheckTypes: false,
    compilerSmall: 1,
    compilerMaxRecInline: 1,
    compilerMaxRecInlineIfReduce: 16,
    compilerMaxRecSpecialize: 64
  })

  React.useEffect(() => {
    if (allDescriptors.length === 0) return
    setOptionValues((prev) => {
      let changed = false
      const next = { ...prev }
      for (const [k, v] of Object.entries(descriptorDefaults)) {
        if (next[k] === undefined) {
          next[k] = v
          changed = true
        }
      }
      return changed ? next : prev
    })
  }, [allDescriptors.length, descriptorDefaults])

  const getBool = (id, fallback = false) => {
    const v = optionValues[id]
    return typeof v === 'boolean' ? v : fallback
  }
  const getNat = (id, fallback = 0) => {
    const n = Number(optionValues[id])
    return Number.isFinite(n) ? n : fallback
  }

  const explicitRc = getBool('explicitRc', false)
  const ppLetVarTypes = getBool('ppLetVarTypes', false)
  const ppFunBinderTypes = getBool('ppFunBinderTypes', false)
  const ppExplicit = getBool('ppExplicit', false)
  const ppAll = getBool('ppAll', false)
  const ppFullNames = getBool('ppFullNames', false)
  const ppPrivateNames = getBool('ppPrivateNames', false)
  const ppUniverses = getBool('ppUniverses', false)
  const compilerExtractClosed = getBool('compilerExtractClosed', true)
  const compilerCheck = getBool('compilerCheck', false)
  const compilerCheckTypes = getBool('compilerCheckTypes', false)
  const compilerSmall = getNat('compilerSmall', 1)
  const compilerMaxRecInline = getNat('compilerMaxRecInline', 1)
  const compilerMaxRecInlineIfReduce = getNat('compilerMaxRecInlineIfReduce', 16)
  const compilerMaxRecSpecialize = getNat('compilerMaxRecSpecialize', 64)

  const irState = useAsync(async () => {
    if (!props?.pos) return undefined
    const params = {
      pos: props.pos,
      forceRecompile,
      lcnfRecompileViaPipeline,
      display: {
        ppLetVarTypes,
        ppFunBinderTypes,
        ppExplicit,
        ppAll,
        ppFullNames,
        ppPrivateNames,
        ppUniverses
      },
      compiler: {
        explicitRc,
        compilerExtractClosed,
        compilerCheck,
        compilerCheckTypes,
        compilerSmall,
        compilerMaxRecInline,
        compilerMaxRecInlineIfReduce,
        compilerMaxRecSpecialize
      }
    }
    return await rs.call('DevWidgets.CE.irAtPos', params)
  }, [
    rs,
    props?.pos?.uri,
    props?.pos?.line,
    props?.pos?.character,
    forceRecompile,
    lcnfRecompileViaPipeline,
    explicitRc,
    ppLetVarTypes,
    ppFunBinderTypes,
    ppExplicit,
    ppAll,
    ppFullNames,
    ppPrivateNames,
    ppUniverses,
    compilerExtractClosed,
    compilerCheck,
    compilerCheckTypes,
    compilerSmall,
    compilerMaxRecInline,
    compilerMaxRecInlineIfReduce,
    compilerMaxRecSpecialize
  ])

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

  const optionsCardStyle = {
    marginBottom: '0.65rem',
    border: `1px solid ${c.border}`,
    borderRadius: '6px',
    background: c.panel,
    padding: '0.5rem 0.6rem'
  }

  const optionGridStyle = {
    display: 'grid',
    gridTemplateColumns: 'repeat(auto-fit, minmax(15rem, 1fr))',
    gap: '0.45rem 0.85rem'
  }

  const advancedGridStyle = {
    display: 'grid',
    gridTemplateColumns: 'repeat(auto-fit, minmax(16rem, 1fr))',
    gap: '0.45rem 0.85rem'
  }

  const optionLabelStyle = {
    display: 'flex',
    alignItems: 'flex-start',
    gap: '0.45rem',
    color: c.fg
  }

  const optionTitleStyle = {
    fontSize: '0.88em',
    fontWeight: 600,
    lineHeight: 1.2
  }

  const optionHintStyle = {
    fontSize: '0.8em',
    color: c.muted,
    lineHeight: 1.25,
    marginTop: '0.08rem'
  }

  const selectStyle = {
    marginTop: '0.15rem',
    borderRadius: '4px',
    border: `1px solid ${c.border}`,
    background: c.bg,
    color: c.fg,
    padding: '0.12rem 0.3rem',
    fontSize: '0.84em'
  }

  const optionsHeaderStyle = {
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'space-between',
    gap: '0.5rem',
    marginBottom: '0.45rem'
  }

  const optionsHeadingStyle = {
    fontSize: '0.84em',
    fontWeight: 700,
    letterSpacing: '0.01em',
    color: c.muted
  }

  const controlsRowStyle = {
    display: 'flex',
    flexWrap: 'wrap',
    alignItems: 'center',
    gap: '0.35rem'
  }

  const smallButtonStyle = {
    borderRadius: '5px',
    border: `1px solid ${c.border}`,
    background: c.bg,
    color: c.fg,
    padding: '0.1rem 0.35rem',
    fontSize: '0.78em',
    cursor: 'pointer'
  }

  const advancedSectionStyle = {
    marginTop: '0.5rem',
    paddingTop: '0.45rem',
    borderTop: `1px dashed ${c.border}`
  }

  const sectionHeaderStyle = {
    fontSize: '0.8em',
    fontWeight: 700,
    color: c.muted,
    marginBottom: '0.35rem'
  }

  const inputStyle = { marginTop: '0.08rem' }

  const renderOptionToggle = (title, hint, checked, onChange, tooltip) =>
    React.createElement(
      'label',
      { style: optionLabelStyle, title: tooltip || '' },
      React.createElement('input', {
        type: 'checkbox',
        checked,
        onChange: (e) => onChange(!!e.target.checked),
        style: inputStyle
      }),
      React.createElement(
        'span',
        null,
        React.createElement('div', { style: optionTitleStyle }, title),
        React.createElement('div', { style: optionHintStyle }, hint)
      )
    )

  const renderSelectOption = (title, hint, value, onChange, choices, tooltip) =>
    React.createElement(
      'label',
      { style: optionLabelStyle, title: tooltip || '' },
      React.createElement(
        'span',
        null,
        React.createElement('div', { style: optionTitleStyle }, title),
        React.createElement('div', { style: optionHintStyle }, hint),
        React.createElement(
          'select',
          {
            value: String(value),
            onChange: (e) => onChange(Number(e.target.value)),
            style: selectStyle
          },
          ...choices.map((n) =>
            React.createElement('option', { key: `${title}-${n}`, value: String(n) }, `${n}`)
          )
        )
      )
    )

  const descriptorById = new Map(allDescriptors
    .filter((d) => d && typeof d.id === 'string')
    .map((d) => [d.id, d]))

  const setOption = (id, value) => {
    setOptionValues((prev) => ({ ...prev, [id]: value }))
  }

  const renderDescriptor = (desc) => {
    if (!desc || typeof desc.id !== 'string') return null
    const title = typeof desc.label === 'string' && desc.label.length > 0 ? desc.label : desc.id
    const hint = typeof desc.description === 'string' ? desc.description : ''
    const tooltip = (typeof desc.leanOption === 'string' && (desc.leanOption.startsWith('pp.') || desc.leanOption.startsWith('compiler.')))
      ? `set_option ${desc.leanOption}`
      : ''
    if (desc.kind === 'natChoice') {
      const choices = Array.isArray(desc.natChoices)
        ? desc.natChoices.map((n) => Number(n)).filter(Number.isFinite)
        : []
      const fallback = Number.isFinite(Number(desc['defaultNat?']))
        ? Number(desc['defaultNat?'])
        : (choices.length > 0 ? choices[0] : 0)
      return renderSelectOption(
        title,
        hint,
        getNat(desc.id, fallback),
        (v) => setOption(desc.id, Number(v)),
        choices.length > 0 ? choices : [fallback],
        tooltip
      )
    }
    return renderOptionToggle(
      title,
      hint,
      getBool(desc.id, !!desc['defaultBool?']),
      (v) => setOption(desc.id, !!v),
      tooltip
    )
  }

  const pickDescriptors = (ids) => ids
    .map((id) => descriptorById.get(id))
    .filter((d) => !!d)

  const primaryDisplayDescriptors = pickDescriptors(['ppLetVarTypes', 'ppFunBinderTypes'])
  const primaryCompilerDescriptors = pickDescriptors(['explicitRc'])
  const prettyDescriptors = pickDescriptors(['ppExplicit', 'ppAll', 'ppFullNames', 'ppPrivateNames', 'ppUniverses'])
  const checkDescriptors = pickDescriptors(['compilerExtractClosed', 'compilerCheck', 'compilerCheckTypes'])
  const heuristicDescriptors = pickDescriptors(['compilerSmall', 'compilerMaxRecInline', 'compilerMaxRecInlineIfReduce', 'compilerMaxRecSpecialize'])

  const setLeanDefaults = () => {
    setOptionValues((prev) => ({ ...prev, ...descriptorDefaults }))
  }

  const setVerbosePreset = () => {
    setOptionValues((prev) => ({
      ...prev,
      ...descriptorDefaults,
      explicitRc: true,
      ppLetVarTypes: true,
      ppFunBinderTypes: true,
      ppExplicit: true,
      ppAll: true,
      ppFullNames: true,
      ppPrivateNames: true,
      ppUniverses: true,
      compilerExtractClosed: true,
      compilerCheck: false,
      compilerCheckTypes: false,
      compilerSmall: 2,
      compilerMaxRecInline: 2,
      compilerMaxRecInlineIfReduce: 32,
      compilerMaxRecSpecialize: 128
    }))
  }

  let content
  if (irState.state === 'resolved' && irState.value) {
    const declaration = (irState.value.declaration && (irState.value.declaration.payload || irState.value.declaration)) || null
    const noDeclarationMsg = irState.value.noDeclaration && irState.value.noDeclaration.message
    if (!declaration) {
      content = React.createElement(
        'div',
        { style: { marginTop: '0.5rem', color: c.muted, whiteSpace: 'pre-wrap' } },
        typeof noDeclarationMsg === 'string' ? noDeclarationMsg : 'No declaration under cursor.'
      )
    } else {
      const decl = typeof declaration.declName === 'string' ? declaration.declName : '<none>'
      const hasIR = !!declaration.hasIR
      const usedHelperFallback = !!declaration.usedHelperFallback
      const irResult = decodeCodeResult(declaration.ir)
      const lcnfResult = decodeCodeResult(declaration.lcnf)
      const irStatus = codeStatus('IR', irResult)
      const lcnfStatus = codeStatus('LCNF', lcnfResult)
      const helperStatus = usedHelperFallback
        ? `Resolved helper '${declaration.cursorDeclName || decl}' to '${decl}'.`
        : ''
      const irCode = irResult.text
      const lcnfCode = lcnfResult.text
      const recompileDiffs = Array.isArray(declaration.recompileOptionDiffs)
        ? declaration.recompileOptionDiffs.filter((s) => typeof s === 'string' && s.length > 0)
        : []
      const recompileHint = recompileTooltip(recompileDiffs)
      const debugInfo = Array.isArray(declaration.debugInfo)
        ? declaration.debugInfo.filter((s) => typeof s === 'string' && s.length > 0)
        : []
      const relevantDebug = (kind) =>
        debugInfo.filter((line) =>
          line.startsWith('shouldGenerateError=') ||
          line.startsWith(`${kind.toLowerCase()}CompileError=`) ||
          line.startsWith('resolvedDecl=') ||
          line.startsWith('forcedRecompile=')
        )
      const badgeStyle = (tone) => {
        let col = c.muted
        if (tone === 'ok') col = c.ok
        else if (tone === 'warn') col = c.warn
        else if (tone === 'err') col = c.err
        return {
          padding: '0.1rem 0.45rem',
          borderRadius: '999px',
          fontSize: '0.8em',
          border: `1px solid ${col}`,
          color: col,
          whiteSpace: 'nowrap'
        }
      }
      const unavailableText = (kind, result) => {
        const lines = []
        lines.push(`${kind} unavailable for '${decl}'.`)
        lines.push(`cause: ${prettyUnavailableReason(result.reason)}`)
        lines.push(`status=${kind === 'IR' ? irStatus.label : lcnfStatus.label}`)
        if (helperStatus.length > 0) lines.push(helperStatus)
        const details = relevantDebug(kind)
        if (details.length > 0) {
          lines.push('details:')
          lines.push(...details)
        }
        return lines.join('\n')
      }
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
          React.createElement(
            'div',
            { style: { display: 'flex', alignItems: 'center', gap: '0.45rem', minWidth: 0, flexWrap: 'wrap' } },
            React.createElement('div', { style: { fontWeight: 600, color: c.fg, whiteSpace: 'nowrap' } }, decl),
            usedHelperFallback
              ? React.createElement('span', { style: badgeStyle('muted') }, 'helper fallback')
              : null,
            React.createElement('span', { style: badgeStyle(hasIR ? 'ok' : 'warn') }, hasIR ? 'IR available' : 'No IR'),
            React.createElement(
              'span',
              {
                style: badgeStyle(irStatus.tone),
                title: shouldShowRecompileTooltip(irResult.source) ? recompileHint : ''
              },
              irStatus.label
            ),
            React.createElement(
              'span',
              {
                style: badgeStyle(lcnfStatus.tone),
                title: shouldShowRecompileTooltip(lcnfResult.source) ? recompileHint : ''
              },
              lcnfStatus.label
            )
          ),
          helperStatus.length > 0
            ? React.createElement('div', { style: { color: c.muted, fontSize: '0.82em', textAlign: 'right' } }, helperStatus)
            : null
        ),
        React.createElement(
          'div',
          {
            style: {
              ...optionsCardStyle
            }
          },
          React.createElement(
            'div',
            { style: optionsHeaderStyle },
            React.createElement('div', { style: optionsHeadingStyle }, 'Inspector options'),
            React.createElement(
              'div',
              { style: controlsRowStyle },
              React.createElement(
                'button',
                { type: 'button', onClick: setLeanDefaults, style: smallButtonStyle, title: 'Restore Lean defaults.' },
                'Defaults'
              ),
              React.createElement(
                'button',
                { type: 'button', onClick: setVerbosePreset, style: smallButtonStyle, title: 'Apply a verbose debugging preset.' },
                'Verbose'
              ),
              React.createElement(
                'button',
                {
                  type: 'button',
                  onClick: () => setShowAdvanced((x) => !x),
                  style: smallButtonStyle,
                  title: 'Toggle advanced compiler and pretty-printer options.'
                },
                showAdvanced ? 'Hide advanced' : 'Show advanced'
              )
            )
          ),
          React.createElement('div', { style: sectionHeaderStyle }, 'Display (render output only)'),
          React.createElement(
            'div',
            { style: optionGridStyle },
            ...primaryDisplayDescriptors.map((d) => React.createElement(React.Fragment, { key: `primary-display-${d.id}` }, renderDescriptor(d)))
          ),
          React.createElement('div', { style: { ...sectionHeaderStyle, marginTop: '0.4rem' } }, 'Compiler (can trigger recompilation)'),
          React.createElement(
            'div',
            { style: optionGridStyle },
            ...primaryCompilerDescriptors.map((d) => React.createElement(React.Fragment, { key: `primary-compiler-${d.id}` }, renderDescriptor(d)))
          ),
          showAdvanced ? React.createElement(
            'div',
            { style: advancedSectionStyle },
            React.createElement('div', { style: sectionHeaderStyle }, 'Pretty-printer'),
            React.createElement(
              'div',
              { style: advancedGridStyle },
              ...prettyDescriptors.map((d) => React.createElement(React.Fragment, { key: `pretty-${d.id}` }, renderDescriptor(d)))
            ),
            React.createElement('div', { style: { ...sectionHeaderStyle, marginTop: '0.5rem' } }, 'Compiler checks'),
            React.createElement(
              'div',
              { style: advancedGridStyle },
              ...checkDescriptors.map((d) => React.createElement(React.Fragment, { key: `check-${d.id}` }, renderDescriptor(d)))
            ),
            React.createElement('div', { style: { ...sectionHeaderStyle, marginTop: '0.5rem' } }, 'Compiler heuristics'),
            React.createElement(
              'div',
              { style: advancedGridStyle },
              ...heuristicDescriptors.map((d) => React.createElement(React.Fragment, { key: `heur-${d.id}` }, renderDescriptor(d)))
            )
          ) : null,
          React.createElement(
            'div',
            {
              style: {
                fontSize: '0.79em',
                color: c.muted,
                marginTop: '0.5rem'
              }
            },
            'Display options are server pretty-printer settings; compiler options change code generation and may force recompilation.'
          )
        ),
        sectionTitle('irTitle', 'IR'),
        codePanel('irCode', irCode, unavailableText('IR', irResult), irFoldState, setIrFoldState),
        React.createElement('div', { style: { height: '0.6rem' } }),
        sectionTitle('lcnfTitle', 'LCNF'),
        codePanel('lcnfCode', lcnfCode, unavailableText('LCNF', lcnfResult), lcnfFoldState, setLcnfFoldState)
      )
    }
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
      React.createElement('div', { style: { fontWeight: 700, letterSpacing: '0.02em', color: c.fg } }, 'Compiler Explorer'),
      React.createElement(
        'div',
        { style: { display: 'flex', alignItems: 'center', gap: '0.75rem' } },
        React.createElement('div', { style: { fontSize: '0.82em', color: c.muted } }, 'IR and LCNF at cursor'),
        React.createElement(
          'label',
          {
            style: {
              display: 'flex',
              alignItems: 'center',
              gap: '0.35rem',
              fontSize: '0.8em',
              color: c.muted,
              cursor: 'pointer',
              userSelect: 'none'
            },
            title: 'Force recompilation regardless of cached code and option diffs.'
          },
          React.createElement('input', {
            type: 'checkbox',
            checked: forceRecompile,
            onChange: (e) => setForceRecompile(!!e.target.checked)
          }),
          'Force recompilation'
        ),
        React.createElement(
          'label',
          {
            style: {
              display: 'flex',
              alignItems: 'center',
              gap: '0.35rem',
              fontSize: '0.8em',
              color: c.muted,
              cursor: 'pointer',
              userSelect: 'none'
            },
            title: 'When recompiling LCNF, use cache-like compiler pipeline instead of direct toDecl reconstruction.'
          },
          React.createElement('input', {
            type: 'checkbox',
            checked: lcnfRecompileViaPipeline,
            onChange: (e) => setLcnfRecompileViaPipeline(!!e.target.checked)
          }),
          'LCNF cache-like pipeline'
        )
      )
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
abbrev compilerExplorerWidget : Widget.Module where
  javascript := widgetJs

end DevWidgets.CE
