/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Server.FileWorker.RequestHandling
public import Lean.Server.Rpc.RequestHandling
public import Lean.Compiler.IR
public import Lean.Compiler.Options
public import Lean.Compiler.LCNF.Main
public import Lean.Compiler.LCNF.ToDecl
public import Lean.Compiler.LCNF.PrettyPrinter
public import DevWidgets.Lib.AtPos
public section

namespace DevWidgets.CE

open Lean Widget Elab
open Lean Server

/-- Pretty-print options affecting only rendered IR/LCNF output (not compiler passes). -/
structure CEDisplayOptions where
  /-- `set_option pp.letVarTypes` -/
  ppLetVarTypes : Bool := false
  /-- `set_option pp.funBinderTypes` -/
  ppFunBinderTypes : Bool := false
  /-- `set_option pp.explicit` -/
  ppExplicit : Bool := false
  /-- `set_option pp.all` -/
  ppAll : Bool := false
  /-- `set_option pp.fullNames` -/
  ppFullNames : Bool := false
  /-- `set_option pp.privateNames` -/
  ppPrivateNames : Bool := false
  /-- `set_option pp.universes` -/
  ppUniverses : Bool := false
  deriving FromJson, ToJson

/-- Compiler options affecting code generation/reconstruction for CE. -/
structure CECompilerOptions where
  /-- Maps to `set_option compiler.reuse (!explicitRc)`.
  When `true`, CE asks for IR before reset/reuse expansion. -/
  explicitRc : Bool := false
  /-- `set_option compiler.extract_closed` -/
  compilerExtractClosed : Bool := true
  /-- `set_option compiler.check` -/
  compilerCheck : Bool := false
  /-- `set_option compiler.checkTypes` -/
  compilerCheckTypes : Bool := false
  /-- `set_option compiler.small` -/
  compilerSmall : Nat := 1
  /-- `set_option compiler.maxRecInline` -/
  compilerMaxRecInline : Nat := 1
  /-- `set_option compiler.maxRecInlineIfReduce` -/
  compilerMaxRecInlineIfReduce : Nat := 16
  /-- `set_option compiler.maxRecSpecialize` -/
  compilerMaxRecSpecialize : Nat := 64
  deriving FromJson, ToJson

/-- Request payload for CE analysis at cursor. -/
structure IRAtPosParams where
  pos : Lsp.Position
  display : CEDisplayOptions := {}
  compiler : CECompilerOptions := {}
  forceRecompile : Bool := false
  /--
  Compiler Explorer option (not a Lean compiler option):
  choose which LCNF reconstruction strategy to use when CE recompiles.
  -/
  lcnfRecompileViaPipeline : Bool := true
  deriving FromJson, ToJson

inductive CEOptionKind where
  | toggle
  | natChoice
  deriving FromJson, ToJson

/-- Declarative option schema so UI can be generated from backend metadata. -/
structure CEOptionDescriptor where
  id : String
  group : String
  label : String
  description : String
  leanOption : Name
  kind : CEOptionKind
  defaultBool? : Option Bool := none
  defaultNat? : Option Nat := none
  natChoices : Array Nat := #[]
  deriving FromJson, ToJson

structure CEOptionSchema where
  display : Array CEOptionDescriptor := #[]
  compiler : Array CEOptionDescriptor := #[]
  deriving FromJson, ToJson

structure CEOptionSchemaParams where
  deriving FromJson, ToJson

def ceOptionSchemaValue : CEOptionSchema := {
  display := #[
    {
      id := "ppLetVarTypes"
      group := "display"
      label := "LCNF let var types"
      description := "Include type annotations on let bindings."
      leanOption := `pp.letVarTypes
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppLetVarTypes
    },
    {
      id := "ppFunBinderTypes"
      group := "display"
      label := "LCNF binder types"
      description := "Include type annotations on function parameters."
      leanOption := `pp.funBinderTypes
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppFunBinderTypes
    },
    {
      id := "ppExplicit"
      group := "display"
      label := "Explicit arguments"
      description := "Show implicit arguments when available."
      leanOption := `pp.explicit
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppExplicit
    },
    {
      id := "ppAll"
      group := "display"
      label := "All details"
      description := "Include extra details in printed terms."
      leanOption := `pp.all
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppAll
    },
    {
      id := "ppFullNames"
      group := "display"
      label := "Full names"
      description := "Avoid abbreviated names in output."
      leanOption := `pp.fullNames
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppFullNames
    },
    {
      id := "ppPrivateNames"
      group := "display"
      label := "Private names"
      description := "Display private/internal names explicitly."
      leanOption := `pp.privateNames
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppPrivateNames
    },
    {
      id := "ppUniverses"
      group := "display"
      label := "Universes"
      description := "Include universe levels in names and types."
      leanOption := `pp.universes
      kind := .toggle
      defaultBool? := some ({} : CEDisplayOptions).ppUniverses
    }
  ]
  compiler := #[
    {
      id := "explicitRc"
      group := "compiler"
      label := "IR explicit RC"
      description := "Inspect pre reset/reuse-expansion IR."
      leanOption := `compiler.reuse
      kind := .toggle
      defaultBool? := some ({} : CECompilerOptions).explicitRc
    },
    {
      id := "compilerExtractClosed"
      group := "compiler"
      label := "Extract closed terms"
      description := "Cache/evaluate closed terms at initialization."
      leanOption := `compiler.extract_closed
      kind := .toggle
      defaultBool? := some ({} : CECompilerOptions).compilerExtractClosed
    },
    {
      id := "compilerCheck"
      group := "compiler"
      label := "Compiler step check"
      description := "Type-check code after compiler steps (debug)."
      leanOption := `compiler.check
      kind := .toggle
      defaultBool? := some ({} : CECompilerOptions).compilerCheck
    },
    {
      id := "compilerCheckTypes"
      group := "compiler"
      label := "LCNF type check"
      description := "Check type compatibility after LCNF passes (debug)."
      leanOption := `compiler.checkTypes
      kind := .toggle
      defaultBool? := some ({} : CECompilerOptions).compilerCheckTypes
    },
    {
      id := "compilerSmall"
      group := "compiler"
      label := "small"
      description := "Inline threshold for tiny declarations."
      leanOption := `compiler.small
      kind := .natChoice
      defaultNat? := some ({} : CECompilerOptions).compilerSmall
      natChoices := #[0, 1, 2, 4, 8]
    },
    {
      id := "compilerMaxRecInline"
      group := "compiler"
      label := "maxRecInline"
      description := "Max recursive inlining for [inline]."
      leanOption := `compiler.maxRecInline
      kind := .natChoice
      defaultNat? := some ({} : CECompilerOptions).compilerMaxRecInline
      natChoices := #[1, 2, 4, 8, 16]
    },
    {
      id := "compilerMaxRecInlineIfReduce"
      group := "compiler"
      label := "maxRecInlineIfReduce"
      description := "Max recursive inlining for [inline_if_reduce]."
      leanOption := `compiler.maxRecInlineIfReduce
      kind := .natChoice
      defaultNat? := some ({} : CECompilerOptions).compilerMaxRecInlineIfReduce
      natChoices := #[8, 16, 32, 64]
    },
    {
      id := "compilerMaxRecSpecialize"
      group := "compiler"
      label := "maxRecSpecialize"
      description := "Max recursive specialization depth."
      leanOption := `compiler.maxRecSpecialize
      kind := .natChoice
      defaultNat? := some ({} : CECompilerOptions).compilerMaxRecSpecialize
      natChoices := #[16, 32, 64, 128, 256]
    }
  ]
}

/-- Static metadata shared by the RPC and embedded frontend. -/
def CEDisplayOptions.schema : Array CEOptionDescriptor := ceOptionSchemaValue.display
def CECompilerOptions.schema : Array CEOptionDescriptor := ceOptionSchemaValue.compiler

namespace CECompilerOptions

/-- Read compiler option values from the current elaboration/context options. -/
def fromOptions (opts : Options) : CECompilerOptions := {
  explicitRc := !(opts.getBool `compiler.reuse true)
  compilerExtractClosed := opts.getBool `compiler.extract_closed true
  compilerCheck := opts.getBool `compiler.check false
  compilerCheckTypes := opts.getBool `compiler.checkTypes false
  compilerSmall := opts.get `compiler.small 1
  compilerMaxRecInline := opts.get `compiler.maxRecInline 1
  compilerMaxRecInlineIfReduce := opts.get `compiler.maxRecInlineIfReduce 16
  compilerMaxRecSpecialize := opts.get `compiler.maxRecSpecialize 64
}

end CECompilerOptions

def ceOptionSchemaImpl (_ : CEOptionSchemaParams) : RequestM (RequestTask CEOptionSchema) := do
  return RequestTask.pure ceOptionSchemaValue

/-- Structured code representation sent to UI.
`lines` keeps nested structure for rendering/folding/indentation workflows. -/
inductive CECodeRepr where
  | text (content : String)
  | lines (code : Array CECodeRepr)
  deriving FromJson, ToJson

namespace CECodeRepr

def toText : CECodeRepr → String
  | .text content => content
  | .lines code => String.intercalate "\n" <| (code.map toText).toList

end CECodeRepr

inductive CECodeOrigin where
  | localEnvironment
  | importedEnvironment
  /-- Stored code existed, but CE recompiled to honor non-default compiler options. -/
  | recompiledDueToOptions
  /-- Stored code existed, and CE recompiled because the user forced it. -/
  | recompiledForced
  /-- No stored code was available; CE compiled directly from declaration. -/
  | compiledFromScratch
  /-- No stored code and CE was already in forced-recompile mode (non-default options). -/
  | compiledFromScratchForced
  deriving FromJson, ToJson

/-- Options known to be used for this code representation. -/
structure CECodeOptions where
  /-- Pretty-printer options used to render this payload, when applicable. -/
  display? : Option CEDisplayOptions := none
  /-- Compiler options used to generate this payload, when applicable. -/
  compiler? : Option CECompilerOptions := none
  deriving FromJson, ToJson

/-- Explicit reasons for unavailability instead of plain `Option.none`. -/
inductive CECodeUnavailableReason where
  | notCompilableConstant
  | compilerDoesNotGenerateCode
  | notFoundInEnvironment
  | compilationReturnedNoCode
  | compilationFailed (message : String)
  deriving FromJson, ToJson

inductive CECodeResult where
  | available (content : CECodeRepr) (origin : CECodeOrigin) (options : CECodeOptions)
  | unavailable (reason : CECodeUnavailableReason)
  deriving FromJson, ToJson

namespace CECodeResult

def isAvailable : CECodeResult → Bool
  | .available .. => true
  | .unavailable .. => false

def text? : CECodeResult → Option String
  | .available content _ _ => some content.toText
  | .unavailable _ => none

def sourceLabel : CECodeResult → Option String
  | .available _ .localEnvironment _ => some "local environment"
  | .available _ .importedEnvironment _ => some "imported environment"
  | .available _ .recompiledDueToOptions _ => some "recompiled due to options"
  | .available _ .recompiledForced _ => some "recompiled (forced)"
  | .available _ .compiledFromScratch _ => some "compiled from scratch"
  | .available _ .compiledFromScratchForced _ => some "compiled from scratch (forced)"
  | .unavailable _ => none

def reasonLabel : CECodeUnavailableReason → String
  | .notCompilableConstant => "notCompilableConstant"
  | .compilerDoesNotGenerateCode => "compilerDoesNotGenerateCode"
  | .notFoundInEnvironment => "notFoundInEnvironment"
  | .compilationReturnedNoCode => "compilationReturnedNoCode"
  | .compilationFailed msg => s!"compilationFailed: {msg}"

end CECodeResult

/-- A compiler option change, independent of its presentation. -/
structure CEOptionDiff where
  id : String
  requested : Json
  context : Json
  deriving FromJson, ToJson

/-- Full analysis payload when a declaration exists under cursor. -/
structure CEDeclAnalysis where
  /-- Declaration selected for analysis (after helper fallback, if any). -/
  declName : Name
  /-- Raw declaration name from cursor hover info. -/
  cursorDeclName : Name
  ir : CECodeResult
  lcnf : CECodeResult
  /-- Compiler options that differ from cursor context and triggered recompilation. -/
  recompileOptionDiffs : Array CEOptionDiff := #[]
  usedHelperFallback : Bool := false
  forceRecompileRequested : Bool := false
  shouldGenerateError? : Option String := none
  deriving FromJson, ToJson

/-- RPC response is a sum type: either no declaration at cursor, or declaration analysis. -/
inductive IRAtPosResponse where
  | noDeclaration (message : String)
  | declaration (payload : CEDeclAnalysis)
  deriving FromJson, ToJson

/-- Conservative filter for declarations potentially handled by compiler pipeline.
Lean does not expose this check as a public helper. -/
private def mayCompileToCode (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ | .opaqueInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

private structure CEAnalysisConfig where
  display : CEDisplayOptions
  compiler : CECompilerOptions
  /-- Compiler options active in the cursor context (`info.ctx.options`). -/
  compilerContext : CECompilerOptions
  /-- Force recompilation independently of compiler option diffs. -/
  forceRecompileRequested : Bool := false
  /-- CE-only switch selecting cache-like vs direct LCNF reconstruction on recompile. -/
  lcnfRecompileViaPipeline : Bool := true

private def optionDiff [BEq α] [ToJson α] (id : String) (requested context : α) : Option CEOptionDiff :=
  if requested == context then none else some { id, requested := toJson requested, context := toJson context }

private def compilerOptionDiffs (requested context : CECompilerOptions) : Array CEOptionDiff :=
  #[
    optionDiff "explicitRc" requested.explicitRc context.explicitRc,
    optionDiff "compilerExtractClosed" requested.compilerExtractClosed context.compilerExtractClosed,
    optionDiff "compilerCheck" requested.compilerCheck context.compilerCheck,
    optionDiff "compilerCheckTypes" requested.compilerCheckTypes context.compilerCheckTypes,
    optionDiff "compilerSmall" requested.compilerSmall context.compilerSmall,
    optionDiff "compilerMaxRecInline" requested.compilerMaxRecInline context.compilerMaxRecInline,
    optionDiff "compilerMaxRecInlineIfReduce" requested.compilerMaxRecInlineIfReduce context.compilerMaxRecInlineIfReduce,
    optionDiff "compilerMaxRecSpecialize" requested.compilerMaxRecSpecialize context.compilerMaxRecSpecialize
  ].filterMap id

private def withDisplayOptions (display : CEDisplayOptions) (x : CoreM α) : CoreM α := do
  withOptions (fun opts =>
    let opts := opts.set `pp.letVarTypes display.ppLetVarTypes
    let opts := opts.set `pp.funBinderTypes display.ppFunBinderTypes
    let opts := opts.set `pp.explicit display.ppExplicit
    let opts := opts.set `pp.all display.ppAll
    let opts := opts.set `pp.fullNames display.ppFullNames
    let opts := opts.set `pp.privateNames display.ppPrivateNames
    let opts := opts.set `pp.universes display.ppUniverses
    opts
  ) x

private def withCompilerOptions (compiler : CECompilerOptions) (x : CoreM α) : CoreM α := do
  withOptions (fun opts =>
    let opts := opts.set `compiler.reuse (!compiler.explicitRc)
    let opts := opts.set `compiler.extract_closed compiler.compilerExtractClosed
    let opts := opts.set `compiler.check compiler.compilerCheck
    let opts := opts.set `compiler.checkTypes compiler.compilerCheckTypes
    let opts := opts.set `compiler.small compiler.compilerSmall
    let opts := opts.set `compiler.maxRecInline compiler.compilerMaxRecInline
    let opts := opts.set `compiler.maxRecInlineIfReduce compiler.compilerMaxRecInlineIfReduce
    let opts := opts.set `compiler.maxRecSpecialize compiler.compilerMaxRecSpecialize
    opts
  ) x

/--
`shouldGenerateCode` can throw for declarations missing expected compiler artifacts
(for example, missing LCNF signatures in some recursive/brec cases). We catch here
to keep CE resilient and expose details via `shouldGenerateError?` instead of failing RPC.
-/
private def shouldGenerateCodeResult (declName : Name) : CoreM (Bool × Option String) := do
  try
    return (← Lean.Compiler.LCNF.shouldGenerateCode declName, none)
  catch e =>
    return (false, some (← e.toMessageData.toString))

private def irDeclToCodeRepr (decl : Lean.IR.Decl) : CECodeRepr :=
  .text (toString decl)

private def lcnfDeclToCodeRepr (display : CEDisplayOptions) {p} (decl : Lean.Compiler.LCNF.Decl p) :
    CoreM CECodeRepr := do
  let fmt ← withDisplayOptions display <| Lean.Compiler.LCNF.ppDecl' decl .base
  return .text fmt.pretty

private def getStoredIRCode (declName : Name) : CoreM CECodeResult := do
  let env ← getEnv
  let local? ← (Lean.IR.findLocalDecl declName) <|> (Lean.IR.findLocalDecl (declName ++ `_boxed))
  if let some decl := local? then
    return .available (irDeclToCodeRepr decl) .localEnvironment {}
  let imported? :=
    Lean.IR.findEnvDecl env declName <|>
    Lean.IR.findEnvDecl env (declName ++ `_boxed)
  if let some decl := imported? then
    return .available (irDeclToCodeRepr decl) .importedEnvironment {}
  return .unavailable .notFoundInEnvironment

private def getStoredLCNFCode (display : CEDisplayOptions) (declName : Name) : CoreM CECodeResult := do
  try
    let localDecl? ← Lean.Compiler.LCNF.CompilerM.run <|
      Lean.Compiler.LCNF.getLocalDeclAt? declName .base
    if let some decl := localDecl? then
      let code ← lcnfDeclToCodeRepr display decl
      return .available code .localEnvironment { display? := some display }

    let importedDecl? ← Lean.Compiler.LCNF.getDeclAt? declName .base
    if let some decl := importedDecl? then
      let code ← lcnfDeclToCodeRepr display decl
      return .available code .importedEnvironment { display? := some display }

    return .unavailable .notFoundInEnvironment
  catch e =>
    return .unavailable (.compilationFailed (← e.toMessageData.toString))

/-- Run the compiler immediately, even in modules that postpone non-meta compilation. -/
private def compileForInspection (declName : Name) : CoreM Unit :=
  withOptions (Lean.Compiler.compiler.postponeCompile.set · false) do
    Lean.Compiler.LCNF.main #[declName] (← getOptions)

/-- Compile once, then read both representations from that invocation's environment. -/
private def compileCode (display : CEDisplayOptions) (compiler : CECompilerOptions)
    (viaPipeline : Bool) (declName : Name) (irOrigin lcnfOrigin : CECodeOrigin) :
    CoreM (CECodeResult × CECodeResult) := do
  let pipeline ← try
    let before := (Lean.IR.getDecls (← getEnv)).length
    withCompilerOptions compiler <| compileForInspection declName
    let allDecls := Lean.IR.getDecls (← getEnv)
    pure <| Except.ok (allDecls.take (allDecls.length - before)).reverse.toArray
  catch e => pure <| Except.error (← e.toMessageData.toString)
  let ir := match pipeline with
    | .error err => .unavailable (.compilationFailed err)
    | .ok decls =>
      if decls.isEmpty then .unavailable .compilationReturnedNoCode
      else .available (.lines (decls.map irDeclToCodeRepr)) irOrigin { compiler? := some compiler }
  let lcnf ← try
    if viaPipeline then
      if let .error err := pipeline then
        pure <| .unavailable (.compilationFailed err)
      else
        let localDecl? ← Lean.Compiler.LCNF.CompilerM.run do
          let direct? ← Lean.Compiler.LCNF.getLocalDeclAt? declName .base
          match direct? with
          | some decl => pure (some decl)
          | none => Lean.Compiler.LCNF.getLocalDeclAt? (declName ++ `_boxed) .base
        match localDecl? with
        | none => pure <| .unavailable .compilationReturnedNoCode
        | some decl =>
          let code ← lcnfDeclToCodeRepr display decl
          pure <| .available code lcnfOrigin { display? := some display, compiler? := some compiler }
    else
      let decl ← withCompilerOptions compiler <| Lean.Compiler.LCNF.CompilerM.run <| Lean.Compiler.LCNF.toDecl declName
      let code ← lcnfDeclToCodeRepr display decl
      pure <| .available code lcnfOrigin { display? := some display, compiler? := some compiler }
  catch e => pure <| .unavailable (.compilationFailed (← e.toMessageData.toString))
  return (ir, lcnf)

namespace Testing

/-- Exercise both recompilation paths, including when module compilation is postponed. -/
def recompile (declName : Name) (viaPipeline : Bool := true) : CoreM (CECodeResult × CECodeResult) := do
  withEnv (← getEnv) do
    compileCode {} {} viaPipeline declName .recompiledForced .recompiledForced

end Testing

private structure AnalysisResult where
  shouldGenerateError? : Option String := none
  recompileOptionDiffs : Array CEOptionDiff := #[]
  ir : CECodeResult := .unavailable .notCompilableConstant
  lcnf : CECodeResult := .unavailable .notCompilableConstant

private def analysisHasAnyCode (a : AnalysisResult) : Bool :=
  a.ir.isAvailable || a.lcnf.isAvailable

private def withShouldGenerateFallback (shouldGenerate : Bool) (code : CECodeResult) : CECodeResult :=
  if shouldGenerate then
    code
  else
    match code with
    | .unavailable .notFoundInEnvironment => .unavailable .compilerDoesNotGenerateCode
    | .unavailable .compilationReturnedNoCode => .unavailable .compilerDoesNotGenerateCode
    | _ => code

private def helperDeclParent? (declName : Name) : Option Name :=
  match declName with
  | .str p s =>
    if p == .anonymous then
      none
    else if s == "_sunfold" || s == "_unsafe_rec" || s.startsWith "match_" then
      some p
    else
      none
  | _ => none

/--
Analysis strategy:
1. Reject clearly non-compilable constants.
2. Prefer stored IR/LCNF from local compiler state and imported environment.
3. Force recompilation when compiler options differ from cursor context, or when explicitly requested.
4. Otherwise, fallback to recompilation only when stored code is missing.
5. Keep explicit unavailability reasons for UI/debugging.
-/
private def analyzeDecl (cfg : CEAnalysisConfig) (declName : Name) : CoreM AnalysisResult := do
  let env ← getEnv
  let maybeCompilable := (env.find? declName).map mayCompileToCode |>.getD false
  if !maybeCompilable then
    return {
      ir := .unavailable .notCompilableConstant
      lcnf := .unavailable .notCompilableConstant
    }

  let (shouldGenerate, shouldGenerateError?) ← shouldGenerateCodeResult declName

  let recompileOptionDiffs := compilerOptionDiffs cfg.compiler cfg.compilerContext
  let forceRecompile := cfg.forceRecompileRequested || !recompileOptionDiffs.isEmpty
  let recompiledOrigin : CECodeOrigin :=
    if cfg.forceRecompileRequested then .recompiledForced else .recompiledDueToOptions
  -- Capture both stored results before compilation mutates the inspection environment.
  let storedIR ← getStoredIRCode declName
  let storedLCNF ← getStoredLCNFCode cfg.display declName
  let needsIR := forceRecompile || !storedIR.isAvailable
  let needsLCNF := forceRecompile || !storedLCNF.isAvailable
  let origin (stored : CECodeResult) :=
    if forceRecompile then
      if stored.isAvailable then recompiledOrigin else .compiledFromScratchForced
    else .compiledFromScratch
  let (compiledIR, compiledLCNF) ←
    if needsIR || needsLCNF then
      compileCode cfg.display cfg.compiler cfg.lcnfRecompileViaPipeline declName
        (origin storedIR) (origin storedLCNF)
    else pure (storedIR, storedLCNF)
  let ir := if needsIR then compiledIR else storedIR
  let lcnf := if needsLCNF then compiledLCNF else storedLCNF

  let ir := withShouldGenerateFallback shouldGenerate ir
  let lcnf := withShouldGenerateFallback shouldGenerate lcnf

  return { shouldGenerateError?, recompileOptionDiffs, ir, lcnf }

private structure ResolvedDeclAnalysis where
  /-- Declaration ultimately used for analysis payload (`declName`). -/
  resolvedDeclName : Name
  /-- Result for `resolvedDeclName`. -/
  analysis : AnalysisResult
  /-- `true` if we switched from a helper declaration (e.g. `.match_1`) to its parent. -/
  usedHelperFallback : Bool

/--
Resolve cursor declaration into final declaration to display.
If the direct declaration has no code and looks like an equation-compiler helper,
we retry its parent declaration.
-/
private def resolveDeclAnalysis (cfg : CEAnalysisConfig) (declName : Name) :
    CoreM ResolvedDeclAnalysis := do
  let analysis ← analyzeDecl cfg declName
  if analysisHasAnyCode analysis then
    return { resolvedDeclName := declName, analysis, usedHelperFallback := false }
  let some parent := helperDeclParent? declName
    | return { resolvedDeclName := declName, analysis, usedHelperFallback := false }
  let parentAnalysis ← analyzeDecl cfg parent
  if analysisHasAnyCode parentAnalysis then
    return { resolvedDeclName := parent, analysis := parentAnalysis, usedHelperFallback := true }
  return { resolvedDeclName := declName, analysis, usedHelperFallback := false }

open Server RequestM
def irAtPosImpl (params : IRAtPosParams) : RequestM (RequestTask IRAtPosResponse) := do
  DevWidgets.Lib.withConstAtPos params.pos (global := false) fun constAt? => do
    let some constAt := constAt?
      | return .noDeclaration "No declaration under cursor."
    let snap := constAt.snap
    let declName := constAt.declName

    -- We intentionally use cursor-local context:
    -- * env: `info.ctx.env`
    -- * options: `info.ctx.options`
    -- so "recompiled due to options" is decided against the same context that
    -- produced the hovered declaration.
    let env := constAt.env
    let ctxCompiler := CECompilerOptions.fromOptions constAt.info.ctx.options
    let cfg : CEAnalysisConfig := {
      display := params.display
      compiler := params.compiler
      compilerContext := ctxCompiler
      forceRecompileRequested := params.forceRecompile
      lcnfRecompileViaPipeline := params.lcnfRecompileViaPipeline
    }
    let resolved ← RequestM.runCoreM snap do
      withEnv env do
        resolveDeclAnalysis cfg declName

    let resolvedDeclName := resolved.resolvedDeclName
    let analysis := resolved.analysis

    return .declaration {
      declName := resolvedDeclName
      cursorDeclName := declName
      ir := analysis.ir
      lcnf := analysis.lcnf
      recompileOptionDiffs := analysis.recompileOptionDiffs
      usedHelperFallback := resolved.usedHelperFallback
      forceRecompileRequested := params.forceRecompile
      shouldGenerateError? := analysis.shouldGenerateError?
    }

end DevWidgets.CE
