/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module

public import Lean.Server.FileWorker.RequestHandling
public import Lean.Server.Rpc.RequestHandling
public import Lean.Compiler.IR
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

/-- Canonical option representation pairing concrete value and descriptor metadata. -/
structure CEOptionDecl (α : Type) where
  value : α
  schema : CEOptionDescriptor
  deriving FromJson, ToJson

structure CEOptionSchema where
  display : Array CEOptionDescriptor := #[]
  compiler : Array CEOptionDescriptor := #[]
  deriving FromJson, ToJson

structure CEOptionSchemaParams where
  deriving FromJson, ToJson

private def ceOptionSchemaValue : CEOptionSchema := {
  display := #[
    {
      id := "ppLetVarTypes"
      group := "display"
      label := "LCNF let var types"
      description := "Include type annotations on let bindings."
      leanOption := `pp.letVarTypes
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "ppFunBinderTypes"
      group := "display"
      label := "LCNF binder types"
      description := "Include type annotations on function parameters."
      leanOption := `pp.funBinderTypes
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "ppExplicit"
      group := "display"
      label := "Explicit arguments"
      description := "Show implicit arguments when available."
      leanOption := `pp.explicit
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "ppAll"
      group := "display"
      label := "All details"
      description := "Include extra details in printed terms."
      leanOption := `pp.all
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "ppFullNames"
      group := "display"
      label := "Full names"
      description := "Avoid abbreviated names in output."
      leanOption := `pp.fullNames
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "ppPrivateNames"
      group := "display"
      label := "Private names"
      description := "Display private/internal names explicitly."
      leanOption := `pp.privateNames
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "ppUniverses"
      group := "display"
      label := "Universes"
      description := "Include universe levels in names and types."
      leanOption := `pp.universes
      kind := .toggle
      defaultBool? := some false
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
      defaultBool? := some false
    },
    {
      id := "compilerExtractClosed"
      group := "compiler"
      label := "Extract closed terms"
      description := "Cache/evaluate closed terms at initialization."
      leanOption := `compiler.extract_closed
      kind := .toggle
      defaultBool? := some true
    },
    {
      id := "compilerCheck"
      group := "compiler"
      label := "Compiler step check"
      description := "Type-check code after compiler steps (debug)."
      leanOption := `compiler.check
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "compilerCheckTypes"
      group := "compiler"
      label := "LCNF type check"
      description := "Check type compatibility after LCNF passes (debug)."
      leanOption := `compiler.checkTypes
      kind := .toggle
      defaultBool? := some false
    },
    {
      id := "compilerSmall"
      group := "compiler"
      label := "small"
      description := "Inline threshold for tiny declarations."
      leanOption := `compiler.small
      kind := .natChoice
      defaultNat? := some 1
      natChoices := #[0, 1, 2, 4, 8]
    },
    {
      id := "compilerMaxRecInline"
      group := "compiler"
      label := "maxRecInline"
      description := "Max recursive inlining for [inline]."
      leanOption := `compiler.maxRecInline
      kind := .natChoice
      defaultNat? := some 1
      natChoices := #[1, 2, 4, 8, 16]
    },
    {
      id := "compilerMaxRecInlineIfReduce"
      group := "compiler"
      label := "maxRecInlineIfReduce"
      description := "Max recursive inlining for [inline_if_reduce]."
      leanOption := `compiler.maxRecInlineIfReduce
      kind := .natChoice
      defaultNat? := some 16
      natChoices := #[8, 16, 32, 64]
    },
    {
      id := "compilerMaxRecSpecialize"
      group := "compiler"
      label := "maxRecSpecialize"
      description := "Max recursive specialization depth."
      leanOption := `compiler.maxRecSpecialize
      kind := .natChoice
      defaultNat? := some 64
      natChoices := #[16, 32, 64, 128, 256]
    }
  ]
}

private def fallbackDescriptor (group id : String) : CEOptionDescriptor := {
  id := id
  group := group
  label := id
  description := ""
  leanOption := .anonymous
  kind := .toggle
}

private def findDescriptor (group : String) (descs : Array CEOptionDescriptor) (id : String) :
    CEOptionDescriptor :=
  (descs.find? (fun d => d.id == id)).getD (fallbackDescriptor group id)

structure CEDisplayOptionDecls where
  ppLetVarTypes : CEOptionDecl Bool
  ppFunBinderTypes : CEOptionDecl Bool
  ppExplicit : CEOptionDecl Bool
  ppAll : CEOptionDecl Bool
  ppFullNames : CEOptionDecl Bool
  ppPrivateNames : CEOptionDecl Bool
  ppUniverses : CEOptionDecl Bool
  deriving FromJson, ToJson

structure CECompilerOptionDecls where
  explicitRc : CEOptionDecl Bool
  compilerExtractClosed : CEOptionDecl Bool
  compilerCheck : CEOptionDecl Bool
  compilerCheckTypes : CEOptionDecl Bool
  compilerSmall : CEOptionDecl Nat
  compilerMaxRecInline : CEOptionDecl Nat
  compilerMaxRecInlineIfReduce : CEOptionDecl Nat
  compilerMaxRecSpecialize : CEOptionDecl Nat
  deriving FromJson, ToJson

namespace CEDisplayOptions

/-- Canonical schema metadata for display options. -/
def schema : Array CEOptionDescriptor := ceOptionSchemaValue.display

def toDecls (opts : CEDisplayOptions) : CEDisplayOptionDecls := {
  ppLetVarTypes := {
    value := opts.ppLetVarTypes
    schema := findDescriptor "display" schema "ppLetVarTypes"
  }
  ppFunBinderTypes := {
    value := opts.ppFunBinderTypes
    schema := findDescriptor "display" schema "ppFunBinderTypes"
  }
  ppExplicit := {
    value := opts.ppExplicit
    schema := findDescriptor "display" schema "ppExplicit"
  }
  ppAll := {
    value := opts.ppAll
    schema := findDescriptor "display" schema "ppAll"
  }
  ppFullNames := {
    value := opts.ppFullNames
    schema := findDescriptor "display" schema "ppFullNames"
  }
  ppPrivateNames := {
    value := opts.ppPrivateNames
    schema := findDescriptor "display" schema "ppPrivateNames"
  }
  ppUniverses := {
    value := opts.ppUniverses
    schema := findDescriptor "display" schema "ppUniverses"
  }
}

end CEDisplayOptions

namespace CECompilerOptions

/-- Canonical schema metadata for compiler options. -/
def schema : Array CEOptionDescriptor := ceOptionSchemaValue.compiler

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

def toDecls (opts : CECompilerOptions) : CECompilerOptionDecls := {
  explicitRc := {
    value := opts.explicitRc
    schema := findDescriptor "compiler" schema "explicitRc"
  }
  compilerExtractClosed := {
    value := opts.compilerExtractClosed
    schema := findDescriptor "compiler" schema "compilerExtractClosed"
  }
  compilerCheck := {
    value := opts.compilerCheck
    schema := findDescriptor "compiler" schema "compilerCheck"
  }
  compilerCheckTypes := {
    value := opts.compilerCheckTypes
    schema := findDescriptor "compiler" schema "compilerCheckTypes"
  }
  compilerSmall := {
    value := opts.compilerSmall
    schema := findDescriptor "compiler" schema "compilerSmall"
  }
  compilerMaxRecInline := {
    value := opts.compilerMaxRecInline
    schema := findDescriptor "compiler" schema "compilerMaxRecInline"
  }
  compilerMaxRecInlineIfReduce := {
    value := opts.compilerMaxRecInlineIfReduce
    schema := findDescriptor "compiler" schema "compilerMaxRecInlineIfReduce"
  }
  compilerMaxRecSpecialize := {
    value := opts.compilerMaxRecSpecialize
    schema := findDescriptor "compiler" schema "compilerMaxRecSpecialize"
  }
}

end CECompilerOptions

private def ceOptionSchemaImpl (_ : CEOptionSchemaParams) : RequestM (RequestTask CEOptionSchema) := do
  return RequestTask.pure ceOptionSchemaValue

@[implemented_by ceOptionSchemaImpl]
meta opaque ceOptionSchema (_ : CEOptionSchemaParams) : RequestM (RequestTask CEOptionSchema)

attribute [server_rpc_method] ceOptionSchema

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
  display? : Option CEDisplayOptionDecls := none
  /-- Compiler options used to generate this payload, when applicable. -/
  compiler? : Option CECompilerOptionDecls := none
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

/-- Full analysis payload when a declaration exists under cursor. -/
structure CEDeclAnalysis where
  /-- Declaration selected for analysis (after helper fallback, if any). -/
  declName : Name
  /-- Raw declaration name from cursor hover info. -/
  cursorDeclName : Name
  /-- Whether the compiler considers this declaration code-generatable. -/
  hasIR : Bool
  ir : CECodeResult
  lcnf : CECodeResult
  /-- Compiler options that differ from cursor context and triggered recompilation. -/
  recompileOptionDiffs : Array String := #[]
  usedHelperFallback : Bool := false
  debugInfo : Array String := #[]
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

structure CEAnalysisConfig where
  display : CEDisplayOptionDecls
  compiler : CECompilerOptionDecls
  /-- Compiler options active in the cursor context (`info.ctx.options`). -/
  compilerContext : CECompilerOptionDecls
  /-- Force recompilation independently of compiler option diffs. -/
  forceRecompileRequested : Bool := false
  /-- CE-only switch selecting cache-like vs direct LCNF reconstruction on recompile. -/
  lcnfRecompileViaPipeline : Bool := true

private def optionDiff [BEq α] [ToString α] (requested context : CEOptionDecl α) : Option String :=
  if requested.value == context.value then
    none
  else
    some s!"{requested.schema.id}: requested={requested.value}, context={context.value}"

private def compilerOptionDiffs (requested context : CECompilerOptionDecls) : Array String :=
  #[
    optionDiff requested.explicitRc context.explicitRc,
    optionDiff requested.compilerExtractClosed context.compilerExtractClosed,
    optionDiff requested.compilerCheck context.compilerCheck,
    optionDiff requested.compilerCheckTypes context.compilerCheckTypes,
    optionDiff requested.compilerSmall context.compilerSmall,
    optionDiff requested.compilerMaxRecInline context.compilerMaxRecInline,
    optionDiff requested.compilerMaxRecInlineIfReduce context.compilerMaxRecInlineIfReduce,
    optionDiff requested.compilerMaxRecSpecialize context.compilerMaxRecSpecialize
  ].filterMap id

private def withDisplayOptions (display : CEDisplayOptionDecls) (x : CoreM α) : CoreM α := do
  withOptions (fun opts =>
    let opts := opts.set `pp.letVarTypes display.ppLetVarTypes.value
    let opts := opts.set `pp.funBinderTypes display.ppFunBinderTypes.value
    let opts := opts.set `pp.explicit display.ppExplicit.value
    let opts := opts.set `pp.all display.ppAll.value
    let opts := opts.set `pp.fullNames display.ppFullNames.value
    let opts := opts.set `pp.privateNames display.ppPrivateNames.value
    let opts := opts.set `pp.universes display.ppUniverses.value
    opts
  ) x

private def withCompilerOptions (compiler : CECompilerOptionDecls) (x : CoreM α) : CoreM α := do
  withOptions (fun opts =>
    let opts := opts.set `compiler.reuse (!compiler.explicitRc.value)
    let opts := opts.set `compiler.extract_closed compiler.compilerExtractClosed.value
    let opts := opts.set `compiler.check compiler.compilerCheck.value
    let opts := opts.set `compiler.checkTypes compiler.compilerCheckTypes.value
    let opts := opts.set `compiler.small compiler.compilerSmall.value
    let opts := opts.set `compiler.maxRecInline compiler.compilerMaxRecInline.value
    let opts := opts.set `compiler.maxRecInlineIfReduce compiler.compilerMaxRecInlineIfReduce.value
    let opts := opts.set `compiler.maxRecSpecialize compiler.compilerMaxRecSpecialize.value
    opts
  ) x

/--
`shouldGenerateCode` can throw for declarations missing expected compiler artifacts
(for example, missing LCNF signatures in some recursive/brec cases). We catch here
to keep CE resilient and expose details via `debugInfo` instead of failing RPC.
-/
private def shouldGenerateCodeResult (declName : Name) : CoreM (Bool × Option String) := do
  try
    return (← Lean.Compiler.LCNF.shouldGenerateCode declName, none)
  catch e =>
    return (false, some (← e.toMessageData.toString))

private def irDeclToCodeRepr (decl : Lean.IR.Decl) : CECodeRepr :=
  .text (toString decl)

private def lcnfDeclToCodeRepr (display : CEDisplayOptionDecls) {p} (decl : Lean.Compiler.LCNF.Decl p) :
    CoreM CECodeRepr := do
  let fmt ← withDisplayOptions display <| Lean.Compiler.LCNF.ppDecl' decl .base
  return .text fmt.pretty

private def getStoredIRCode (declName : Name) : CoreM CECodeResult := do
  let env ← getEnv
  let local? ← (Lean.IR.findLocalDecl declName) <|> (Lean.IR.findLocalDecl (declName ++ `_boxed))
  if let some decl := local? then
    return .available (irDeclToCodeRepr decl) .localEnvironment {}
  let imported? :=
    Lean.IR.findEnvDecl (includeServer := true) env declName <|>
    Lean.IR.findEnvDecl (includeServer := true) env (declName ++ `_boxed)
  if let some decl := imported? then
    return .available (irDeclToCodeRepr decl) .importedEnvironment {}
  return .unavailable .notFoundInEnvironment

private def getStoredLCNFCode (display : CEDisplayOptionDecls) (declName : Name) : CoreM CECodeResult := do
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

private def compileIRCode (compiler : CECompilerOptionDecls) (declName : Name)
    (origin : CECodeOrigin) : CoreM CECodeResult := do
  try
    let sccs ← withCompilerOptions compiler <| Lean.Compiler.LCNF.compile #[declName]
    if sccs.isEmpty then
      return .unavailable .compilationReturnedNoCode
    let sccCode : Array CECodeRepr :=
      sccs.map fun scc => .lines (scc.map irDeclToCodeRepr)
    let code := .lines sccCode
    return .available code origin { compiler? := some compiler }
  catch e =>
    return .unavailable (.compilationFailed (← e.toMessageData.toString))

private def compileLCNFCode (display : CEDisplayOptionDecls) (compiler : CECompilerOptionDecls)
    (recompileViaPipeline : Bool)
    (declName : Name) (origin : CECodeOrigin) : CoreM CECodeResult := do
  try
    if recompileViaPipeline then
      let _ ← withCompilerOptions compiler <| Lean.Compiler.LCNF.compile #[declName]
      let localDecl? ← Lean.Compiler.LCNF.CompilerM.run do
        let direct? ← Lean.Compiler.LCNF.getLocalDeclAt? declName .base
        match direct? with
        | some decl => pure (some decl)
        | none => Lean.Compiler.LCNF.getLocalDeclAt? (declName ++ `_boxed) .base
      let some decl := localDecl?
        | return .unavailable .compilationReturnedNoCode
      let code ← lcnfDeclToCodeRepr display decl
      return .available code origin { display? := some display, compiler? := some compiler }
    else
      let decl ← withCompilerOptions compiler <| Lean.Compiler.LCNF.CompilerM.run <| Lean.Compiler.LCNF.toDecl declName
      let code ← lcnfDeclToCodeRepr display decl
      return .available code origin { display? := some display, compiler? := some compiler }
  catch e =>
    return .unavailable (.compilationFailed (← e.toMessageData.toString))

private structure AnalysisResult where
  shouldGenerate : Bool := false
  shouldGenerateError? : Option String := none
  forceRecompile : Bool := false
  recompileOptionDiffs : Array String := #[]
  ir : CECodeResult := .unavailable .notCompilableConstant
  lcnf : CECodeResult := .unavailable .notCompilableConstant

private def analysisHasAnyCode (a : AnalysisResult) : Bool :=
  a.ir.isAvailable || a.lcnf.isAvailable

private def analysisHasIR (a : AnalysisResult) : Bool :=
  analysisHasAnyCode a || a.shouldGenerate

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
      shouldGenerate := false
      ir := .unavailable .notCompilableConstant
      lcnf := .unavailable .notCompilableConstant
    }

  let (shouldGenerate, shouldGenerateError?) ← shouldGenerateCodeResult declName

  let optionDiffs := compilerOptionDiffs cfg.compiler cfg.compilerContext
  let mut recompileOptionDiffs := optionDiffs
  if cfg.forceRecompileRequested then
    recompileOptionDiffs := #["forced by header checkbox"] ++ recompileOptionDiffs
  let forceRecompile := cfg.forceRecompileRequested || !recompileOptionDiffs.isEmpty
  let recompiledOrigin : CECodeOrigin :=
    if cfg.forceRecompileRequested then .recompiledForced else .recompiledDueToOptions

  let storedIR ← getStoredIRCode declName
  let ir ←
    if forceRecompile then
      let origin := if storedIR.isAvailable then recompiledOrigin else .compiledFromScratchForced
      compileIRCode cfg.compiler declName origin
    else
      match storedIR with
      | .available .. => pure storedIR
      | .unavailable _ => compileIRCode cfg.compiler declName .compiledFromScratch

  let storedLCNF ← getStoredLCNFCode cfg.display declName
  let lcnf ←
    if forceRecompile then
      let origin := if storedLCNF.isAvailable then recompiledOrigin else .compiledFromScratchForced
      compileLCNFCode cfg.display cfg.compiler cfg.lcnfRecompileViaPipeline declName origin
    else
      match storedLCNF with
      | .available .. => pure storedLCNF
      | .unavailable _ =>
          compileLCNFCode cfg.display cfg.compiler cfg.lcnfRecompileViaPipeline declName .compiledFromScratch

  let ir := withShouldGenerateFallback shouldGenerate ir
  let lcnf := withShouldGenerateFallback shouldGenerate lcnf

  return { shouldGenerate, shouldGenerateError?, forceRecompile, recompileOptionDiffs, ir, lcnf }

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

private def codeResultDebug (code : CECodeResult) : String :=
  match code with
  | .available _ origin opts =>
    let originStr := match origin with
      | .localEnvironment => "localEnvironment"
      | .importedEnvironment => "importedEnvironment"
      | .recompiledDueToOptions => "recompiledDueToOptions"
      | .recompiledForced => "recompiledForced"
      | .compiledFromScratch => "compiledFromScratch"
      | .compiledFromScratchForced => "compiledFromScratchForced"
    s!"available:{originStr}:display={opts.display?.isSome}:compiler={opts.compiler?.isSome}"
  | .unavailable reason => s!"unavailable:{CECodeResult.reasonLabel reason}"

private def mkDebugInfo (_params : IRAtPosParams)
    (cursorDeclName resolvedDeclName : Name) (analysis : AnalysisResult) : Array String :=
  let out := #[
    s!"ir={codeResultDebug analysis.ir}",
    s!"lcnf={codeResultDebug analysis.lcnf}"
  ]
  let out :=
    if cursorDeclName != resolvedDeclName then
      out.push s!"resolvedDecl={resolvedDeclName}"
    else
      out
  let out :=
    if analysis.forceRecompile then
      out.push "forcedRecompile=true"
    else
      out
  let out :=
    if analysis.recompileOptionDiffs.isEmpty then
      out
    else
      out ++ (analysis.recompileOptionDiffs.map (fun d => s!"recompileDiff={d}"))
  let out := match analysis.ir with
    | .unavailable (.compilationFailed err) => out.push s!"irCompileError={err}"
    | _ => out
  let out := match analysis.lcnf with
    | .unavailable (.compilationFailed err) => out.push s!"lcnfCompileError={err}"
    | _ => out
  match analysis.shouldGenerateError? with
  | some err => out.push s!"shouldGenerateError={err}"
  | none => out

open Server RequestM
private def irAtPosImpl (params : IRAtPosParams) : RequestM (RequestTask IRAtPosResponse) := do
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
    let ctxCompiler := CECompilerOptions.fromOptions constAt.info.ctx.options |>.toDecls
    let cfg : CEAnalysisConfig := {
      display := params.display.toDecls
      compiler := params.compiler.toDecls
      compilerContext := ctxCompiler
      forceRecompileRequested := params.forceRecompile
      lcnfRecompileViaPipeline := params.lcnfRecompileViaPipeline
    }
    let resolved ← RequestM.runCoreM snap do
      withEnv env do
        resolveDeclAnalysis cfg declName

    let resolvedDeclName := resolved.resolvedDeclName
    let analysis := resolved.analysis
    let debugInfo := mkDebugInfo params declName resolvedDeclName analysis

    return .declaration {
      declName := resolvedDeclName
      cursorDeclName := declName
      hasIR := analysisHasIR analysis
      ir := analysis.ir
      lcnf := analysis.lcnf
      recompileOptionDiffs := analysis.recompileOptionDiffs
      usedHelperFallback := resolved.usedHelperFallback
      debugInfo
    }

@[implemented_by irAtPosImpl]
meta opaque irAtPos (params : IRAtPosParams) : RequestM (RequestTask IRAtPosResponse)

attribute [server_rpc_method] irAtPos

end DevWidgets.CE
