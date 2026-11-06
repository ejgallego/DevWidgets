import Lean

/-! Plain, version-scoped captures. No RPC references retain elaborator state. -/
namespace DevWidgets.SnapshotExplorer
open Lean

/-- Shared numeric bounds, also embedded in the frontend. -/
structure NumericSetting where
  value : Nat
  min : Nat
  max : Nat
  deriving ToJson

def intervalSetting : NumericSetting := ⟨500, 100, 60000⟩
def commandsSetting : NumericSetting := ⟨200, 1, 2000⟩
def nodesSetting : NumericSetting := ⟨128, 1, 2048⟩
def depthSetting : NumericSetting := ⟨12, 0, 32⟩

def NumericSetting.clamp (setting : NumericSetting) (value? : Option Nat) : Nat :=
  Nat.max setting.min (Nat.min setting.max (value?.getD setting.value))

structure Limits where
  maxCommands : Nat := commandsSetting.value
  maxNodes : Nat := nodesSetting.value
  maxDepth : Nat := depthSetting.value
  deriving ToJson, FromJson

structure Config extends Limits where
  autoRefresh : Bool := true
  intervalMs : Nat := intervalSetting.value
  deriving ToJson, FromJson

def Config.manual : Config := { autoRefresh := false }

structure ReadParams where
  maxCommands? : Option Nat := none
  maxNodes? : Option Nat := none
  maxDepth? : Option Nat := none
  /-- All three fields are required to follow a selection. -/
  generation? : Option String := none
  version? : Option Nat := none
  command? : Option Nat := none
  deriving ToJson, FromJson

def ReadParams.limits (p : ReadParams) : Limits := {
  maxCommands := commandsSetting.clamp p.maxCommands?
  maxNodes := nodesSetting.clamp p.maxNodes?
  maxDepth := depthSetting.clamp p.maxDepth?
}

inductive Frontier where
  | pending | complete | limited | fatal
  deriving ToJson, FromJson, BEq, Inhabited

structure CommandRow where
  index : Nat
  label : String
  range? : Option Lsp.Range
  mainReady : Bool
  infoReady : Bool
  reportingReady : Bool
  fatal : Bool
  deriving ToJson, FromJson

inductive NodeKind where
  | main | infoTree | elaboration | reporting | nested
  deriving ToJson, FromJson

inductive ReportingRange where
  | inherit | skip | explicit
  deriving ToJson, FromJson

structure Facts where
  description : String
  fatal : Bool
  hasInfoTree : Bool
  /-- Local message count, not a count of distinct messages across the tree. -/
  messages : Nat
  deriving ToJson, FromJson

/-- Task readiness does not imply a usable result or supported inspection. -/
inductive Observation where
  | pending
  | inspected (facts : Facts)
  | unsupported (typeName : String)
  | noResult
  deriving ToJson, FromJson

/-- Preorder rows; depth determines parentage within this capture only. -/
structure Node where
  label : String
  depth : Nat
  kind : NodeKind := .nested
  observation : Observation := .pending
  range? : Option Lsp.Range := none
  reporting : ReportingRange := .inherit
  deriving ToJson, FromJson

structure View where
  uri : Lsp.DocumentUri
  /-- Opaque identity for one file worker; not a reuse fingerprint. -/
  generation : String
  version : Nat
  commands : Array CommandRow := #[]
  frontier : Frontier := .pending
  selected? : Option Nat := none
  nodes : Array Node := #[]
  /-- Only traversal-budget exhaustion; unsupported observations are marked per node. -/
  truncated : Bool := false
  deriving ToJson, FromJson

end DevWidgets.SnapshotExplorer
