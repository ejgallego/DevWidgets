import Lean

/-! Plain, version-scoped captures. No RPC references retain elaborator state. -/
namespace DevWidgets.SnapshotExplorer
open Lean

structure Config where
  autoRefresh : Bool := true
  intervalMs : Nat := 500
  maxCommands : Nat := 200
  maxNodes : Nat := 128
  maxDepth : Nat := 12
  deriving ToJson, FromJson

def Config.manual : Config := { autoRefresh := false }

structure ReadParams where
  maxCommands? : Option Nat := none
  maxNodes? : Option Nat := none
  maxDepth? : Option Nat := none
  /-- Selection belongs to exactly this version; stale selection is never followed. -/
  version? : Option Nat := none
  command? : Option Nat := none
  deriving ToJson, FromJson

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

/-- Preorder rows; depth determines parentage within this capture only. -/
structure Node where
  label : String
  depth : Nat
  ready : Bool
  description : String := ""
  range? : Option Lsp.Range := none
  reporting : String := "inherit"
  fatal : Bool := false
  hasInfoTree : Bool := false
  /-- Local message count, not a count of distinct messages across the tree. -/
  messages : Nat := 0
  unsupported : Bool := false
  deriving ToJson, FromJson

structure View where
  uri : Lsp.DocumentUri
  version : Nat
  commands : Array CommandRow := #[]
  frontier : Frontier := .pending
  selected? : Option Nat := none
  nodes : Array Node := #[]
  truncated : Bool := false
  deriving ToJson, FromJson

end DevWidgets.SnapshotExplorer
