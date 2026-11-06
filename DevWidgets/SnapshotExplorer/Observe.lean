import DevWidgets.SnapshotExplorer.Model

/-!
Lean 4.36 adapter. Read ready tasks directly: never map a snapshot task or convert the
whole document with `toSnapshotTree`, which can recursively schedule conversions.
Unknown dynamic snapshot types remain opaque. Traversal limits apply before expansion.
-/
namespace DevWidgets.SnapshotExplorer
open Lean Language

private structure Capture where
  nodes : Array Node := #[]
  truncated : Bool := false

private abbrev ObserveM := StateT Capture BaseIO

private def lspRange (text : FileMap) (r : Syntax.Range) : Lsp.Range :=
  ⟨text.utf8PosToLspPos r.start, text.utf8PosToLspPos r.stop⟩

private def facts (node : Node) (snap : Language.Snapshot) : Node :=
  { node with observation := .inspected {
      description := snap.desc.take 240 |>.toString
      fatal := snap.isFatal, hasInfoTree := snap.infoTree?.isSome
      messages := snap.diagnostics.msgLog.reported.size + snap.diagnostics.msgLog.unreported.size
  } }

private def room (limits : Limits) (depth : Nat) : ObserveM Bool := do
  if (← get).nodes.size >= limits.maxNodes || depth > limits.maxDepth then
    modify fun s => { s with truncated := true }
    return false
  return true

/-- A budget is shared across all branches, including pending and unpositioned tasks. -/
private def visitTask (text : FileMap) (limits : Limits) (depth : Nat) (label : String)
    (task : SnapshotTask α) (inspect : α → Node → ObserveM Unit)
    (trans : SnapshotTreeTransform := default) (kind : NodeKind := .nested) : ObserveM Unit := do
  if !(← room limits depth) then return
  let value ← task.get?
  let node : Node := {
    label, depth, kind
    range? := task.stx?.map trans.transformSyntax |>.bind (·.getRange?) |>.map (lspRange text)
    reporting := match task.reportingRange with
      | .inherit => .inherit
      | .skip => .skip
      | .some _ => .explicit
  }
  match value with
  | none => modify fun s => { s with nodes := s.nodes.push node }
  | some value => inspect value node

private def emit (node : Node) : ObserveM Unit :=
  modify fun s => { s with nodes := s.nodes.push node }

private def children (p : Limits) (depth : Nat) (items : Array α)
    (visit : Nat → α → ObserveM Unit) : ObserveM Unit := do
  for h : i in [:items.size] do
    if !(← room p depth) then break
    visit i items[i]

-- Pass transformations down as values. Do not call applyTransform: that maps child tasks.
mutual
private partial def tree (text : FileMap) (p : Limits) (trans : SnapshotTreeTransform)
    (snap : SnapshotTree) (node : Node) : ObserveM Unit := do
  emit (facts node snap.element)
  children p (node.depth + 1) snap.children fun i child => do
    visitTask text p (node.depth + 1) s!"Snapshot {i + 1}" child
      (tree text p trans) trans

private partial def tactic (text : FileMap) (p : Limits) (trans : SnapshotTreeTransform)
    (snap : Elab.Tactic.TacticParsedSnapshot) (node : Node) : ObserveM Unit := do
  let outer := trans
  let trans := trans.compose snap.transformed.transform
  let raw := snap.transformed.raw
  let range? := (trans.transformSyntax raw.stx).getRange? |>.map (lspRange text)
  emit (facts { node with range? } raw.toSnapshot)
  if let some inner := raw.inner? then
    visitTask text p (node.depth + 1) "Nested tactic" inner (tactic text p trans) trans
  visitTask text p (node.depth + 1) "Tactic result" raw.finished fun s n => do
    emit (facts n s.toSnapshot)
    children p (n.depth + 1) s.moreSnaps fun i child => do
      visitTask text p (n.depth + 1) s!"Reporting {i + 1}" child (tree text p trans) trans
  children p (node.depth + 1) snap.next fun i child => do
    visitTask text p (node.depth + 1) s!"Next tactic {i + 1}" child (tactic text p outer) outer

private partial def dynamic (text : FileMap) (p : Limits)
    (snap : DynamicSnapshot) (node : Node) : ObserveM Unit := do
  if let some s := snap.toTyped? SnapshotLeaf then
    emit (facts node s.toSnapshot)
  else if let some s := snap.toTyped? SnapshotTree then
    tree text p default s node
  else if let some s := snap.toTyped? Elab.Command.MacroExpandedSnapshot then
    emit (facts node s.toSnapshot)
    children p (node.depth + 1) s.next fun i child => do
      visitTask text p (node.depth + 1) s!"Expanded command {i + 1}" child (dynamic text p)
  else if let some s := snap.toTyped? Elab.DefsParsedSnapshot then
    emit (facts node s.toSnapshot)
    children p (node.depth + 1) s.defs fun i child => do
      visitTask text p (node.depth + 1) s!"Declaration {i + 1}" child.headerProcessedSnap fun s n => do
        match s with
        | none => emit { n with observation := .noResult }
        | some s =>
          emit (facts n s.toSnapshot)
          if let some t := s.tacSnap? then
            visitTask text p (n.depth + 1) "Tactics" t (tactic text p default)
          visitTask text p (n.depth + 1) "Body result" s.bodySnap fun body n => do
            match body with
            | none => emit { n with observation := .noResult }
            | some body =>
              emit (facts n body.toSnapshot)
              children p (n.depth + 1) body.moreSnaps fun i child => do
                visitTask text p (n.depth + 1) s!"Reporting {i + 1}" child (tree text p default)
          children p (n.depth + 1) s.moreSnaps fun i child => do
            visitTask text p (n.depth + 1) s!"Reporting {i + 1}" child (tree text p default)
  else
    emit { node with observation := .unsupported snap.val.typeName.toString }
end

/-- Inspect only one command, without retaining its tasks after returning. -/
def observeCommand (text : FileMap) (params : ReadParams)
    (snap : Language.Lean.CommandElaboratingSnapshot) : BaseIO (Array Node × Bool) := do
  let p := params.limits
  let (_, capture) ← (do
    visitTask text p 0 "Main elaborator" snap.resultSnap (fun s n => emit (facts n s.toSnapshot)) (kind := .main)
    visitTask text p 0 "Complete InfoTree" snap.infoTreeSnap (fun s n => emit (facts n s.toSnapshot)) (kind := .infoTree)
    visitTask text p 0 "Elaboration snapshots" snap.elabSnap (dynamic text p) (kind := .elaboration)
    visitTask text p 0 "Reporting" snap.reportSnap (tree text p default) (kind := .reporting)).run {}
  return (capture.nodes, capture.truncated)

private def commandLabel (text : FileMap) (stx : Syntax) : String := Id.run do
  let some range := stx.getRange? | return stx.getKind.toString
  let mut stop := range.start
  for _ in [:100] do
    if stop >= range.stop || stop.atEnd text.source || stop.get text.source == '\n' then break
    stop := stop.next text.source
  let label := String.Pos.Raw.extract text.source range.start stop
  return if label == "/-!" then "Module documentation"
    else if label.isEmpty then stx.getKind.toString else label

/-- File sampling follows only ready command links. Completion means command discovery ended;
individual elaboration/reporting tasks may still be pending. -/
def observe (generation : String) (uri : Lsp.DocumentUri) (version : Nat) (text : FileMap)
    (root : Language.Lean.InitialSnapshot) (params : ReadParams) : BaseIO View := do
  let mut view : View := { uri, generation, version }
  let some parsed := root.result? | return { view with frontier := .fatal }
  let some processed ← parsed.processedSnap.get? | return view
  let some header := processed.result? | return { view with frontier := .fatal }
  let mut next := some header.firstCmdSnap
  for i in [:params.limits.maxCommands] do
    let some task := next | return { view with frontier := .complete }
    let some cmd ← task.get? | return view
    if cmd.stx.isOfKind ``Parser.Command.eoi then
      return { view with frontier := .complete }
    let main ← cmd.elabSnap.resultSnap.get?
    let row : CommandRow := {
      index := i, label := commandLabel text cmd.stx
      range? := cmd.stx.getRange? |>.map (lspRange text)
      mainReady := main.isSome
      infoReady := (← IO.hasFinished cmd.elabSnap.infoTreeSnap.task)
      reportingReady := (← IO.hasFinished cmd.elabSnap.reportSnap.task)
      fatal := cmd.isFatal || main.any (·.isFatal)
    }
    view := { view with commands := view.commands.push row }
    if params.generation? == some generation && params.version? == some version && params.command? == some i then
      let (nodes, truncated) ← observeCommand text params cmd.elabSnap
      view := { view with selected? := some i, nodes, truncated }
    if row.fatal then return { view with frontier := .fatal }
    next := cmd.nextCmdSnap?
  -- The budget counts commands, not EOF. One nonblocking lookahead distinguishes
  -- a complete prefix, a pending continuation, and a genuinely omitted command.
  let some task := next | return { view with frontier := .complete }
  let some cmd ← task.get? | return view
  return { view with frontier := if cmd.stx.isOfKind ``Parser.Command.eoi then .complete else .limited }

end DevWidgets.SnapshotExplorer
