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
  { node with description := snap.desc.take 240 |>.toString
              fatal := snap.isFatal, hasInfoTree := snap.infoTree?.isSome
              messages := snap.diagnostics.msgLog.reported.size + snap.diagnostics.msgLog.unreported.size }

private def room (limits : Config) (depth : Nat) : ObserveM Bool := do
  if (← get).nodes.size >= limits.maxNodes || depth > limits.maxDepth then
    modify fun s => { s with truncated := true }
    return false
  return true

/-- A budget is shared across all branches, including pending and unpositioned tasks. -/
private def visitTask (text : FileMap) (limits : Config) (depth : Nat) (label : String)
    (task : SnapshotTask α) (inspect : α → Node → ObserveM Unit)
    (trans : SnapshotTreeTransform := default) : ObserveM Unit := do
  if !(← room limits depth) then return
  let value ← task.get?
  let node : Node := {
    label, depth, ready := value.isSome
    range? := task.stx?.map trans.transformSyntax |>.bind (·.getRange?) |>.map (lspRange text)
    reporting := match task.reportingRange with
      | .inherit => "inherit"
      | .skip => "skip"
      | .some _ => "explicit"
  }
  match value with
  | none => modify fun s => { s with nodes := s.nodes.push node }
  | some value => inspect value node

private def emit (node : Node) : ObserveM Unit :=
  modify fun s => { s with nodes := s.nodes.push node }

-- Pass transformations down as values. Do not call applyTransform: that maps child tasks.
mutual
private partial def tree (text : FileMap) (p : Config) (trans : SnapshotTreeTransform)
    (snap : SnapshotTree) (node : Node) : ObserveM Unit := do
  emit (facts node snap.element)
  for i in [:snap.children.size] do
    if !(← room p (node.depth + 1)) then
      break
    visitTask text p (node.depth + 1) s!"Snapshot {i + 1}" snap.children[i]!
      (tree text p trans) trans

private partial def tactic (text : FileMap) (p : Config) (trans : SnapshotTreeTransform)
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
    for i in [:s.moreSnaps.size] do
      if !(← room p (n.depth + 1)) then
        break
      visitTask text p (n.depth + 1) s!"Reporting {i + 1}" s.moreSnaps[i]! (tree text p trans) trans
  for i in [:snap.next.size] do
    if !(← room p (node.depth + 1)) then
      break
    visitTask text p (node.depth + 1) s!"Next tactic {i + 1}" snap.next[i]! (tactic text p outer) outer

private partial def dynamic (text : FileMap) (p : Config)
    (snap : DynamicSnapshot) (node : Node) : ObserveM Unit := do
  if let some s := snap.toTyped? SnapshotLeaf then
    emit (facts node s.toSnapshot)
  else if let some s := snap.toTyped? Elab.Command.MacroExpandedSnapshot then
    emit (facts node s.toSnapshot)
    for i in [:s.next.size] do
      if !(← room p (node.depth + 1)) then
        break
      visitTask text p (node.depth + 1) s!"Expanded command {i + 1}" s.next[i]! (dynamic text p)
  else if let some s := snap.toTyped? Elab.DefsParsedSnapshot then
    emit (facts node s.toSnapshot)
    for h : i in [:s.defs.size] do
      if !(← room p (node.depth + 1)) then
        break
      visitTask text p (node.depth + 1) s!"Declaration {i + 1}" s.defs[i].headerProcessedSnap fun s n => do
        match s with
        | none => emit { n with description := "No header result" }
        | some s =>
          emit (facts n s.toSnapshot)
          if let some t := s.tacSnap? then
            visitTask text p (n.depth + 1) "Tactics" t (tactic text p default)
          visitTask text p (n.depth + 1) "Body result" s.bodySnap fun body n => do
            match body with
            | none => emit { n with description := "No body result" }
            | some body =>
              emit (facts n body.toSnapshot)
              for i in [:body.moreSnaps.size] do
                if !(← room p (n.depth + 1)) then
                  break
                visitTask text p (n.depth + 1) s!"Reporting {i + 1}" body.moreSnaps[i]! (tree text p default)
          for i in [:s.moreSnaps.size] do
            if !(← room p (n.depth + 1)) then
              break
            visitTask text p (n.depth + 1) s!"Reporting {i + 1}" s.moreSnaps[i]! (tree text p default)
  else
    emit { node with unsupported := true, description := s!"Unsupported snapshot type: {snap.val.typeName}" }
end

/-- Inspect only one command, without retaining its tasks after returning. -/
def observeCommand (text : FileMap) (params : ReadParams)
    (snap : Language.Lean.CommandElaboratingSnapshot) : BaseIO (Array Node × Bool) := do
  let p : Config := { maxNodes := max 1 (min 2048 (params.maxNodes?.getD 128))
                      maxDepth := min 32 (params.maxDepth?.getD 12) }
  let (_, capture) ← (do
    visitTask text p 0 "Main elaborator" snap.resultSnap fun s n => emit (facts n s.toSnapshot)
    visitTask text p 0 "Complete InfoTree" snap.infoTreeSnap fun s n => emit (facts n s.toSnapshot)
    visitTask text p 0 "Elaboration snapshots" snap.elabSnap (dynamic text p)
    visitTask text p 0 "Reporting" snap.reportSnap (tree text p default)).run {}
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
def observe (uri : Lsp.DocumentUri) (version : Nat) (text : FileMap)
    (root : Language.Lean.InitialSnapshot) (params : ReadParams) : BaseIO View := do
  let mut view : View := { uri, version }
  let some parsed := root.result? | return { view with frontier := .fatal }
  let some processed ← parsed.processedSnap.get? | return view
  let some header := processed.result? | return { view with frontier := .fatal }
  let mut next := some header.firstCmdSnap
  for i in [:max 1 (min 2000 (params.maxCommands?.getD 200))] do
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
    if params.version? == some version && params.command? == some i then
      let (nodes, truncated) ← observeCommand text params cmd.elabSnap
      view := { view with selected? := some i, nodes, truncated }
    if row.fatal then return { view with frontier := .fatal }
    next := cmd.nextCmdSnap?
  return { view with frontier := if next.isNone then .complete else .limited }

end DevWidgets.SnapshotExplorer
