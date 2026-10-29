import DevWidgets.InfoTreeExplorer
import Lean

open Lean

namespace DevWidgets.Tests.InfoTreeExplorer.AtPos

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain substring `{needle}`\n---\n{haystack}\n---"

private def parseSingleCommand (src : String) : CoreM (Syntax × MessageLog) := do
  let ictx := Parser.mkInputContext src "<infotree-test>"
  let env ← getEnv
  let cmdState : Elab.Command.State := {
    env
    maxRecDepth := (← MonadRecDepth.getMaxRecDepth)
    scopes := [{ header := "", isPublic := true }]
  }
  let pstate : Parser.ModuleParserState := { pos := 0, recovering := false }
  let scope := cmdState.scopes.head!
  let pmctx := {
    env := cmdState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls
  }
  let (cmd, _, msgs) := Parser.parseCommand ictx pmctx pstate cmdState.messages
  pure (cmd, msgs)

-- The removed command must remain unavailable; runtime tests cover cursor RPC calls.
#eval show CoreM Unit from do
  let (legacyCmd, parseMsgs) ← parseSingleCommand "#infotree_explorer\n"
  unless legacyCmd.getKind == ``Lean.Parser.Command.eoi do
    throwError m!"expected parse fallback kind `Lean.Parser.Command.eoi`, got `{legacyCmd.getKind}`"
  let parseMsgTxts ← parseMsgs.toList.mapM (fun m => m.data.toString)
  unless parseMsgTxts.any (·.contains "unexpected token '#'; expected command") do
    throwError m!"expected parser error for removed `#infotree_explorer`, got:\n{String.intercalate "\n" parseMsgTxts}"

#eval show CoreM Unit from do
  let info : Elab.Info := .ofChoiceResolutionInfo { stx := .missing, chosenAltIdx := 0 }
  unless DevWidgets.InfoTreeExplorer.infoTag info == "choiceResolution" do
    throwError "expected a distinct tag for choice-resolution info"

#eval show CoreM Unit from do
  let limits := DevWidgets.InfoTreeExplorer.Config.bounded { maxChildren := 0, maxDepth := 10000 }
  unless limits.maxChildren == 1 && limits.maxDepth == 64 do
    throwError "tree rendering limits were not bounded"
  let text := FileMap.ofString ""
  let stx : Syntax := .node .none `test #[.missing, .missing, .missing]
  let rendered := DevWidgets.InfoTreeExplorer.stxToExplorerTree text 1 stx 1
  assertContains "child limit" rendered.compress "2 more children"
  assertContains "syntax depth limit" rendered.compress "depth limit reached"
  let tree : Elab.InfoTree := .context (.parentDeclCtx `demo) (.hole ⟨`hole⟩)
  let rendered := DevWidgets.InfoTreeExplorer.infoTreeToExplorerTree text 1 none tree 1
  assertContains "info depth limit" rendered.compress "depth limit reached"

end DevWidgets.Tests.InfoTreeExplorer.AtPos
