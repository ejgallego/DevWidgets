import DevWidgets.InfoTreeExplorer
import Lean

open Lean

namespace DevWidgets.Tests.InfoTreeExplorer.AtPos

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain substring `{needle}`\n---\n{haystack}\n---"

private def assertNotContains (label haystack needle : String) : CoreM Unit := do
  if haystack.contains needle then
    throwError m!"expected `{label}` to not contain substring `{needle}`\n---\n{haystack}\n---"

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

/-!
Regression test for the InfoTree explorer refactor:
- frontend RPC must use `infoTreeAtPos` keyed by `props.pos` (cursor/click).
- old polling endpoint must not be referenced anymore.
- old `#infotree_explorer` command must remain unavailable.
-/
#eval show CoreM Unit from do
  let js := DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget.javascript
  assertContains "infoTreeExplorerWidget.javascript" js "infoTreeAtPos"
  assertContains "infoTreeExplorerWidget.javascript" js "props?.pos"
  assertNotContains "infoTreeExplorerWidget.javascript" js "fetchInfoTreeSummary"
  let (legacyCmd, parseMsgs) ← parseSingleCommand "#infotree_explorer\n"
  unless legacyCmd.getKind == ``Lean.Parser.Command.eoi do
    throwError m!"expected parse fallback kind `Lean.Parser.Command.eoi`, got `{legacyCmd.getKind}`"
  let parseMsgTxts ← parseMsgs.toList.mapM (fun m => m.data.toString)
  unless parseMsgTxts.any (·.contains "unexpected token '#'; expected command") do
    throwError m!"expected parser error for removed `#infotree_explorer`, got:\n{String.intercalate "\n" parseMsgTxts}"

end DevWidgets.Tests.InfoTreeExplorer.AtPos
