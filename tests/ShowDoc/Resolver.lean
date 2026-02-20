import DevWidgets.ShowDoc
import Lean

open Lean

namespace DevWidgets.Tests.ShowDoc.Resolver

private def parseSingleCommand (src : String) : CoreM Syntax := do
  let ictx := Parser.mkInputContext src "<showdoc-resolver-test>"
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
  let (cmd, _, _) := Parser.parseCommand ictx pmctx pstate cmdState.messages
  return cmd

private partial def firstNodeByKind? (kind : Name) (stx : Syntax) : Option Syntax :=
  match stx with
  | Syntax.node _ k args =>
    if k == kind then
      some stx
    else
      args.foldl (init := none) fun found? arg =>
        match found? with
        | some _ => found?
        | none => firstNodeByKind? kind arg
  | _ => none

private partial def firstNodeSatisfying? (p : Syntax → Bool) (stx : Syntax) : Option Syntax :=
  if p stx then
    some stx
  else
    match stx with
    | Syntax.node _ _ args =>
      args.foldl (init := none) fun found? arg =>
        match found? with
        | some _ => found?
        | none => firstNodeSatisfying? p arg
    | _ => none

private def assertEqNames (label : String) (expected actual : List Name) : CoreM Unit := do
  unless expected == actual do
    throwError m!"{label}: expected {expected}, got {actual}"

#eval show CoreM Unit from do
  let src := "/-- resolver docs -/\ndef sampleDecl : Nat := 1\n"
  let cmd ← parseSingleCommand src

  let some docComment := firstNodeByKind? ``Lean.Parser.Command.docComment cmd
    | throwError "expected a docComment node"
  let some docRange := docComment.getRange? (canonicalOnly := true)
    | throwError "docComment should have a canonical range"

  let posInDoc := docRange.start + 'x'
  unless DevWidgets.ShowDoc.Testing.isInDocComment cmd posInDoc do
    throwError "expected cursor inside doc comment to be detected"

  let declInDoc := DevWidgets.ShowDoc.Testing.declIdAtPos? cmd posInDoc
  unless declInDoc == some `sampleDecl do
    throwError m!"expected declId at doc-comment cursor to be `sampleDecl`, got {declInDoc}"

  let posAfterDoc := docRange.stop + ' '
  if DevWidgets.ShowDoc.Testing.isInDocComment cmd posAfterDoc then
    throwError "expected cursor after doc comment stop to be outside doc comment"

  let declAfterDoc := DevWidgets.ShowDoc.Testing.declIdAtPos? cmd posAfterDoc
  unless declAfterDoc == some `sampleDecl do
    throwError m!"expected declId after doc-comment to still be `sampleDecl`, got {declAfterDoc}"

#eval show CoreM Unit from do
  let src := "/--\nline one\n\nline three\n-/\ndef withBlank : Nat := 0\n"
  let cmd ← parseSingleCommand src
  let some docComment := firstNodeByKind? ``Lean.Parser.Command.docComment cmd
    | throwError "expected a docComment node"
  let some docRange := docComment.getRange? (canonicalOnly := true)
    | throwError "docComment should have a canonical range"
  -- Position on the empty line between `line one` and `line three`.
  let posOnBlankLine := docRange.start + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x'
  unless DevWidgets.ShowDoc.Testing.isInDocComment cmd posOnBlankLine do
    throwError "expected blank-line cursor inside doc comment to be detected"
  let posAtBlankLineStart := docRange.start + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x' + 'x'
  unless DevWidgets.ShowDoc.Testing.isInDocComment cmd posAtBlankLineStart do
    throwError "expected blank-line-start cursor inside doc comment to be detected"
  unless DevWidgets.ShowDoc.Testing.isInDocCommentNear cmd posAtBlankLineStart do
    throwError "expected near-doc-comment detection on blank-line start"

#eval show CoreM Unit from do
  let src := "/-- body lookup docs -/\ndef bodyLookup : Nat := 37\n"
  let cmd ← parseSingleCommand src
  let some rhsAtom := firstNodeSatisfying? (fun s =>
    match s with
    | Syntax.atom _ v => v == "37"
    | _ => false) cmd
    | throwError "expected literal atom `37` in declaration body"
  let some rhsRange := rhsAtom.getRange? (canonicalOnly := true)
    | throwError "rhs literal atom should have a canonical range"
  let posInBody := rhsRange.start + 'x'
  let declInBody := DevWidgets.ShowDoc.Testing.declIdAtPos? cmd posInBody
  unless declInBody == some `bodyLookup do
    throwError m!"expected declId in declaration body to be `bodyLookup`, got {declInBody}"

#eval show CoreM Unit from do
  let c1 := DevWidgets.ShowDoc.Testing.declarationCandidates `Demo (some `Demo.sampleDecl) (some `sampleDecl)
  assertEqNames "candidate ordering: ctx + stx" [`Demo.sampleDecl, `sampleDecl] c1

  let c2 := DevWidgets.ShowDoc.Testing.declarationCandidates `Demo none (some `sampleDecl)
  assertEqNames "candidate ordering: stx + namespaced" [`sampleDecl, `Demo.sampleDecl] c2

  let c3 := DevWidgets.ShowDoc.Testing.declarationCandidates `Demo (some `Demo.sampleDecl) (some `Demo.sampleDecl)
  assertEqNames "candidate dedup" [`Demo.sampleDecl] c3

  let i1 := DevWidgets.ShowDoc.Testing.identifierCandidates (some `Demo.sampleDecl) (some `sampleDecl)
  assertEqNames "identifier ordering: info + ident" [`Demo.sampleDecl, `sampleDecl] i1

  let i2 := DevWidgets.ShowDoc.Testing.identifierCandidates none (some `sampleDecl)
  assertEqNames "identifier ordering: only ident" [`sampleDecl] i2

  let i3 := DevWidgets.ShowDoc.Testing.identifierCandidates (some `sampleDecl) (some `sampleDecl)
  assertEqNames "identifier dedup" [`sampleDecl] i3

end DevWidgets.Tests.ShowDoc.Resolver
