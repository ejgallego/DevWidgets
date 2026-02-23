import DevWidgets.DocString
import Lean

open Lean

set_option doc.verso true

namespace DevWidgets.Tests.DocString.VersoLean

/--
Inline Lean role and Lean code block, intended to validate semantic rendering.

Inline: {lean}`Nat.succ`

```lean
def localDocExample : Nat := Nat.succ 1
```
-/
def sampleDecl : Nat := 3

private def assertContains (label haystack needle : String) : CoreM Unit := do
  unless haystack.contains needle do
    throwError m!"expected `{label}` to contain substring `{needle}`\n---\n{haystack}\n---"

/-
Regression test:
- Lean block should render as semantically highlighted code (`lean-code` / `lean-token`).
- Inline `{lean}` role should also carry dedicated semantic markup.
-/
#eval show CoreM Unit from do
  let env ← getEnv
  let some internal := (← findInternalDocString? env ``sampleDecl)
    | throwError "no internal docstring found for `sampleDecl`"
  let .inr verso := internal
    | throwError "expected a Verso docstring for `sampleDecl`"
  let html := DevWidgets.DocString.renderVersoDocHtml verso
  assertContains "Verso HTML" html "lean-code"
  assertContains "Verso HTML" html "lean-token"
  assertContains "Verso HTML" html "lean-ref lean-term"

/--
Docstring with multiple {lit}`#eval` commands to validate command rendering.

```lean
#eval (1 + 2)
#eval Nat.succ 10
#eval String.length "lean"
```
-/
def sampleEvalDecl : Nat := 4

/-
Regression test:
- `#eval` lines inside Verso `lean` blocks should be rendered as code.
-/
#eval show CoreM Unit from do
  let env ← getEnv
  let some internal := (← findInternalDocString? env ``sampleEvalDecl)
    | throwError "no internal docstring found for `sampleEvalDecl`"
  let .inr verso := internal
    | throwError "expected a Verso docstring for `sampleEvalDecl`"
  let html := DevWidgets.DocString.renderVersoDocHtml verso
  assertContains "Verso #eval HTML" html "lean-code"
  assertContains "Verso #eval HTML" html "#eval"
  assertContains "Verso #eval HTML" html "Nat.succ"
  assertContains "Verso #eval HTML" html "String.length"

/--
# Markdown docstring

This declaration demonstrates plain/Markdown docstrings.

- bullet item
- second bullet with {lit}`inline code`

1. ordered item
2. another ordered item

 quoted text block

**bold**, *italic*, and a [link](https://lean-lang.org/).

```lean
#eval [1, 2, 3].length
```
-/
def mdSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + mdSum xs

/--
# Verso mini case study

This declaration describes a tiny pipeline that combines
{name}`Nat` with {name}`mdSum`.

## Steps

1. increment the input with {name}`List.length`
2. scale the result
3. add a small checksum based on {lit}`n`

## Notes

- The expression is intentionally simple but non-trivial.
- It is useful for verifying hover docs on references.

```lean
def aaaa := 3
#eval (2 * (5 + 1) + (5 + 1))
```
-/
def versoPipeline (n : Nat) : Nat :=
  2 * n + mdSum [n, 1]


end DevWidgets.Tests.DocString.VersoLean
