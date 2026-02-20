import Lean
import Lean.DocString.Syntax
import DevWidgets.DocString

/-!
# DocString Example

Move the cursor over documented identifiers in this file.
This file intentionally mixes `doc.verso = false` and `doc.verso = true`
to exercise both docstring modes in the `DevWidgets.DocString` panel.
-/

namespace DocStringExample

set_option doc.verso false

/--
# Markdown docstring (`doc.verso = false`)

This declaration demonstrates plain/Markdown docstrings.

- bullet item
- second bullet with `inline code`

1. ordered item
2. another ordered item

> quoted text block

**bold**, *italic*, and a [link](https://lean-lang.org/).

```lean
#eval mdSum [1, 2, 3]
```
-/
def mdSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + mdSum xs



/--
Markdown table-style content:

| Feature | Example |
| --- | --- |
| code | `Nat.succ` |
| math-ish text | `x + y` |
-/
def mdTable (a b : Nat) : Nat := a + b

/-- Simple theorem with a Markdown-mode docstring. -/
theorem mdSum_nil : mdSum [] = 0 := rfl

/--
Markdown docstring on a structure.
Fields below also have independent docstrings.
-/
structure MarkdownRecord where
  /-- Numeric payload in Markdown mode. -/
  value : Nat
  /-- Human-readable label in Markdown mode. -/
  tag : String

/--
Markdown _docstring_ on an inductive declaration.
Constructors below are documented too.
-/
inductive MarkdownTree where
  /-- Leaf constructor carrying one `Nat`. -/
  | leaf (n : Nat)
  /-- Binary branch constructor. -/
  | branch (left right : MarkdownTree)
  deriving Repr

set_option doc.verso true

/--
# Verso declaration doc

This docstring exercises common Verso features:

- literal role: {lit}`x + 1`
- Lean role: {lean}`Nat.succ`
- declaration role: {name}`List.map`
- declaration role with full target:
  {name (full := List.foldl)}`List.foldl`

## Block content

1. first ordered entry
2. second ordered entry

```lean
def localExample : Nat := 7
```
-/
def versoSucc (n : Nat) : Nat := n + 1

/--
# Verso structure docs

Field docs can also use roles like {name}`Nat`.
-/
structure VersoRecord where
  /-- Base numeric value with literal role: {lit}`base`. -/
  base : Nat
  /-- User-facing label field. -/
  label : String

/--
# Verso inductive docs

Constructors are documented independently.
-/
inductive VersoExpr where
  /-- Numeric literal node. -/
  | lit (n : Nat)
  /-- Addition node combining two expressions. -/
  | add (a b : VersoExpr)
  deriving Repr

/--
# Verso theorem docs

Small theorem for hover/doc testing.
-/
theorem versoSucc_zero : versoSucc 0 = 1 := rfl

/--
# Verso mini case study

This declaration describes a tiny pipeline that combines
{name}`versoSucc` with {name}`mdSum`.

## Steps

1. increment the input with {name}`versoSucc`
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
  2 * versoSucc n + mdSum [n, 1]

/--
# Verso record with narrative docs

This record documents a made-up analysis report.
Each field is documented independently so the widget can show
constructor and projection docs with {name}`DocCaseStudy`.
-/
structure DocCaseStudy where
  /-- Scenario title, usually short and human-readable. -/
  title : String
  /-- Main input value to the pipeline, often a {lean}`Nat`. -/
  seed : Nat
  /-- Optional summary text shown to users. -/
  summary : String

/--
# Verso expression evaluator

The evaluator demonstrates recursive docs in Verso mode.

| Constructor | Meaning |
| --- | --- |
| {name}`VersoExpr.lit` | numeric literal |
| {name}`VersoExpr.add` | sum of two sub-expressions |
-/
def evalVersoExpr : VersoExpr → Nat
  | .lit n => n
  | .add a b => evalVersoExpr a + evalVersoExpr b

/--
# Verso theorem docs: computed examples

These tiny theorems are intended for quick hover checks and
to provide concrete examples for the rendered docs.
-/
theorem versoPipeline_zero : versoPipeline 0 = 3 := by
  simp [versoPipeline, versoSucc, mdSum]

def demoTree : MarkdownTree := .branch (.leaf 2) (.branch (.leaf 3) (.leaf 5))
def demoExpr : VersoExpr := .add (.lit 2) (.add (.lit 10) (.lit 4))
def demoCase : DocCaseStudy :=
  { title := "Three-step pipeline", seed := 7, summary := "Used by DocString example." }

/-- Demo expression evaluates to {lit}`16`. -/
theorem evalVersoExpr_demo : evalVersoExpr demoExpr = 16 := by
  rfl

#check mdSum
#check mdTable
#check MarkdownRecord.value
#check MarkdownTree.branch
#check versoSucc
#check versoPipeline
#check VersoRecord.base
#check VersoExpr.add
#check versoSucc_zero
#check DocCaseStudy.seed
#check evalVersoExpr

#eval mdSum [1, 2, 3, 4]
#eval versoSucc 41
#eval versoPipeline 5
#eval evalVersoExpr demoExpr

end DocStringExample
