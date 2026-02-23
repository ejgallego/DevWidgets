# Lean Dev Widgets

Interactive Lean infoview widgets for compiler output, progress tracking,
info trees, and docstring inspection.

Current development target: `leanprover/lean4-nightly` (from `lean-toolchain`).

## Widgets

- `DevWidgets.CE`: Compiler Explorer panel for IR/LCNF inspection.
- `DevWidgets.PTracker`: progress tracker API and widget for long-running elaboration.
- `DevWidgets.InfoTreeExplorer`: cursor-focused info tree explorer panel.
- `DevWidgets.DocString`: cursor-focused docstring inspector with Markdown/Verso rendering.

See runnable demos in `examples/`.

## Quick Start

Build the project:

```bash
lake build
```

Then open any file from `examples/` in Lean/VSCode:

- `examples/CE.lean`
- `examples/PTracker.lean`
- `examples/InfoViewExplorer.lean`
- `examples/InfoTreeFocused.lean`
- `examples/DocString.lean`

## Tests

Run all tests with:

```bash
lake test
```

See [`tests/README.md`](./tests/README.md) for suite details.

## `DevWidgets.CE`

Compiler Explorer widget.

This is an interactive complement to `set_option trace.Compiler.*`:

- shows IR and LCNF (when available),
- supports folding and syntax highlighting,
- exposes pretty-printer/compiler tuning options,
- can compile on-the-fly and diff outputs.

Import:

```lean
import DevWidgets.CE
```

## `DevWidgets.PTracker`

Fine-grained progress reporting for tactics/commands before elaboration is complete.

Main API:

```lean
def withProgressRef [Monad m] [MonadLiftT IO m] [MonadFinally m]
    (totalSteps? : Option Nat)
    (description : String)
    (initialLabel : String := "")
    (act : ProgressRef → m α) : m α := do
```

Update progress:

```lean
def ProgressRef.update
    (ref : ProgressRef)
    (stepsDone : Nat)
    (label? : Option String := none) : IO Unit
```

Tip: call `Lean.Core.checkInterrupted` at safe points in long loops.

## `DevWidgets.InfoTreeExplorer`

Interactive explorer for elaboration info trees around the current cursor position.

- Uses cursor-position RPC (`DevWidgets.InfoTreeExplorer.infoTreeAtPos`).
- Displays focused path information for easier local inspection.

Import:

```lean
import DevWidgets.InfoTreeExplorer
```

Example files: `examples/InfoViewExplorer.lean`, `examples/InfoTreeFocused.lean`.

## `DevWidgets.DocString`

Docstring inspector panel for the declaration or identifier under cursor.

This is currently a draft/demo widget and API surface may change.

- Resolves declaration docstrings using elaborated context + syntax fallbacks.
- Renders both Markdown and Verso docstrings.
- Provides raw doc-comment preview when elaborated docs are unavailable.
- Uses fully-qualified RPC call `DevWidgets.DocString.docAtPos`.

Import:

```lean
import DevWidgets.DocString
```

Example file: `examples/DocString.lean`.

## Regression Tests

Run all regression tests used by CI:

```bash
lake env lean tests/Rpc/QualifiedMethodNames.lean
lake env lean tests/InfoTreeExplorer/AtPos.lean
lake env lean tests/DocString/Resolver.lean
lake env lean tests/DocString/VersoLean.lean
lake env lean tests/Examples/Smoke.lean
```

CI (`.github/workflows/lean_action_ci.yml`) runs these checks on
the repo nightly toolchain.
