# Lean Dev Widgets

Interactive Lean infoview widgets for compiler output, progress tracking,
info trees, and docstring inspection.

Current development target: `leanprover/lean4:v4.36.0-rc2` (from `lean-toolchain`).

## Choose a widget

Each widget works independently. Import its short module name to enable its panel:

| Task | Import |
| --- | --- |
| Inspect IR/LCNF and compiler options | `DevWidgets.CE` |
| Monitor a long-running tactic or command | `DevWidgets.PTracker` |
| Investigate elaboration around the cursor | `DevWidgets.InfoTreeExplorer` |
| Read Markdown/Verso documentation | `DevWidgets.DocString` |

Use the corresponding `.API` import to access definitions and RPC handlers without
enabling a panel. For example, `import DevWidgets.PTracker.API` provides the progress
API and widget definition without showing it. The lighter
`DevWidgets.PTracker.ProgressRef` import provides only the reporting API.

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
- `examples/Configuration.lean`

## Activation and configuration

Use `configure_panel_widget` to enable or replace a panel with a typed configuration:

```lean
import DevWidgets.PTracker

configure_panel_widget DevWidgets.PTracker.progressWidget with
  ({ DevWidgets.PTracker.Config.quiet with autoRemove := false } : DevWidgets.PTracker.Config)
```

This command replaces existing instances of that widget, including ones activated by
imports. It applies to the current section/file; leaving a section restores the previous
configuration. It is available from both the short imports and `.API` imports.

Lean's `show_panel_widgets [local Widget with config]` **adds** an instance; it does not
replace one. Use `configure_panel_widget` for ordinary configuration to avoid duplicates.
For downstream activation, import `.API` and use `show_panel_widgets [Widget with config]`;
Lean also supports `scoped` activation.
Hide a panel for the current scope with:

```lean
show_panel_widgets [-DevWidgets.PTracker.progressWidget]
```

Configurations and task presets stay specific to each widget:

| Widget | Configuration fields | Named presets |
| --- | --- | --- |
| CE | `display`, `compiler`, `showAdvanced`, `lcnfRecompileViaPipeline` | `CE.Config.verbose` |
| InfoTreeExplorer | `maxChildren`, `maxDepth` | `InfoTreeExplorer.Config.focused`, `.detailed` |
| DocString | `maxHeight` in pixels | `DocString.Config.expanded` |
| PTracker | `autoRefresh`, `intervalMs`, `autoRemove`, `retainDoneMs` | `PTracker.Config.quiet`, `.manual` |

All names above are under `DevWidgets`. An empty `Config` uses the widget's defaults.
See [`examples/Configuration.lean`](./examples/Configuration.lean) for all four widgets.

CE, InfoTreeExplorer, and DocString share **Pin result**, **Follow cursor**, **Refresh**,
and **Reset panel** controls. Pinning freezes the displayed response and its source
position; it does not keep requesting a potentially changed file. Follow the cursor
again to refresh. **Reset panel** restores the Lean-supplied configuration and unpins.
CE's separate **Defaults** button restores the compiler schema defaults.
Compiler output appears before a collapsed **Inspector options** section. InfoTreeExplorer
shows the focused result first, with metadata, paths, and full trees available as disclosures.

UI overrides belong to the current panel instance; they are not saved across remounts.
Changing the configuration in Lean replaces those overrides. Keep reusable settings
in a Lean `Config` value. PTracker uses polling controls instead of cursor pinning;
**Manual** disables periodic refresh and automatic removal, while still allowing
the initial read and explicit refresh/removal.
**Auto-refresh** controls polling only. The always-visible retention message describes
whether completed tasks will be deleted. **Delete** removes a task from the shared registry
for the file, so it disappears from all panels viewing that registry.

InfoTreeExplorer clamps children per node to 1–100 and tree depth to 1–64, and marks
truncated branches. These limits bound rendered tree expansion, not info collection
or every snapshot-summary traversal. PTracker clamps polling to 100–60,000 ms and
retention to 1–3,600 seconds. Automatic removal deletes completed registry entries,
so another panel viewing the same registry will also stop seeing them.

## Tests

Run all tests with Node.js 22 or later on `PATH` (no npm install is needed):

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
- can compile on-the-fly and diff outputs,
- restores option values from the backend schema with the **Defaults** button.

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

The panel refreshes automatically and reconnects when the InfoView RPC session
changes. Replies from an earlier session are discarded.

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

Run the same local gate as CI:

```bash
lake build
lake check-test
lake test
```

For focused regression checks:

```bash
lake env lean tests/Rpc/QualifiedMethodNames.lean
lake env lean tests/InfoTreeExplorer/AtPos.lean
lake env lean tests/DocString/Resolver.lean
lake env lean tests/DocString/VersoLean.lean
lake env lean tests/Examples/Smoke.lean
lake env lean tests/Widget/Runtime.lean
lake env lean tests/Widget/Server.lean
```

CI (`.github/workflows/lean_action_ci.yml`) builds the package and runs all suites
registered in `lakefile.toml` using the toolchain pinned in `lean-toolchain`.
