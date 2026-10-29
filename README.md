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
| InfoTreeExplorer | `maxChildren`, `maxDepth`, `maxNodes` | `InfoTreeExplorer.Config.focused`, `.detailed` |
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

InfoTreeExplorer clamps children per node to 1–100, depth to 1–64, and inspected nodes
per tree to 1–16,384 (default 4,096). It bounds traversal before computing paths and
facts, and labels partial captures. Counts and focused results then describe only the
captured portion. These limits do not bound Lean's original elaboration work or the
cost of formatting an individual expression. PTracker clamps polling to 100–60,000 ms
and retention to 1–3,600 seconds. Deletion is shared by panels viewing the same registry.

## `DevWidgets.CE`

Compiler Explorer widget.

This is an interactive complement to `set_option trace.Compiler.*`:

- shows IR and LCNF (when available),
- supports folding and syntax highlighting,
- exposes pretty-printer/compiler tuning options,
- can recompile on demand and explain which compiler options differ from the cursor context,
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

For tactics and commands, use `withElabProgressRef` with the same arguments. It
records Lean interrupts as **Cancelled**, other exceptions as **Failed**, and rethrows
both unchanged. Call `Lean.Core.checkInterrupted` at safe points in long loops; see
[`examples/PTracker.lean`](./examples/PTracker.lean).

The generic `withProgressRef` records an unsuccessful action as **Failed** because
`MonadFinally` alone cannot classify exceptions. Explicit `ref.close (interrupted := true)`
records cancellation. Terminal outcomes are preserved by repeated closure, and deleting
an already-absent task succeeds. Running tasks cannot be deleted.

Closing records an outcome; it does not delete an entry. Automatic retention is owned
by active panels. With no panel, or with automatic removal disabled, entries remain
until explicit deletion/pruning or worker exit. Headless callers can apply their own
retention policy without starting a background worker:

```lean
-- Inside an IO-capable action: keep at most 100 completed tasks, all younger than a minute.
discard <| DevWidgets.PTracker.pruneProgressRefs {
  maxAgeMs? := some 60000, maxCompleted? := some 100
}
```

Pruning never removes running tasks. Multiple panels share retention: the shortest
active retention policy can remove entries also displayed by other panels.

The panel refreshes automatically and reconnects when the InfoView RPC session
changes. Replies from an earlier session are discarded, and reads that overlap a
successful deletion cannot restore the deleted row.

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
- Uses InfoView's bundled Markdown component, with the same HTML policy as hover docs;
  there is no CDN script, renderer download, or renderer-loading effect.
- Renders Verso with escaped text and attributes; links/images reject executable URL schemes.
  Only this server-generated Verso HTML enters the HTML rendering path. Documentation may
  still contain external links/images; the renderer itself works offline.
- Provides raw doc-comment preview when elaborated docs are unavailable.
- Uses fully-qualified RPC call `DevWidgets.DocString.docAtPos`.

Import:

```lean
import DevWidgets.DocString
```

Example file: `examples/DocString.lean`.

## Tests

With Node.js 22 or later on `PATH` (no npm install), run the same local gate as CI:

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

See [`tests/README.md`](./tests/README.md) for coverage and the optional real InfoView
checks. Those checks run separately from CI and cover keyboard focus, layout, themes,
and the host Markdown renderer.

## Internal contracts and compatibility

This pre-1.0 PR updates both producers and consumers of the widget RPC payloads:

- CE code availability comes from `ir`/`lcnf` result constructors; the redundant `hasIR`
  field is removed. Code options contain plain typed values, with static metadata exposed
  once by `ceOptionSchema` and embedded into the widget from the same Lean definition.
  `recompileOptionDiffs` contains `{id, requested, context}` records;
  `forceRecompileRequested` and `shouldGenerateError` replace parsed debug strings.
- InfoTree `focused` entries contain `{title, path, output}`, where `path` is an array.
  `truncated` identifies partial captures; `summary` is a status message, not a second
  Markdown representation of the capture. The redundant request `uri` field is removed;
  RPC session routing selects the file, and retained UI results preserve their source position.
- Progress deletion returns `Unit`; success includes an already-absent entry.
  Status now includes `failed`, and the unused registry counters are removed.
- The identity-only `DevWidgets.DocString.Markdown` helper module is removed.
  Import `DevWidgets.DocString.API` for the supported draft API.

Shared controls own panel-local settings and frozen snapshots. Each widget owns its
RPC contract and task-specific behavior; there is no shared global widget store.
The retained InfoTree result behavior builds on [PR #8](https://github.com/ejgallego/DevWidgets/pull/8);
retained and pinned results keep their source position rather than borrowing the new cursor.
