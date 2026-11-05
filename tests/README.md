# DevWidgets Tests

This package uses Lake's test runner.

The widget runtime and server suites also require Node.js 22 or later on `PATH`. They use
only Node built-ins; no npm install is needed. Run commands from the repository root.

## Run all tests

```bash
lake test
```

## Check test-driver configuration

```bash
lake check-test
```

## Current suites

- `tests/CE/RpcAndSchema.lean`: canonical CE option-schema coverage.
- `tests/CE/Compilation.lean`: actual IR/LCNF recompilation in a module with postponed compilation.
- `tests/PTracker/RpcContracts.lean`: progress success/failure/interruption, idempotent closure/deletion, and headless retention.
- `tests/InfoTreeExplorer/AtPos.lean`: InfoTree explorer at-pos regression checks.
- `tests/InfoTreeExplorer/RpcContracts.lean`: structured preview round trips and node-budget checks.
- `tests/Lib/Resource.lean`: `DevWidgets.Lib.withResource`/`withResourceUnit` behavior.
- `tests/Rpc/QualifiedMethodNames.lean`: executable registration of all six RPC methods (actual frontend names are checked by the runtime suite).
- `tests/DocString/Resolver.lean`: cursor resolution, doc-comment previews, and declaration candidates.
- `tests/DocString/VersoLean.lean`: rendering of elaborated Verso docstrings and Lean code.
- `tests/Widget/Runtime.lean`: runs the shipped JavaScript with Lean-serialized fixtures through
  `tests/Widget/runtime.mjs`, checking CE defaults, InfoTreeExplorer position/budget decoding, and PTracker
  session changes, both same-session read/delete orderings, shared deletion, and cleanup. It also checks pin/follow across files,
  refresh invalidation, presets, typed props, configuration changes, reset behavior, multiline
  focused previews, accurate availability, and the Markdown-to-host-renderer boundary.
  The hook driver controls effects and
  timers; it does not test browser layout or replace a VSCode InfoView smoke test.
- `tests/Widget/Activation.lean`: panel-free API imports, RPC registration, typed configuration, and local hiding.
- `tests/Widget/DefaultActivation.lean`: short imports activate each panel exactly once;
  repeated `configure_panel_widget` replaces imported instances and restores them after a section.
- `tests/Widget/Server.lean`: starts a real Lean language server through
  `tests/Widget/server.mjs` and checks panel activation, section scoping, serialized
  configuration, JavaScript retrieval, all six widget RPC endpoints, repeated CE
  recompilation, edits, and progress registry sharing/isolation across sessions/files.
  Fixtures are opened as in-memory documents; the test does not modify source files.
  Requests and the whole run have timeouts; malformed transport data rejects pending
  requests, and the server is shut down after success or failure.
- `tests/Examples/Smoke.lean`: import-only smoke test for all runnable demos in `examples/`.

Most files use Lean-native checks (`#eval` + `throwError`/`IO.userError`), and smoke suites
use import/elaboration success. Any failure stops `lake test`. Lake tracks the JavaScript
drivers as input dependencies so edits to them invalidate the test build. Lean checks
are cached by Lake when their inputs are unchanged; repeated `lake test` invocations
do not necessarily execute every check again.

To run the server checks directly after `lake build`:

```bash
lake env node tests/Widget/server.mjs
```

## Actual InfoView browser checks

`tests/Widget/browser.mjs` checks keyboard focus across Pin/Follow, narrow-pane task
layout, syntax-text contrast, visible retention information, collapsed inspector settings, tree-budget
changes, offline Markdown/HTML policy, and task deletion
in a real VSCode InfoView. It is optional and uses only Node built-ins. It is separate
from `lake test`, which does not require VSCode or a graphical display.

After `lake build`, start an **isolated** VSCode window with a temporary profile and
the Lean extension installed:

```bash
code --new-window --user-data-dir /tmp/dev-widgets-ui --remote-debugging-port=9231 . tests/Widget/Interactive.lean
```

In that window, place the cursor on `usabilityCounter` in the final `#check`, open
Lean InfoView, and wait for the three sample tasks and compiler output. Then run:

```bash
# Arguments: debugging port, window width, optional screenshot destination.
node tests/Widget/browser.mjs 9231 900 /tmp/dev-widgets-ui.png
```

Run it in both light and dark themes, and at a wider window width (for example 1440).
Use **Lean 4: Server: Restart File** before each run to recreate the deleted sample task.
The script drives the focused controls and deletes the completed fixture task, so use
the dedicated window and fixture. Close the window when finished. Inspect the resulting
screenshots for theme contrast and visual hierarchy; automated checks do not replace that review.
