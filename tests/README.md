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

- `tests/CE/RpcAndSchema.lean`: CE widget RPC naming and option-schema coverage.
- `tests/CE/Compilation.lean`: actual IR/LCNF recompilation in a module with postponed compilation.
- `tests/PTracker/RpcContracts.lean`: PTracker RPC naming coverage.
- `tests/InfoTreeExplorer/AtPos.lean`: InfoTree explorer at-pos regression checks.
- `tests/InfoTreeExplorer/RpcContracts.lean`: InfoTree explorer RPC contract checks.
- `tests/Lib/Resource.lean`: `DevWidgets.Lib.withResource`/`withResourceUnit` behavior.
- `tests/Rpc/QualifiedMethodNames.lean`: fully-qualified widget RPC method names and executable registrations.
- `tests/DocString/Resolver.lean`: cursor resolution, doc-comment previews, and declaration candidates.
- `tests/DocString/VersoLean.lean`: rendering of elaborated Verso docstrings and Lean code.
- `tests/Widget/Runtime.lean`: runs the shipped JavaScript with Lean-serialized fixtures through
  `tests/Widget/runtime.mjs`, checking CE defaults, InfoTreeExplorer URI decoding, and PTracker
  session changes, late RPC replies/deletes, and cleanup. It also checks pin/follow across files,
  refresh invalidation, presets, typed props, configuration changes, and reset behavior.
  The hook driver controls effects and
  timers; it does not test browser layout or replace a VSCode InfoView smoke test.
- `tests/Widget/Activation.lean`: panel-free API imports, RPC registration, typed configuration, and local hiding.
- `tests/Widget/DefaultActivation.lean`: short imports activate each panel exactly once.
- `tests/Widget/Server.lean`: starts a real Lean language server through
  `tests/Widget/server.mjs` and checks panel activation, section scoping, serialized
  configuration, JavaScript retrieval, all six widget RPC endpoints, repeated CE
  recompilation, edits, and progress registry sharing/isolation across sessions/files.
  Fixtures are opened as in-memory documents; the test does not modify source files.
  Requests have timeouts and the server is shut down after success or failure.
- `tests/Examples/Smoke.lean`: import-only smoke test for all runnable demos in `examples/`.

Most files use Lean-native checks (`#eval` + `throwError`/`IO.userError`), and smoke suites
use import/elaboration success. Any failure stops `lake test`. Lake tracks the JavaScript
drivers as input dependencies so edits to them invalidate the test build.

To run the server checks directly after `lake build`:

```bash
lake env node tests/Widget/server.mjs
```

These checks exercise the real Lean RPC protocol; browser layout and VSCode
InfoView integration still need an editor smoke test.
