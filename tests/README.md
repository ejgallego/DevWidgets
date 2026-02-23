# DevWidgets Tests

This package uses Lake's test runner.

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
- `tests/PTracker/RpcContracts.lean`: PTracker RPC naming coverage.
- `tests/InfoTreeExplorer/AtPos.lean`: InfoTree explorer at-pos regression checks.
- `tests/InfoTreeExplorer/RpcContracts.lean`: InfoTree explorer RPC contract checks.
- `tests/Lib/Resource.lean`: `DevWidgets.Lib.withResource`/`withResourceUnit` behavior.
- `tests/Examples/Smoke.lean`: import-only smoke test for all runnable demos in `examples/`.

Most files use Lean-native checks (`#eval` + `throwError`/`IO.userError`), and smoke suites
use import/elaboration success. Any failure stops `lake test`.
