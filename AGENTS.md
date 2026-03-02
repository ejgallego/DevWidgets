# AGENTS.md

## Repository Context

This repository (`dev-widgets`) provides Lean 4 developer-focused InfoView widgets.
Current target toolchain is `leanprover/lean4:v4.29.0-rc3` (see `lean-toolchain`).

Main modules:
- `DevWidgets.CE`: compiler exploration panel (IR/LCNF + options).
- `DevWidgets.PTracker`: progress tracking API/widget for long-running elaboration.
- `DevWidgets.InfoTreeExplorer`: cursor-focused info tree explorer.
- `DevWidgets.DocString`: cursor-focused docstring inspector (currently draft/demo).

## Where To Look First

- Main package docs: `README.md`
- Change log: `CHANGES.md`
- Widget code: `DevWidgets/**`
- Runnable demos: `examples/**`
- Tests and RPC contract checks: `tests/**`

Useful example entry points:
- `examples/CE.lean`
- `examples/PTracker.lean`
- `examples/InfoViewExplorer.lean`
- `examples/InfoTreeFocused.lean`
- `examples/DocString.lean`

## Development Workflow

Build:
```bash
lake build
```

Run all tests:
```bash
lake test
```

Run important regression checks explicitly:
```bash
lake env lean tests/Rpc/QualifiedMethodNames.lean
lake env lean tests/InfoTreeExplorer/AtPos.lean
lake env lean tests/DocString/Resolver.lean
lake env lean tests/DocString/VersoLean.lean
lake env lean tests/Examples/Smoke.lean
```

## Contribution Workflow

Before opening a PR, run this minimum local gate:
```bash
lake build
lake check-test
lake test
```

Before pushing any branch (including `main`), run the same local CI gate:
```bash
lake build
lake check-test
lake test
```

When touching specific areas, also run focused checks:
- RPC method names/contracts: `lake env lean tests/Rpc/QualifiedMethodNames.lean`
- InfoTree explorer behavior: `lake env lean tests/InfoTreeExplorer/AtPos.lean` and `lake env lean tests/InfoTreeExplorer/RpcContracts.lean`
- DocString resolution/rendering: `lake env lean tests/DocString/Resolver.lean` and `lake env lean tests/DocString/VersoLean.lean`
- CE schema/RPC surface: `lake env lean tests/CE/RpcAndSchema.lean`
- PTracker RPC surface: `lake env lean tests/PTracker/RpcContracts.lean`
- Lib resource helpers: `lake env lean tests/Lib/Resource.lean`

PR hygiene expectations:
- Keep changes scoped to one widget or one cross-cutting concern when possible.
- Update `README.md` examples/import docs when API or UX changes.
- Add an entry under `CHANGES.md` for user-visible behavior changes.
- If a module is draft/demo quality (for example `DocString`), mention compatibility expectations in PR notes.

## Commit Message Conventions

Use short, scoped subjects:
- Format: `[Area] imperative summary`
- Examples: `[DocString] fix fallback for unresolved identifiers`, `[InfoTreeExplorer] qualify RPC method name`

Guidelines:
- Keep subject line under ~72 characters when possible.
- Use recognized areas: `CE`, `PTracker`, `InfoTreeExplorer`, `DocString`, `Lib`, `Tests`, `CI`, `Docs`.
- In the body, include:
  - what changed,
  - why it changed,
  - how it was validated (commands run).

## Notes For Agents

- Create git worktrees under `.worktrees/` (plural) to match local testing setup expectations.
- Prefer fully-qualified RPC method names in widget JS and tests.
- Keep docs/examples aligned with API changes, especially for draft modules like `DocString`.
- When adding RPC/widget behavior, include regression coverage under `tests/`.
- Follow existing Lean style and keep examples runnable in VSCode InfoView.
