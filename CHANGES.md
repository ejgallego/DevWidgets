unreleased
----------

- [PTracker] First usable version, with resource bracket.
- [InfoTreeExplorer] Refactor to cursor-position RPC (`infoTreeAtPos`), remove `#infotree_explorer` polling workflow, and add richer focused-path visualization plus regression coverage.
- [InfoTreeExplorer] Use fully-qualified RPC method names from widget JS (`DevWidgets.InfoTreeExplorer.infoTreeAtPos`).
- [InfoTreeExplorer] Use Lean core `Info.stx`/`Info.contains` helpers in explorer internals to reduce ad-hoc info-tree plumbing.
- [DocString] New cursor-focused docstring widget (`DevWidgets.DocString`) with Markdown/Verso rendering, declaration fallback resolution, examples, and regression tests.
- [DocString] Marked as draft/demo quality in docs while API/UX stabilizes.
- [CI] Build `DevWidgets.DocString` by default and run RPC/docstring regression tests in CI.
- [CI] Move project toolchain target to `leanprover/lean4:v4.29.0-rc3`.
- [Docs] Expand `README.md` with widget usage, examples, and reproducible local test commands.
- [Tests] Add `tests/Examples/Smoke.lean` and an `Examples` Lean library so demos are compiled during `lake test`.
