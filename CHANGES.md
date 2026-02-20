unreleased
----------

- [PTracker] First usable version, with resource bracket.
- [InfoTreeExplorer] Refactor to cursor-position RPC (`infoTreeAtPos`), remove `#infotree_explorer` polling workflow, and add richer focused-path visualization plus regression coverage.
- [InfoTreeExplorer] Use fully-qualified RPC method names from widget JS (`DevWidgets.InfoTreeExplorer.infoTreeAtPos`).
- [DocString] New cursor-focused docstring widget (`DevWidgets.DocString`) with Markdown/Verso rendering, declaration fallback resolution, examples, and regression tests.
- [DocString] Marked as draft/demo quality in docs while API/UX stabilizes.
- [CI] Build `DevWidgets.DocString` by default and run RPC/docstring regression tests in CI.
- [CI] Target nightly Lean toolchain only for this development cycle.
- [Docs] Expand `README.md` with widget usage, examples, and reproducible local test commands.
