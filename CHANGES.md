unreleased
----------

- [PTracker] First usable version, with resource bracket.
- [InfoTreeExplorer] Refactor to cursor-position RPC (`infoTreeAtPos`), remove `#infotree_explorer` polling workflow, and add richer focused-path visualization plus regression coverage.
- [InfoTreeExplorer] Use fully-qualified RPC method names from widget JS (`DevWidgets.InfoTreeExplorer.infoTreeAtPos`).
- [DocString] New cursor-focused docstring widget (`DevWidgets.DocString`) with Markdown/Verso rendering, declaration fallback resolution, examples, and regression tests.
- [CI] Build `DevWidgets.DocString` by default and run RPC/docstring regression tests in CI.
- [CI] Add a stable Lean lane as non-blocking, while keeping nightly as the required lane.
- [Docs] Expand `README.md` with widget usage, examples, and reproducible local test commands.
