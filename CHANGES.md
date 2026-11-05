unreleased
----------

- [PTracker] Reconcile overlapping reads/deletes; make shared deletion idempotent and return Unit. Remove unused counters, distinguish failed/cancelled outcomes with an elaboration bracket, and expose explicit headless retention by age/count.
- [CE] Derive availability from code results, embed the canonical schema, remove metadata/value wrappers and parsed debug strings, and compile once for both IR/LCNF outputs. RPC payload changes are documented in README.
- [InfoTreeExplorer] Return structured focused previews, remove redundant summaries and unused full fingerprint mode, and bound inspection by node/depth budgets before computing facts and paths. Mark partial captures explicitly.
- [DocString] Reuse InfoView's bundled Markdown renderer, remove the CDN loader and identity-only Markdown helper module, filter Verso link/image schemes, and use theme colors for readable format badges.
- [Tests] Cover same-session deletion ordering, shared deletion, bracket failure/interruption, retention, structured previews and HTML boundaries. Harden browser/server cleanup and replace redundant JavaScript source-string checks with behavioral coverage.

- [Lib] Add section-local `configure_panel_widget` replacement to avoid duplicate imported panels, and preserve keyboard focus when toggling Pin/Follow.
- [PTracker] Use wrapping task cards with visible Delete actions, explicit Auto-refresh labeling, and always-visible shared-registry retention information.
- [CE] Put output before collapsed inspector settings and use distinct light/dark syntax palettes with high-contrast theme support.
- [InfoTreeExplorer] Show focused results first, collapse detailed paths and trees, wrap metadata, and use theme foregrounds for readable node labels.
- [Tests] Add an optional real InfoView browser suite for keyboard focus, narrow layout, syntax contrast, retention information, and deletion, with a dedicated interactive fixture.
- [Tests] Exercise independent activation, configured panels, all widget RPC endpoints, edits, and cross-file progress isolation against a real Lean server in `lake test`.
- [Lib] Share cursor pin/follow, refresh, reset, and configuration-override behavior across independent widgets.
- [CE] Add typed panel configuration and a verbose inspection preset; reset can restore Lean-supplied defaults.
- [InfoTreeExplorer] Add focused/detailed presets, configurable child/depth limits, and explicit truncation markers.
- [InfoTreeExplorer] Preserve retained results while loading and pin them with their original source position.
- [DocString] Add configurable panel height and shared cursor controls; the widget remains draft/demo quality.
- [PTracker] Enable the panel from the short import and provide a panel-free `.API` import, configurable polling/retention, and Live/Quiet/Manual controls.
- [Docs] Document independent activation and `.API` imports for all widgets, with a runnable configuration example.
- [CI] Update the development toolchain to `leanprover/lean4:v4.36.0-rc2`.
- [CE] Adapt recompilation to Lean 4.36's compiler entry point and postponed module compilation.
- [DocString] Adapt Verso custom elements and preserve fallback text for deferred elements; the widget remains draft/demo quality.
- [InfoTreeExplorer] Recognize choice-resolution info nodes introduced by the new toolchain.
- [Tests] Cover compiler execution, deferred Verso rendering, and executable RPC registration under Lean 4.36. CE and DocString register their RPC handlers from the documented root imports.

- [CE] Fix the Defaults button to read serialized schema field names, preserving backend boolean and numeric defaults.
- [PTracker] Refresh on RPC session changes and ignore late reads/deletes from earlier sessions or unmounted panels.
- [Tests] Add JavaScript runtime regression checks with Lean-serialized fixtures; `lake test` now requires Node.js 22 or later.
- [Docs] Align test-suite documentation and CI instructions with the pinned toolchain and complete local gate.

Earlier development (before this PR)
-----------------------------------

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
