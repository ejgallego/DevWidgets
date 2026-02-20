# Lean Dev Widgets

- **DevWidgets.CE**: Interactive IR and LCNF "Compiler Explorer" like widget.
- **DevWidgets.PTracker**: A progress tracker widget that allows to display progress before elaboration has finished.
- **DevWidgets.InfoTreeExplorer**: Interactive Syntax and InfoView Explorer
- **DevWidgets.DHover**: Displays internal Lean information on hover, like Snapshot status, etc...

See some [examples](./examples).

## `DevWidgets.CE`

An interactive complement to some `set_option trace.Compiler.*`, shows
IR and LCNF if available, with folding.

## `DevWidgets.PTracker`

When you need more granularity than incremental snapshot reporting,
your elaboration routine can use this widget to display progress.

## `DevWidgets.InfoTreeExplorer`

An interactive complement to `set_option trace.Elab.Info`. It shows infoTree, snapsho

## TODO:

- Refactor Snapshot code into a lib for common consumption.
- Common panel for all widgets
- PTracker Report stats, histogram
