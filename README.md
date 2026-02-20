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

This widget allows tactics and commands to report progress in a more
fine-grained way than increment snapshot reporting.

The main API this Widget provides is a `ProgressRef` resource bracket:

```lean
def withProgressRef [Monad m] [MonadLiftT IO m] [MonadFinally m]
    (totalSteps? : Option Nat)
    (description : String)
    (initialLabel : String := "")
    (act : ProgressRef → m α) : m α := do
```

This ensures that `act` will properly release the `ProgressRef` on cancellation or error.

Clients can report progress with:

```lean
def ProgressRef.update
    (ref : ProgressRef)
    (stepsDone : Nat)
    (label? : Option String := none) : IO Unit
```

Enable the Widget with `show_panel_widgets [progressWidget]`.

See the [example](./examples/PTracker.lean) for more information.

Tip: Use `Lean.Core.checkInterrupted` in your elaboration code to
check for interruption requests at safe points.

## `DevWidgets.InfoTreeExplorer`

An interactive complement to `set_option trace.Elab.Info`. It shows infoTree, snapsho

## TODO:

- Refactor Snapshot code into a lib for common consumption.
- Common panel for all widgets
- PTracker Report stats, histogram
