import DevWidgets.CE
import DevWidgets.DocString
import DevWidgets.InfoTreeExplorer
import DevWidgets.PTracker

/-!
Fixture for the optional real InfoView browser checks. Open in an isolated VSCode
window and place the cursor on `usabilityCounter` in the final `#check`.
The task states below are static UI samples, not background work.
-/

-- Exercise replacement after the short import and keep tasks available for inspection.
configure_panel_widget DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.manual

/-- Increment a counter.

This longer documentation paragraph should wrap without horizontal scrolling in a narrow
InfoView pane. Use `usabilityCounter 3` to obtain the next value, `4`.

**Bundled Markdown check**

<span data-devwidgets-raw="yes" onclick="window.devWidgetsUnsafe = true">raw HTML</span>
[Unsafe link](javascript:alert(1))
-/
def usabilityCounter (count : Nat) : Nat := count + 1

#eval show IO Unit from do
  let done ← DevWidgets.PTracker.ProgressRef.create (some 200) "Completed sample"
  done.update 200 (some "All dependencies checked")
  done.close (interrupted := false)
  let active ← DevWidgets.PTracker.ProgressRef.create (some 500) "Running sample with a long declaration name"
  active.update 237 (some "MyProject.Analysis.Simplification.normalizeExpressionWithAVeryLongName")
  let unknown ← DevWidgets.PTracker.ProgressRef.create none "Unbounded sample"
  unknown.update 12 (some "Reading imported metadata")

#check usabilityCounter
