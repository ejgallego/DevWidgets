import DevWidgets.SnapshotExplorer

/-!
Open InfoView at `snapshotAnchor` and pin that InfoView position while editing below it.
The panel observes the whole file, so the anchor can stay on a completed command.
Use Freeze capture to preserve a serialized view; Resume live follows the current file again.
-/

def snapshotAnchor : Nat := 42
#check snapshotAnchor

configure_panel_widget DevWidgets.SnapshotExplorer.snapshotWidget with
  ({ intervalMs := 500, maxCommands := 200, maxNodes := 128 } : DevWidgets.SnapshotExplorer.Config)

-- Select this theorem to inspect declaration and tactic snapshots.
theorem snapshotExample (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

-- Uncomment to keep elaboration pending briefly. Keep InfoView pinned above this line.
-- #eval IO.sleep 3000

#check snapshotExample
