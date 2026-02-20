import DevWidgets.InfoTreeExplorer
import Lean

open Lean

/-!
# Focused Details Demo

This file is designed to compare:
- `Path to Cursor` (structural containment)
- `Focused details` (elaboration payloads / outputs)

Try placing the cursor on:
1. `n` inside `triple! (wrapSucc! n)`
2. `Nat.succ` in `focusA`
3. `simp` in `focusProof`

The path is usually short and structural; focused details add
the local elaboration output that explains *what* was produced there.
-/

namespace InfoTreeFocusedDemo

syntax "triple!" term : term
macro_rules
  | `(triple! $t) => `(($t) + ($t) + ($t))

macro "wrapSucc!" t:term : term => `(Nat.succ ($t))

def focusA (n : Nat) : Nat :=
  let a := triple! (wrapSucc! n)
  let b := (fun x => x + 1) a
  b

def focusB (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | y :: ys =>
    let z := triple! (Nat.succ y)
    z + ys.length

example (n : Nat) : focusA n = focusA n := by
  rfl

example (xs : List Nat) : focusB xs = focusB xs := by
  rfl

example (n : Nat) : n + 0 = n := by
  -- Cursor on `simp` is useful for focused tactic details.
  simp

#eval focusA 4
#eval focusB [1, 2, 3]

end InfoTreeFocusedDemo
