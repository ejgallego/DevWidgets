import DevWidgets.CE
import DevWidgets.DHover

/--
Place the cursor on `cfgDemo`, `loopAcc`, or `matchDemo` below to inspect
their IR/LCNF in the widget.
-/
def hello : String := "widget demo"

/-- Branch-heavy function to produce multiple control-flow blocks. -/
def cfgDemo (n : Nat) : Nat :=
  if n == 0 then
    0
  else if n % 2 == 0 then
    let k := n / 2
    if k > 10 then
      k + 3
    else
      k + 1
  else
    let m := n * 3 + 1
    if m % 5 == 0 then
      m - 5
    else
      m + 7

/-- Tail-recursive helper: useful for seeing jumps/joins in LCNF. -/
def loopAcc (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 =>
    let acc' := if k % 2 == 0 then acc + k else acc + 2 * k
    loopAcc k acc'

/-- Pattern-match demo with several alternatives. -/
def matchDemo (x : Nat × Nat) : Nat :=
  match x with
  | (0, b) => b
  | (a + 1, 0) => a + 1
  | (a + 1, b + 1) =>
    if a < b then b - a else a - b

#eval cfgDemo 27
#eval loopAcc 12 0
#eval matchDemo (5, 3)
#check Nat.succ
