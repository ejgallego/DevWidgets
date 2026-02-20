import DevWidgets.InfoTreeExplorer
import Lean

open Lean

/- Move the cursor around this file to explore diverse infotree nodes. -/

namespace InfoViewExplorerDemo

inductive Expr where
  | lit : Nat → Expr
  | add : Expr → Expr → Expr
  deriving Repr, Inhabited

structure Config where
  fuel : Nat
  verbose : Bool
  deriving Repr

class Scalable (α : Type) where
  scale : Nat → α → α

instance : Scalable Nat where
  scale k x := k * x

instance : Scalable (List α) where
  scale k xs := (List.replicate k xs).foldr (· ++ ·) []

syntax "myNat%" num : term
macro_rules
  | `(myNat%$n:num) => `(($n : Nat))

macro "twice!" t:term : term => `(($t) + ($t))

notation "⟪" n "⟫" => List.replicate n ()

partial def evalExpr : Expr → Nat
  | .lit n => n
  | .add a b => evalExpr a + evalExpr b

/-- Recursive definition with explicit termination argument. -/
def foldDown (n : Nat) (acc : Nat := 0) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => foldDown k (acc + k + 1)
termination_by n

/-- Mix of `let`, `match`, and typeclass inference. -/
def mixedTerm (c : Config) (xs : List Nat) : Nat :=
  let scaled := Scalable.scale c.fuel xs
  let base := twice! (myNat%7)
  match scaled with
  | [] => base
  | y :: ys =>
    let z := if c.verbose then y + ys.length else y
    z + foldDown c.fuel

def sampleExpr : Expr := .add (.lit 3) (.add (.lit 10) (.lit 4))

def pairMap (xs : List Nat) : List (Nat × Nat) :=
  xs.map (fun x => (x, x * x))

example (a b : Nat) : a + b = b + a := by
  simp [Nat.add_comm]

example (xs : List Nat) : xs.reverse.reverse = xs := by
  simp

example (n : Nat) : foldDown (n + 1) 0 = foldDown n (n + 1) := by
  simp [foldDown]

example : (fun x : Nat => x + 1) 3 = 4 := by
  decide

#check Expr.add
#check Scalable.scale
#check (inferInstance : Scalable Nat)
#print foldDown

#eval evalExpr sampleExpr
#eval mixedTerm { fuel := 4, verbose := true } [1, 2, 3]
#eval pairMap [2, 3, 5]
#eval (⟪3⟫).length

end InfoViewExplorerDemo
