import Mathlib

def f a := 2 * a

def f2 {T : Type} [Mul T] [OfNat T 2] (a : T) :=
  2 * a

example : f 1 = 2 :=
  rfl

example : Eq (f 1) 2 :=
  rfl

example : f2 1 = 2 :=
  refl 2

lemma my_great_theorem : f2 1 = 2 :=
  refl 2

#check Eq

#eval f 124212
--#native_eval f 1

--def main : IO Unit :=
--  IO.println s!"f 3 = {f 3}"

#check List.Vector
#check ℕ
#check Nat

#check Nat.Prime 5

example : Nat.Prime 2 := by
  decide

example a : a ≥ 2 ∧ a ≤ 2 → a = 2 := by
  grind
