import Mathlib

open List


example a b c : {a, b} ≤ ({a, b, c} : Multiset ℝ) := by
  simp [Multiset.cons_le_cons]

example a b c : {a, b} ≤ ({a, b, c} : Multiset ℝ) := by
  simp

example a b : {a, b} ≤ ({a, a, b, b} : Multiset ℝ) := by
  simp


example a b c : {a, b} ⊆ ({a, b, c} : Multiset ℝ) := by
  simp


example a b c : {a, b} ⊆ ({a, b, c} : Finset ℝ) := by
  simp

example a b : {a, b} ≤ ({a, a, b, b} : Finset ℝ) := by
  simp


example a b c : [a, b] <+ ([a, b, c] : List ℝ) := by
  simp

example a b c : [a, b] <+ ([a, b, c] : List ℝ) := by
  simp only [cons_sublist_cons, Sublist.refl, Sublist.cons]
