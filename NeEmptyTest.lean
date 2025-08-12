import Mathlib

example (s : Multiset ℕ) (h : s ≠ ∅) : ∃ n t, s = n ::ₘ t := by
  sorry

example (s : Multiset ℕ) (h : s.Nonempty) : ∃ n t, s = n ::ₘ t := by
  sorry

example (s : Multiset ℕ) (h : s ≠ ∅) : ∃ n, n ∈ s:= by
  exact Multiset.exists_mem_of_ne_zero h

example (s : Finset ℕ) (h : s ≠ ∅) : ∃ n t, s = insert n t := by
  sorry

example (s : Finset ℕ) (h : s.Nonempty) : ∃ n t, s = insert n t := by
  sorry

example (s : List ℕ) (h : s ≠ ∅) : ∃ n t, s = n :: t := by
  exact List.ne_nil_iff_exists_cons.mp h
