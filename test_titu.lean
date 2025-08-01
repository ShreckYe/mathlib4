import Mathlib.Algebra.Order.BigOperators.Ring.Finset

#check Finset.sq_sum_div_le_sum_sq_div
#check Finset.titu_lemma
#check Finset.Real.titu_lemma

-- Test the real version with a simple example
example : let s := ({0, 1} : Finset ℕ)
          let f : ℕ → ℝ := fun i => if i = 0 then 1 else 2
          let g : ℕ → ℝ := fun i => if i = 0 then 1 else 1
          (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i := by
  simp only [Finset.sum_insert, Finset.not_mem_singleton, Finset.sum_singleton]
  norm_num
  apply Finset.Real.titu_lemma
  intro i hi
  simp at hi
  cases hi with
  | inl h => simp [h]
  | inr h => simp [h]
