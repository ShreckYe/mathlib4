import Mathlib

example (f : ℝ → ℝ) (h : f.Injective) (s : Set ℝ) : Set.InjOn f s := by
  exact h.injOn

#check Set.BijOn.injOn

example (f : ℝ → ℝ) (h : f.Surjective) (t : Set ℝ) : Set.SurjOn f Set.univ t := by
  exact Function.Surjective.surjOn h t

#check Set.exists_injOn_iff_injective
