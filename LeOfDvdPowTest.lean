import Mathlib

variable {α} [Dvd α] [HPow α ℕ α] [LT α] [One α]

example {a : α} {b c : ℕ} (ha : 1 < a) /- This condition needs to be changed/generalized for `Polynomial`. -/ (h : a ^ b ∣ a ^ c) : b ≤ c := by
  hint

#synth UniqueFactorizationMonoid (Polynomial ℤ)
#synth UniqueFactorizationMonoid (Polynomial ℝ)
