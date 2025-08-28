import Mathlib

variable {α} [Dvd α] [HPow α ℕ α] [LT α] [One α]

example {a : α} {b c : ℕ} (ha : 1 < a) (h : a ^ b ∣ a ^ c) : b ≤ c := by
  hint
