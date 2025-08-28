import Mathlib

variable {α} [Dvd α] [HPow α ℕ α]

example {a : α} {b c : ℕ} : a ^ b ∣ a ^ c -> b ≤ c := by
  hint
