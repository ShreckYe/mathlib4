import Mathlib

example (f g : ℕ → ℕ) : f * g = fun x ↦ f x * g x := by
  --simp
  conv_lhs => unfold HMul.hMul
  unfold instHMul
  dsimp
  unfold Mul.mul
  dsimp [Pi.instMul]
  sorry
