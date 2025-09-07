import Mathlib

example (x : ℝ) : deriv (fun x ↦ x * 2) x = 2 := by
  simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_mul, deriv_id'', one_mul,
    deriv_const', mul_zero, add_zero]

example (x : ℝ) : deriv (fun x ↦ 2 * x) x = 2 * 1 := by
  simp
