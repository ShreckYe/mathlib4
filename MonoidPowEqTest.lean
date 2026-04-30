import Mathlib

#check CancelMonoid
#check CommMonoid
#check UniqueFactorizationMonoid
#check CancelMonoidWithZero
#check Prime

example (α : Type*) [CommMonoidWithZero α] [IsCancelMulZero α] : UniqueFactorizationMonoid α := by
  --infer_instance
  sorry

#check IsCancelMulZero

-- also check related code for $p$-adic valuation

#check FreeMonoid

example {α : Type*}
    [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [GCDMonoid α] {a b : α} {m n : ℕ} (hmn : m.gcd n = 1) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  hint

#check CancelCommMonoid
#check exists_associated_pow_of_mul_eq_pow
