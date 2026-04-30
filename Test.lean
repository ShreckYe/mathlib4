import Mathlib

example {α : Type*}
    [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [GCDMonoid α] {a b : α} {m n : ℕ} (hmn : GCDMonoid.gcd m n = 1) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  hint

#check CancelCommMonoid
#check exists_associated_pow_of_mul_eq_pow
