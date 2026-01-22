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
