import Mathlib

lemma modEq_iff_dvd {α : Type} [AddCommGroup α] [Semigroup α] (p a b : α) : a ≡ b [PMOD p] ↔ p ∣ (b - a) := by
  constructor
  . intro h
    simp [AddCommGroup.ModEq] at h
    simp [Dvd.dvd]
    --simp [HSMul.hSMul, SMul.smul] at h
    rcases h with ⟨c, eq⟩
    --use c
    sorry
  sorry

lemma modEq_iff_dvd_int (p a b : ℤ) : a ≡ b [ZMOD p] ↔ p ∣ (b - a) := by
  exact Int.modEq_iff_dvd
