import Mathlib

/-!
# Generalized Prime Power and Coprime Exponent Theorems

This file contains generalizations of theorems from PR #28557:
- Group 1: Prime exponent theorems (`p ^ m = a ^ n`) generalized to `CancelCommMonoidWithZero`
- Group 2: Coprime exponent root theorems (`a ^ m = b ^ n`) generalized to
  `UniqueFactorizationMonoid`
-/

open scoped ENat

/-! ## Group 1: Prime Exponents in CancelCommMonoidWithZero -/

section CancelCommMonoidWithZero

variable {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]

/-- If `p` is prime and `p ^ m = a ^ n`, then `n ∣ m`.

This follows from the `p`-adic valuation: `m = emultiplicity p (p ^ m) = emultiplicity p (a ^ n) =
n * emultiplicity p a`. -/
theorem Prime.dvd_of_pow_eq_pow {p a : α} {m n : ℕ} (hp : Prime p) (h : p ^ m = a ^ n) :
    n ∣ m := by
  have key : (m : ℕ∞) = n * emultiplicity p a := by
    have := congr_arg (emultiplicity p) h
    rwa [emultiplicity_pow_self_of_prime hp, emultiplicity_pow hp] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp at key; exact key ▸ dvd_refl 0
  · have hfin : emultiplicity p a ≠ ⊤ := by
      intro htop
      simp [htop, ENat.mul_top (show (n : ℕ∞) ≠ 0 from Nat.cast_ne_zero.mpr hn)] at key
    lift emultiplicity p a to ℕ using hfin with k hk
    rw [hk, ← ENat.coe_mul, ENat.coe_inj] at key
    exact ⟨k, key⟩

/-- If `p` is prime, `p ^ m = a ^ n`, and `n ≠ 0`, then `a` is associated to a power of `p`.

This is proved by strong induction on `m`: the prime `p` divides `a`, say `a = p * b`,
leading to `p ^ (m - n) = b ^ n` after cancellation, and the result follows by induction. -/
theorem Prime.exists_associated_pow_of_pow_eq_pow {p a : α} {m n : ℕ}
    (hp : Prime p) (hn : n ≠ 0) (h : p ^ m = a ^ n) :
    ∃ k, Associated a (p ^ k) := by
  suffices ∀ m (a : α), p ^ m = a ^ n → ∃ k, Associated a (p ^ k) from this m a h
  intro m
  induction m using Nat.strongRecOn with | ind m ih =>
  intro a h
  by_cases hm : m = 0
  · subst hm
    rw [pow_zero] at h
    exact ⟨0, (associated_one_iff_isUnit.mpr (IsUnit.of_pow_eq_one h.symm hn)).symm⟩
  · -- m > 0, so p ∣ a^n, hence p ∣ a
    have hpa : p ∣ a := hp.dvd_of_dvd_pow (h ▸ dvd_pow_self p hm)
    obtain ⟨b, rfl⟩ := hpa
    -- p^m = (p * b)^n = p^n * b^n
    rw [mul_pow] at h
    -- n ≤ m since p^n ∣ p^m
    have hnm : n ≤ m :=
      (pow_dvd_pow_iff hp.ne_zero hp.not_unit).mp ⟨b ^ n, h.symm⟩
    -- Cancel p^n: p^(m-n) = b^n
    have hcancel : p ^ (m - n) = b ^ n := by
      have hpn : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero
      apply mul_left_cancel₀ hpn
      rw [← pow_add, Nat.add_sub_cancel' hnm, h]
    -- Induction: m - n < m since n ≥ 1
    have hlt : m - n < m := Nat.sub_lt (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
    obtain ⟨k, hk⟩ := ih (m - n) hlt b hcancel
    exact ⟨k + 1, by rw [pow_succ']; exact Associated.mul_left p hk⟩

end CancelCommMonoidWithZero

/-! ## Group 2: Coprime Exponent Roots in UniqueFactorizationMonoid -/

section UFM

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/-- In a UFM, if `a ^ m = b ^ n` and `m.Coprime n`, then there exists `c` such that
`a` is associated to `c ^ n` and `b` is associated to `c ^ m`.

This generalizes the `ℕ`-specific theorem `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow`. -/
theorem exists_associated_pow_of_coprime_of_pow_eq_pow {a b : α} {m n : ℕ}
    (hmn : m.Coprime n) (h : a ^ m = b ^ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c : α, Associated a (c ^ n) ∧ Associated b (c ^ m) := by
  -- For every prime p, from m * v_p(a) = n * v_p(b) and coprimality,
  -- we get n ∣ v_p(a) and m ∣ v_p(b).
  -- The key insight is to use the existing `exists_associated_pow_of_mul_eq_pow` from GCDMonoid.
  -- We use the fact that in a UFM with a GCDMonoid, coprimality gives us what we need.
  sorry

end UFM
