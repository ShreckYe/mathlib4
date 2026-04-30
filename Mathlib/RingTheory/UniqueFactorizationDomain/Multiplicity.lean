/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Unique factorization and multiplicity

## Main results

* `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`: The multiplicity of an
  irreducible factor of a nonzero element is exactly the number of times the normalized factor
  occurs in the `normalizedFactors`.
-/

public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

theorem WfDvdMonoid.max_power_factor' [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : ¬IsUnit x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a := by
  obtain ⟨a, ⟨n, rfl⟩, hm⟩ := wellFounded_dvdNotUnit.has_min
    {a | ∃ n, x ^ n * a = a₀} ⟨a₀, 0, by rw [pow_zero, one_mul]⟩
  refine ⟨n, a, ?_, rfl⟩; rintro ⟨d, rfl⟩
  exact hm d ⟨n + 1, by rw [pow_succ, mul_assoc]⟩
    ⟨(right_ne_zero_of_mul <| right_ne_zero_of_mul h), x, hx, mul_comm _ _⟩

theorem WfDvdMonoid.max_power_factor [CommMonoidWithZero α] [WfDvdMonoid α] {a₀ x : α}
    (h : a₀ ≠ 0) (hx : Irreducible x) : ∃ (n : ℕ) (a : α), ¬x ∣ a ∧ a₀ = x ^ n * a :=
  max_power_factor' h hx.not_isUnit

theorem FiniteMultiplicity.of_not_isUnit [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : ¬IsUnit a) (hb : b ≠ 0) : FiniteMultiplicity a b := by
  obtain ⟨n, c, ndvd, rfl⟩ := WfDvdMonoid.max_power_factor' hb ha
  exact ⟨n, by rwa [pow_succ, mul_dvd_mul_iff_left (left_ne_zero_of_mul hb)]⟩

theorem FiniteMultiplicity.of_prime_left [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α]
    {a b : α} (ha : Prime a) (hb : b ≠ 0) : FiniteMultiplicity a b :=
  .of_not_isUnit ha.not_unit hb

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section multiplicity

variable [NormalizationMonoid R]

open Multiset

theorem le_emultiplicity_iff_replicate_le_normalizedFactors {a b : R} {n : ℕ} (ha : Irreducible a)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n (normalize a) ≤ normalizedFactors b := by
  rw [← pow_dvd_iff_le_emultiplicity]
  revert b
  induction n with
  | zero => simp
  | succ n ih => ?_
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne, pow_succ', mul_assoc, mul_eq_zero, not_or] at hb
    rw [pow_succ', mul_assoc, normalizedFactors_mul hb.1 hb.2, replicate_succ,
      normalizedFactors_irreducible ha, singleton_add, cons_le_cons_iff, ← ih hb.2]
    apply Dvd.intro _ rfl
  · rw [Multiset.le_iff_exists_add]
    rintro ⟨u, hu⟩
    rw [← (prod_normalizedFactors hb).dvd_iff_dvd_right, hu, prod_add, prod_replicate]
    exact (Associated.pow_pow <| associated_normalize a).dvd.trans (Dvd.intro u.prod rfl)

variable [DecidableEq R]

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `multiplicity`, see `multiplicity_eq_count_normalizedFactors`.

See also `count_normalizedFactors_eq` which expands the definition of `multiplicity`
to produce a specification for `count (normalizedFactors _) _`..
-/
theorem emultiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    emultiplicity a b = (normalizedFactors b).count (normalize a) := by
  apply le_antisymm
  · apply Order.le_of_lt_add_one
    rw [← Nat.cast_one, ← Nat.cast_add, lt_iff_not_ge,
      le_emultiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]
    simp
  rw [le_emultiplicity_iff_replicate_le_normalizedFactors ha hb, ← le_count_iff_replicate_le]

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalizedFactors`.

For a version using `emultiplicity`, see `emultiplicity_eq_count_normalizedFactors`. -/
theorem multiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  have := emultiplicity_eq_count_normalizedFactors ha hb
  rwa [(finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity,
    ENat.coe_inj] at this

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalizedFactors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : ℕ}
    (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  by_cases hx0 : x = 0
  · simp [hx0] at hlt
  apply Nat.cast_injective (R := ℕ∞)
  convert (emultiplicity_eq_count_normalizedFactors hp hx0).symm
  · exact hnorm.symm
  exact (emultiplicity_eq_coe.mpr ⟨hle, hlt⟩).symm

/-- The number of times an irreducible factor `p` appears in `normalizedFactors x` is defined by
the number of times it divides `x`. This is a slightly more general version of
`UniqueFactorizationMonoid.count_normalizedFactors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalizedFactors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalizedFactors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p)
    {n : ℕ} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) :
    (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_notMem_normalizedFactors _)
    · rw [zero_pow (Nat.succ_ne_zero _)] at hle hlt
      exact absurd hle hlt
  · exact count_normalizedFactors_eq hp hnorm hle hlt

lemma associated_finprod_pow_count {x : R} (hx : x ≠ 0) :
    Associated (∏ᶠ p : R, p ^ (normalizedFactors x).count p) x := by
  rw [← Multiset.prod_map_eq_finprod, Multiset.map_id']
  exact prod_normalizedFactors hx

lemma finprod_pow_count_eq_of_subsingleton_units [Subsingleton Rˣ] {x : R} (hx : x ≠ 0) :
    ∏ᶠ p : R, p ^ (normalizedFactors x).count p = x :=
  associated_iff_eq.mp <| associated_finprod_pow_count hx

end multiplicity

lemma dvd_iff_emultiplicity_le {a b : R} (ha : a ≠ 0) :
    a ∣ b ↔ ∀ p : R, Prime p → emultiplicity p a ≤ emultiplicity p b := by
  classical
  refine ⟨fun h _ _ ↦ emultiplicity_le_emultiplicity_of_dvd_right h, fun h ↦ ?_⟩
  by_cases hb : b = 0
  · simp_all
  letI : NormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha hb, Multiset.le_iff_count]
  intro q
  by_cases hq : q ∈ normalizedFactors a
  · have hqprime : Prime q := prime_of_normalized_factor q hq
    have h1 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible ha
    have h2 := emultiplicity_eq_count_normalizedFactors hqprime.irreducible hb
    rw [normalize_normalized_factor q hq] at h1 h2
    simpa [h1, h2] using h q hqprime
  · simp [Multiset.count_eq_zero_of_notMem hq]

lemma pow_dvd_pow_iff_dvd {a b : R} {n : ℕ} (hn : n ≠ 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  by_cases ha : a = 0
  · simp [ha, hn]
  refine ⟨?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  rw [dvd_iff_emultiplicity_le (pow_ne_zero n ha), dvd_iff_emultiplicity_le ha]
  intro H p hp
  have := H p hp
  rwa [emultiplicity_pow hp, emultiplicity_pow hp,
    ENat.mul_le_mul_left_iff (by exact_mod_cast hn) (ENat.coe_ne_top _)] at this

end UniqueFactorizationMonoid

/-! ## Prime power equals general power -/

section PrimePowEqPow

variable {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {p a : α} {m n : ℕ}

/-- If `p` is prime and `p ^ m = a ^ n`, then `m = n * multiplicity p a`. -/
theorem Prime.multiplicity_prime_pow_eq_pow (hp : Prime p) (h : p ^ m = a ^ n) (ha : a ≠ 0) :
    m = n * multiplicity p a := by
  have hfin : FiniteMultiplicity p a := FiniteMultiplicity.of_prime_left hp ha
  have h1 : emultiplicity p (p ^ m) = m := emultiplicity_pow_self_of_prime hp m
  have h2 : emultiplicity p (a ^ n) = n * emultiplicity p a := emultiplicity_pow hp
  have heq : (m : ℕ∞) = n * emultiplicity p a := by
    rw [← h1, congr_arg (emultiplicity p) h, h2]
  rw [hfin.emultiplicity_eq_multiplicity] at heq
  exact_mod_cast heq

/-- If `p` is prime and `p ^ m = a ^ n`, then `n ∣ m`. -/
theorem Prime.dvd_of_prime_pow_eq_pow (hp : Prime p) (h : p ^ m = a ^ n) : n ∣ m := by
  by_cases hn : n = 0
  · subst hn
    simp only [pow_zero] at h
    by_cases hm : m = 0
    · simp [hm]
    · exact absurd (IsUnit.of_pow_eq_one h hm) hp.not_unit
  have ha : a ≠ 0 := by
    intro ha; rw [ha, zero_pow hn] at h
    have h1 : emultiplicity p (p ^ m) = ⊤ := by rw [h]; exact emultiplicity_zero p
    rw [emultiplicity_pow_self hp.ne_zero hp.not_unit] at h1
    exact absurd h1 (ENat.coe_ne_top m)
  exact ⟨multiplicity p a, hp.multiplicity_prime_pow_eq_pow h ha⟩

/-- If `p` is prime, `n ≠ 0`, `p ^ m = a ^ n`, and the monoid is torsion-free,
then `a = p ^ (m / n)`. -/
theorem Prime.eq_prime_pow_of_prime_pow_eq_pow (hp : Prime p) [IsMulTorsionFree α]
    (h : p ^ m = a ^ n) (hn : n ≠ 0) : a = p ^ (m / n) := by
  have hdvd := hp.dvd_of_prime_pow_eq_pow h
  conv_lhs at h => rw [show m = m / n * n from (Nat.div_mul_cancel hdvd).symm]
  rw [pow_mul] at h
  exact pow_left_injective hn h.symm

/-- If `p` is prime, `n ≠ 0`, and `p ^ m = a ^ n`, then `∃ k, a = p ^ k`. -/
theorem Prime.exists_eq_prime_pow_of_prime_pow_eq_pow (hp : Prime p) [IsMulTorsionFree α]
    (h : p ^ m = a ^ n) (hn : n ≠ 0) : ∃ k, a = p ^ k :=
  ⟨m / n, hp.eq_prime_pow_of_prime_pow_eq_pow h hn⟩

end PrimePowEqPow

/-! ## Coprime exponent roots in UFM -/

section CoprimeExpRoots

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a b : α} {m n : ℕ}

open UniqueFactorizationMonoid

/-- In a UFM, if `m.Coprime n` and `a ^ m = b ^ n` with `a, b ≠ 0`, then for every prime `q`,
`n ∣ multiplicity q a`. -/
theorem Nat.Coprime.dvd_multiplicity_of_pow_eq (hmn : Nat.Coprime m n) (h : a ^ m = b ^ n)
    (ha : a ≠ 0) (hb : b ≠ 0) {q : α} (hq : Prime q) :
    n ∣ multiplicity q a := by
  have hfina : FiniteMultiplicity q a := FiniteMultiplicity.of_prime_left hq ha
  have hfinb : FiniteMultiplicity q b := FiniteMultiplicity.of_prime_left hq hb
  have heq : m * multiplicity q a = n * multiplicity q b := by
    have h1 : (m * multiplicity q a : ℕ∞) = n * multiplicity q b := by
      calc (m * multiplicity q a : ℕ∞)
          = m * emultiplicity q a := by rw [hfina.emultiplicity_eq_multiplicity]
        _ = emultiplicity q (a ^ m) := (emultiplicity_pow hq).symm
        _ = emultiplicity q (b ^ n) := by rw [congr_arg (emultiplicity q) h]
        _ = n * emultiplicity q b := emultiplicity_pow hq
        _ = n * multiplicity q b := by rw [hfinb.emultiplicity_eq_multiplicity]
    exact_mod_cast h1
  exact hmn.symm.dvd_of_dvd_mul_left (Dvd.intro _ heq.symm)

/-- In a UFM with trivial units, if `m.Coprime n` and `a ^ m = b ^ n` (both nonzero),
then `∃ c, a = c ^ n ∧ b = c ^ m`. -/
theorem exists_eq_pow_of_coprime_pow_eq [NormalizationMonoid α] [Subsingleton αˣ]
    (hmn : Nat.Coprime m n) (h : a ^ m = b ^ n)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c : α, a = c ^ n ∧ b = c ^ m := by
  -- Handle edge cases
  by_cases hn : n = 0
  · have hm : m = 1 := by
      have := hmn; rwa [hn, Nat.Coprime, Nat.gcd_zero_right] at this
    subst hn; subst hm; simp only [pow_one, pow_zero] at h ⊢; exact ⟨b, h, rfl⟩
  by_cases hm : m = 0
  · have hn1 : n = 1 := by
      have := hmn; rwa [hm, Nat.Coprime, Nat.gcd_zero_left] at this
    subst hm; subst hn1; simp only [pow_zero, pow_one] at h ⊢; exact ⟨a, rfl, h.symm⟩
  classical
  -- From a^m = b^n, we get m • normalizedFactors a = n • normalizedFactors b
  have hfact : m • normalizedFactors a = n • normalizedFactors b := by
    have heq := congr_arg normalizedFactors h
    rwa [normalizedFactors_pow, normalizedFactors_pow] at heq
  -- Helper: count equality from hfact
  have hcount : ∀ p, m * (normalizedFactors a).count p = n * (normalizedFactors b).count p := by
    intro p
    have := congr_arg (Multiset.count p) hfact
    rwa [Multiset.count_nsmul, Multiset.count_nsmul] at this
  -- n divides all counts of normalizedFactors a
  have hdvd : ∀ p, n ∣ (normalizedFactors a).count p := fun p =>
    hmn.symm.dvd_of_dvd_mul_left (Dvd.intro _ (hcount p).symm)
  -- m divides all counts of normalizedFactors b
  have hdvd_b : ∀ p, m ∣ (normalizedFactors b).count p := fun p =>
    hmn.dvd_of_dvd_mul_left (Dvd.intro _ (hcount p))
  -- count_a / n = count_b / m
  have hcount_eq : ∀ p, (normalizedFactors a).count p / n =
      (normalizedFactors b).count p / m := by
    intro p
    obtain ⟨k, hk⟩ := hdvd p
    obtain ⟨j, hj⟩ := hdvd_b p
    rw [hk, hj, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)]
    have := hcount p
    rw [hk, hj] at this
    -- this : m * (n * k) = n * (m * j), want k = j
    have hmn_pos := Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
    apply Nat.eq_of_mul_eq_mul_left hmn_pos
    calc m * n * k = m * (n * k) := by rw [Nat.mul_assoc]
      _ = n * (m * j) := this
      _ = m * n * j := by rw [← Nat.mul_assoc, Nat.mul_comm n m]
  -- Construct c via finprod
  set c := ∏ᶠ p : α, p ^ ((normalizedFactors a).count p / n) with hc_def
  -- Finite support
  have hfin_supp : (Function.mulSupport fun p : α =>
      p ^ ((normalizedFactors a).count p / n)).Finite := by
    apply Set.Finite.subset (normalizedFactors a).toFinset.finite_toSet
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra h_nmem
    exact hp (by rw [Multiset.count_eq_zero.mpr h_nmem, Nat.zero_div, pow_zero])
  use c
  constructor
  · -- Show a = c ^ n
    have ha_eq := finprod_pow_count_eq_of_subsingleton_units ha
    have hcn : c ^ n = ∏ᶠ p : α, p ^ ((normalizedFactors a).count p / n * n) := by
      rw [hc_def, finprod_pow hfin_supp]
      congr 1; ext p; exact (pow_mul p _ n).symm
    simp_rw [Nat.div_mul_cancel (hdvd _)] at hcn
    exact hcn.symm ▸ ha_eq.symm
  · -- Show b = c ^ m
    have hb_eq := finprod_pow_count_eq_of_subsingleton_units hb
    have hcm : c ^ m = ∏ᶠ p : α, p ^ ((normalizedFactors b).count p / m * m) := by
      rw [hc_def, finprod_pow hfin_supp]
      congr 1; ext p; rw [hcount_eq p]; exact (pow_mul p _ m).symm
    simp_rw [Nat.div_mul_cancel (hdvd_b _)] at hcm
    exact hcm.symm ▸ hb_eq.symm

end CoprimeExpRoots
