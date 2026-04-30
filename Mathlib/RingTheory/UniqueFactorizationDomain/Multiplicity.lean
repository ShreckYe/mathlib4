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

/-- In a UFM, if `a ^ m = b ^ n` and `m.Coprime n`, then there exists `c` such that
`a` is associated to `c ^ n` and `b` is associated to `c ^ m`. -/
theorem exists_associated_pow_of_coprime_of_pow_eq_pow [NormalizationMonoid R] [DecidableEq R]
    {a b : R} {m n : ℕ}
    (hmn : m.Coprime n) (h : a ^ m = b ^ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c : R, Associated a (c ^ n) ∧ Associated b (c ^ m) := by
  -- From a^m = b^n, normalizedFactors satisfy m • nf(a) = n • nf(b)
  have hnf : m • normalizedFactors a = n • normalizedFactors b := by
    have heq : Associated (a ^ m) (b ^ n) := by rw [h]
    have := (associated_iff_normalizedFactors_eq_normalizedFactors
      (pow_ne_zero m ha) (pow_ne_zero n hb)).mp heq
    rwa [normalizedFactors_pow, normalizedFactors_pow] at this
  -- For each prime p, n ∣ count(p, nf(a)) by coprimality
  have hdvd_n : ∀ p, n ∣ (normalizedFactors a).count p := by
    intro p
    have hcount : m * (normalizedFactors a).count p = n * (normalizedFactors b).count p := by
      have := congr_arg (Multiset.count p) hnf
      simp [Multiset.count_nsmul] at this; exact this
    exact hmn.symm.dvd_of_dvd_mul_left ⟨_, hcount⟩
  -- Handle trivial case n = 0
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.Coprime, Nat.gcd_zero_right] at hmn
    subst hmn; simp at h; exact ⟨b, by simp [h], by simp⟩
  -- Handle trivial case m = 0
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Nat.Coprime, Nat.gcd_zero_left] at hmn
    subst hmn; simp at h; exact ⟨a, by simp, by simp [h]⟩
  -- Construct S with n • S = normalizedFactors a
  set S : Multiset R := (normalizedFactors a).dedup.bind
    (fun p => Multiset.replicate ((normalizedFactors a).count p / n) p)
  have hS : n • S = normalizedFactors a := by
    ext p
    simp only [S, Multiset.count_nsmul, Multiset.count_bind, Multiset.count_replicate]
    -- The map/sum over dedup is a Finset sum
    change n * (∑ x ∈ (normalizedFactors a).toFinset,
      (if x = p then (normalizedFactors a).count x / n else 0)) = _
    rw [Finset.sum_eq_single p (fun q _ hqp => by simp [hqp])
      (fun hp => by simp [Multiset.mem_toFinset.not.mp hp])]
    simp [Nat.mul_div_cancel' (hdvd_n p)]
  -- S consists of normalized irreducibles
  have hS_irred : ∀ p ∈ S, Irreducible p := by
    intro p hp
    have : p ∈ normalizedFactors a := by rw [← hS]; exact Multiset.mem_nsmul.mpr ⟨hn, hp⟩
    exact irreducible_of_normalized_factor p this
  have hS_norm : ∀ p ∈ S, normalize p = p := by
    intro p hp
    have : p ∈ normalizedFactors a := by rw [← hS]; exact Multiset.mem_nsmul.mpr ⟨hn, hp⟩
    exact normalize_normalized_factor p this
  -- S.prod ≠ 0
  have hS_prod_ne : S.prod ≠ 0 := by
    intro h0
    have : (n • S).prod = S.prod ^ n := Multiset.prod_nsmul S n
    rw [hS, h0, zero_pow hn] at this
    exact ((prod_normalizedFactors ha).ne_zero_iff.mpr ha) this
  -- normalizedFactors(S.prod) = S
  have hnf_S : normalizedFactors S.prod = S := by
    have h1 := normalizedFactors_prod_eq S hS_irred
    rwa [show Multiset.map normalize S = S from
      (Multiset.map_congr rfl hS_norm).trans (Multiset.map_id S)] at h1
  use S.prod
  constructor
  · rw [associated_iff_normalizedFactors_eq_normalizedFactors ha (pow_ne_zero n hS_prod_ne)]
    rw [normalizedFactors_pow, hnf_S, hS]
  · rw [associated_iff_normalizedFactors_eq_normalizedFactors hb (pow_ne_zero m hS_prod_ne)]
    rw [normalizedFactors_pow, hnf_S]
    have key : n • (m • S) = n • normalizedFactors b := by
      calc n • (m • S)
          _ = (m * n) • S := (mul_nsmul S m n).symm
          _ = (n * m) • S := by rw [Nat.mul_comm]
          _ = m • (n • S) := mul_nsmul S n m
          _ = m • normalizedFactors a := by rw [hS]
          _ = n • normalizedFactors b := hnf
    exact ((nsmul_right_inj hn).mp key).symm

end UniqueFactorizationMonoid
