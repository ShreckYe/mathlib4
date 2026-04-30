import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Finsupp.Multiset

/-!
# Generalized Prime Power and Coprime Exponent Theorems
-/

open scoped ENat

/-! ## Group 1: Prime Exponents in CancelCommMonoidWithZero -/

section CancelCommMonoidWithZero

variable {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]

/-- If `p` is prime and `p ^ m = a ^ n`, then `n ∣ m`. -/
theorem Prime.dvd_of_pow_eq_pow {p a : α} {m n : ℕ} (hp : Prime p) (h : p ^ m = a ^ n) :
    n ∣ m := by
  have key : (m : ℕ∞) = n * emultiplicity p a := by
    have := congr_arg (emultiplicity p) h
    rwa [emultiplicity_pow_self_of_prime hp, emultiplicity_pow hp] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp at key; omega
  · have hfin : emultiplicity p a ≠ ⊤ := by
      intro htop
      simp [htop, ENat.mul_top (show (n : ℕ∞) ≠ 0 from Nat.cast_ne_zero.mpr hn)] at key
    lift emultiplicity p a to ℕ using hfin with k hk
    have key' : m = n * k := by exact_mod_cast key
    exact ⟨k, key'⟩

/-- If `p` is prime, `p ^ m = a ^ n`, and `n ≠ 0`, then `a` is associated to a power of `p`. -/
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
    exact ⟨0, by rw [pow_zero]; exact associated_one_iff_isUnit.mpr (IsUnit.of_pow_eq_one h.symm hn)⟩
  · have hpa : p ∣ a := hp.dvd_of_dvd_pow (h ▸ dvd_pow_self p hm)
    obtain ⟨b, rfl⟩ := hpa
    rw [mul_pow] at h
    have hnm : n ≤ m :=
      (pow_dvd_pow_iff hp.ne_zero hp.not_unit).mp ⟨b ^ n, h⟩
    have hcancel : p ^ (m - n) = b ^ n := by
      apply mul_left_cancel₀ (pow_ne_zero n hp.ne_zero)
      rw [← pow_add, Nat.add_sub_cancel' hnm, h]
    have hlt : m - n < m := Nat.sub_lt (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
    obtain ⟨k, hk⟩ := ih (m - n) hlt b hcancel
    exact ⟨k + 1, by rw [pow_succ']; exact Associated.mul_left p hk⟩

end CancelCommMonoidWithZero

/-! ## Group 2: Coprime Exponent Roots in UniqueFactorizationMonoid -/

section UFM

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

open UniqueFactorizationMonoid

/-- In a UFM, if `a ^ m = b ^ n` and `m.Coprime n`, then there exists `c` such that
`a` is associated to `c ^ n` and `b` is associated to `c ^ m`. -/
theorem exists_associated_pow_of_coprime_of_pow_eq_pow [NormalizationMonoid α] [DecidableEq α]
    {a b : α} {m n : ℕ}
    (hmn : m.Coprime n) (h : a ^ m = b ^ n) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c : α, Associated a (c ^ n) ∧ Associated b (c ^ m) := by
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
  -- Construct S with n • S = normalizedFactors a using Finsupp
  -- toFinsupp converts Multiset to Finsupp, we divide pointwise by n
  set fa := (normalizedFactors a).toFinsupp
  -- Divide each coefficient by n
  set fc : α →₀ ℕ := fa.mapRange (· / n) (by simp)
  -- Convert back to multiset
  set S := fc.toMultiset
  have hS : n • S = normalizedFactors a := by
    ext p
    simp [Multiset.count_nsmul, S, fc, fa, Finsupp.count_toMultiset]
    exact Nat.mul_div_cancel' (hdvd_n p)
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
    -- (normalizedFactors a).prod = 0, but it's associated to a ≠ 0
    exact ((prod_normalizedFactors ha).ne_zero_iff.mpr ha) this
  -- normalizedFactors(S.prod) = S
  have hnf_S : normalizedFactors S.prod = S := by
    have h1 := normalizedFactors_prod_eq S hS_irred
    -- h1 : normalizedFactors S.prod = Multiset.map normalize S
    -- Since normalize p = p for all p ∈ S, map normalize S = S
    rwa [show Multiset.map normalize S = S from
      (Multiset.map_congr rfl hS_norm).trans (Multiset.map_id S)] at h1
  use S.prod
  constructor
  · -- Associated a (S.prod ^ n)
    rw [associated_iff_normalizedFactors_eq_normalizedFactors ha (pow_ne_zero n hS_prod_ne)]
    rw [normalizedFactors_pow, hnf_S, hS]
  · -- Associated b (S.prod ^ m)
    rw [associated_iff_normalizedFactors_eq_normalizedFactors hb (pow_ne_zero m hS_prod_ne)]
    rw [normalizedFactors_pow, hnf_S]
    -- Need: m • S = normalizedFactors b
    have key : n • (m • S) = n • normalizedFactors b := by
      -- n • (m • S) = (m * n) • S by mul_nsmul
      -- (m * n) • S = (n * m) • S = n • (m • S) via commutativity
      -- But also (n * m) • S = m • (n • S) = m • nf(a) = n • nf(b)
      calc n • (m • S)
          _ = (m * n) • S := (mul_nsmul S m n).symm
          _ = (n * m) • S := by rw [Nat.mul_comm]
          _ = m • (n • S) := mul_nsmul S n m
          _ = m • normalizedFactors a := by rw [hS]
          _ = n • normalizedFactors b := hnf
    exact ((nsmul_right_inj hn).mp key).symm

end UFM
