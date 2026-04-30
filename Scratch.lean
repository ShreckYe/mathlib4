import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

open scoped Classical

local infixl:50 " ~ᵤ " => Associated
open UniqueFactorizationMonoid

namespace Finsupp

theorem exists_eq_nsmul_of_coprime_of_nsmul_eq_nsmul {α : Type*} [DecidableEq α]
    {f g : α →₀ ℕ} {m n : ℕ} (hmn : m.Coprime n) (h : m • f = n • g) :
    ∃ c : α →₀ ℕ, f = n • c ∧ g = m • c := by
  obtain rfl | hn := eq_or_ne n 0
  · have hm : m = 1 := by simpa [Nat.coprime_zero_right] using hmn
    subst hm
    exact ⟨g, by simpa using h, by simp⟩
  obtain rfl | hm := eq_or_ne m 0
  · have hn1 : n = 1 := by simpa [Nat.coprime_zero_left] using hmn
    subst hn1
    exact ⟨f, by simp, by simpa using h.symm⟩
  let c := f.mapRange (· / n) (Nat.zero_div n)
  refine ⟨c, ?_, ?_⟩
  · ext a
    have hmul : m * f a = n * g a := by
      simpa [nsmul_eq_mul] using congr(($h) a)
    have hdiv : n ∣ f a := by
      refine hmn.symm.dvd_of_dvd_mul_left ?_
      exact ⟨g a, hmul⟩
    simp [c, Nat.mul_div_cancel' hdiv]
  · ext a
    have hmul : m * f a = n * g a := by
      simpa [nsmul_eq_mul] using congr(($h) a)
    have hdiv : n ∣ f a := by
      refine hmn.symm.dvd_of_dvd_mul_left ?_
      exact ⟨g a, hmul⟩
    have hf : f a = n * c a := by
      simp [c, Nat.mul_div_cancel' hdiv]
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
    calc
      n * g a = m * f a := hmul.symm
      _ = m * (n * c a) := by rw [hf]
      _ = n * (m * c a) := by ac_rfl

end Finsupp

namespace Prime

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

theorem exponent_eq_exponent_mul_multiplicity_of_pow_eq_pow {p a : M} {m n : ℕ}
    (hp : Prime p) (h : p ^ m = a ^ n) :
    m = n * multiplicity p a := by
  obtain rfl | hn := eq_or_ne n 0
  · have hm : p ^ m = p ^ 0 := by simpa using h
    have hm0 : m = 0 := (pow_inj_of_not_isUnit hp.not_unit hp.ne_zero).mp hm
    simp [hm0]
  have hemul : (m : ℕ∞) = n * emultiplicity p a := by
    calc
      (m : ℕ∞) = emultiplicity p (p ^ m) := by
        simpa using (emultiplicity_pow_self_of_prime hp m).symm
      _ = emultiplicity p (a ^ n) := by rw [h]
      _ = n * emultiplicity p a := by
        simpa [Nat.mul_comm] using (emultiplicity_pow hp (a := a) (k := n))
  have hfin : FiniteMultiplicity p a := by
    refine finiteMultiplicity_iff_emultiplicity_ne_top.2 ?_
    intro htop
    have : (m : ℕ∞) = ⊤ := by simpa [htop, hn] using hemul
    simpa using this
  have hemul' : emultiplicity p a = multiplicity p a := hfin.emultiplicity_eq_multiplicity
  exact ENat.coe_inj.mp <| by simpa [hemul', Nat.mul_comm] using hemul

theorem exponent_dvd_of_pow_eq_pow {p a : M} {m n : ℕ} (hp : Prime p) (h : p ^ m = a ^ n) :
    n ∣ m :=
  ⟨multiplicity p a, exponent_eq_exponent_mul_multiplicity_of_pow_eq_pow hp h⟩

theorem exists_associated_pow_of_pow_eq_pow {p a : M} {m n : ℕ}
    (hp : Prime p) (hn : n ≠ 0) (h : p ^ m = a ^ n) : ∃ k, a ~ᵤ p ^ k := by
  let k := multiplicity p a
  refine ⟨k, ?_⟩
  obtain ⟨b, hb_eq⟩ := pow_multiplicity_dvd p a
  have hm : m = n * k := by
    simpa [k] using exponent_eq_exponent_mul_multiplicity_of_pow_eq_pow hp h
  have hpow : p ^ (n * k) = p ^ (n * k) * b ^ n := by
    calc
      p ^ (n * k) = p ^ m := by simp [hm]
      _ = a ^ n := h
      _ = (p ^ k * b) ^ n := by rw [hb_eq]
      _ = (p ^ k) ^ n * b ^ n := by rw [mul_pow]
      _ = p ^ (k * n) * b ^ n := by rw [pow_mul]
      _ = p ^ (n * k) * b ^ n := by rw [Nat.mul_comm]
  have hb : b ^ n = 1 := by
    apply (mul_left_cancel₀ (a := p ^ (n * k)) (b := b ^ n) (c := 1) (pow_ne_zero _ hp.ne_zero))
    simpa using hpow.symm
  exact hb_eq ▸ associated_mul_unit_left (p ^ k) b (IsUnit.of_pow_eq_one hb hn)

theorem exists_eq_pow_of_pow_eq_pow [Subsingleton Mˣ] {p a : M} {m n : ℕ}
    (hp : Prime p) (hn : n ≠ 0) (h : p ^ m = a ^ n) : ∃ k, a = p ^ k := by
  obtain ⟨k, hk⟩ := exists_associated_pow_of_pow_eq_pow hp hn h
  exact ⟨k, associated_iff_eq.mp hk⟩

end Prime

section UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R]
  [NormalizationMonoid R] [UniqueFactorizationMonoid R]

theorem exists_associated_pow_of_exponent_coprime_of_pow_eq_pow {a b : R} {m n : ℕ}
    (hmn : m.Coprime n) (h : a ^ m = b ^ n) : ∃ c, a ~ᵤ c ^ n ∧ b ~ᵤ c ^ m := by
  obtain rfl | hm := eq_or_ne m 0
  · have hn : n = 1 := by simpa [Nat.coprime_zero_left] using hmn
    subst hn
    have hb1 : b = 1 := by simpa using h.symm
    refine ⟨a, ?_, ?_⟩
    · simpa using (Associated.refl a : a ~ᵤ a)
    · simpa [hb1] using (Associated.refl (1 : R) : (1 : R) ~ᵤ 1)
  obtain rfl | hn := eq_or_ne n 0
  · have hm1 : m = 1 := by simpa [Nat.coprime_zero_right] using hmn
    subst hm1
    have ha1 : a = 1 := by simpa using h
    refine ⟨b, ?_, ?_⟩
    · simpa [ha1] using (Associated.refl (1 : R) : (1 : R) ~ᵤ 1)
    · simpa using (Associated.refl b : b ~ᵤ b)
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by
      apply (pow_eq_zero_iff hn).1
      simpa [ha0, hm] using h.symm
    refine ⟨0, ?_, ?_⟩ <;> simp [ha0, hb0, hm, hn]
  by_cases hb0 : b = 0
  · have ha0' : a = 0 := by
      apply (pow_eq_zero_iff hm).1
      simpa [hb0, hn] using h
    exact (ha0 ha0').elim
  haveI : Nontrivial R := nontrivial_of_ne 0 a (Ne.symm ha0)
  have hnf : m • normalizedFactors a = n • normalizedFactors b := by
    simpa [UniqueFactorizationMonoid.normalizedFactors_pow] using congrArg normalizedFactors h
  let f : R →₀ ℕ := Multiset.toFinsupp (normalizedFactors a)
  let g : R →₀ ℕ := Multiset.toFinsupp (normalizedFactors b)
  have hfg : m • f = n • g := by
    simpa [f, g] using congrArg Multiset.toFinsupp hnf
  obtain ⟨u, hf, hg⟩ := Finsupp.exists_eq_nsmul_of_coprime_of_nsmul_eq_nsmul hmn hfg
  let factors : Multiset R := Finsupp.toMultiset u
  let c : R := factors.prod
  have hfa : normalizedFactors a = n • factors := by
    simpa [f, factors] using congrArg Finsupp.toMultiset hf
  have hgb : normalizedFactors b = m • factors := by
    simpa [g, factors] using congrArg Finsupp.toMultiset hg
  have hirr : ∀ q ∈ factors, Irreducible q := by
    intro q hq
    apply irreducible_of_normalized_factor q
    rw [hfa]
    exact (Multiset.mem_nsmul_of_ne_zero hn).2 hq
  have hnorm : ∀ q ∈ factors, normalize q = q := by
    intro q hq
    apply normalize_normalized_factor
    rw [hfa]
    exact (Multiset.mem_nsmul_of_ne_zero hn).2 hq
  have hc0 : c ≠ 0 := by
    apply factors.prod_ne_zero
    intro h0
    exact (hirr 0 h0).ne_zero rfl
  have hcf : normalizedFactors c = factors := by
    calc
      normalizedFactors c = factors.map normalize := by
        simpa [c] using UniqueFactorizationMonoid.normalizedFactors_prod_eq factors hirr
      _ = factors := by
        simpa using Multiset.map_congr rfl hnorm
  refine ⟨c, ?_, ?_⟩
  · refine (associated_iff_normalizedFactors_eq_normalizedFactors ha0 (pow_ne_zero n hc0)).2 ?_
    rw [UniqueFactorizationMonoid.normalizedFactors_pow, hcf, hfa]
  · refine (associated_iff_normalizedFactors_eq_normalizedFactors hb0 (pow_ne_zero m hc0)).2 ?_
    rw [UniqueFactorizationMonoid.normalizedFactors_pow, hcf, hgb]

theorem exists_eq_pow_of_exponent_coprime_of_pow_eq_pow [Subsingleton Rˣ]
    {a b : R} {m n : ℕ} (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  obtain ⟨c, ha, hb⟩ := exists_associated_pow_of_exponent_coprime_of_pow_eq_pow hmn h
  exact ⟨c, associated_iff_eq.mp ha, associated_iff_eq.mp hb⟩

end UniqueFactorizationMonoid
