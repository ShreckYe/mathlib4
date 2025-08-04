/-
Copyright (c) 2025 GitHub Copilot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Prime elements and GCD/LCM

This file contains theorems relating prime elements to GCD and LCM operations
in commutative monoids with zero.

## Main theorems

- `Prime.dvd_lcm`: A prime divides the LCM of two elements iff it divides one of them
- `Prime.not_dvd_lcm`: A prime doesn't divide the LCM iff it doesn't divide either element
-/

variable {M : Type*} [CancelCommMonoidWithZero M] [GCDMonoid M]

theorem Prime.dvd_lcm {p a b : M} (hp : Prime p) : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    -- For a prime in a GCDMonoid, if it divides the lcm, it must divide one of the operands
    -- Use the fundamental identity: gcd(a,b) * lcm(a,b) is associated with a * b
    -- Since p divides lcm(a,b), and gcd(a,b) divides gcd(a,b) * lcm(a,b),
    -- p divides gcd(a,b) * lcm(a,b), so by association, p divides a * b
    have assoc : Associated (gcd a b * lcm a b) (a * b) := gcd_mul_lcm a b
    have hdvd : p ∣ gcd a b * lcm a b := dvd_mul_of_dvd_right h (gcd a b)
    -- Use that gcd(a,b) * lcm(a,b) is associated with a * b to get p ∣ a * b
    obtain ⟨u, hu⟩ := assoc
    have : p ∣ a * b := by
      rw [← hu]
      exact dvd_mul_of_dvd_left hdvd u
    exact hp.dvd_or_dvd this
  · rintro (h | h)
    · exact dvd_trans h (dvd_lcm_left a b)
    · exact dvd_trans h (dvd_lcm_right a b)

theorem Prime.not_dvd_lcm {p a b : M} (hp : Prime p) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    ¬ p ∣ lcm a b :=
  hp.dvd_lcm.not.mpr <| not_or.mpr ⟨ha, hb⟩

namespace Prime

variable {M : Type*} [CancelCommMonoidWithZero M] [GCDMonoid M]

theorem Prime.dvd_lcm {p a b : M} (hp : Prime p) : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    -- For a prime in a GCDMonoid, if it divides the lcm, it must divide one of the operands
    -- Use the fundamental identity: gcd(a,b) * lcm(a,b) is associated with a * b
    rw [← hp.dvd_mul]
    have assoc : Associated (gcd a b * lcm a b) (a * b) := gcd_mul_lcm a b
    have hdvd : p ∣ gcd a b * lcm a b := dvd_mul_of_dvd_right h (gcd a b)
    exact hp.dvd_mul.mp (assoc.dvd.mp hdvd)
  · rintro (h | h)
    · exact dvd_trans h (dvd_lcm_left a b)
    · exact dvd_trans h (dvd_lcm_right a b)

theorem Prime.not_dvd_lcm {p a b : M} (hp : Prime p) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    ¬ p ∣ lcm a b :=
  hp.dvd_lcm.not.mpr <| not_or.mpr ⟨ha, hb⟩
