import Mathlib

example  {s f : Finset ℝ} {f : ℝ → ℝ} : (s.image f).card < s.card -> ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ f p = f q := by
  intros card_lt
  have : Set.MapsTo f s (s.image f) := by
    sorry
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to card_lt this

example {s : Finset ℝ} {f : ℝ → ℝ} : Set.MapsTo f s (s.image f) := by
  have := Set.mapsTo_image f s
  simp only [Finset.coe_image]
  exact this
