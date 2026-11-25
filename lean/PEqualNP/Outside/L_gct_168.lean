import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_gct_168 : ∀ (K : Type) [Field K] (O : ValuationSubring K) (a b c : K), a * b * c = 1 → (a ∈ O.nonunits ∨ b ∈ O.nonunits ∨ c ∈ O.nonunits) → (a ∉ O ∨ b ∉ O ∨ c ∉ O) := by
  intro K _ O a b c h hn
  by_contra hc
  push_neg at hc
  obtain ⟨ha, hb, hc⟩ := hc
  have key : ∀ x y z : K, x * y * z = 1 → x ∈ O → y ∈ O → z ∈ O → x ∉ O.nonunits := by
    intro x y z hxyz hx hy hz hxn
    rw [ValuationSubring.mem_nonunits_iff] at hxn
    have h1 : O.valuation (x * y * z) = 1 := by rw [hxyz, map_one]
    rw [map_mul, map_mul] at h1
    have hy1 := (O.valuation_le_one_iff y).mpr hy
    have hz1 := (O.valuation_le_one_iff z).mpr hz
    have : O.valuation x * O.valuation y * O.valuation z < 1 := by
      calc O.valuation x * O.valuation y * O.valuation z ≤ O.valuation x * 1 * 1 := by gcongr
        _ = O.valuation x := by simp
        _ < 1 := hxn
    exact absurd h1 (ne_of_lt this)
  rcases hn with h1 | h1 | h1
  · exact key a b c h ha hb hc h1
  · exact key b a c (by rw [← h]; ring) hb ha hc h1
  · exact key c a b (by rw [← h]; ring) hc ha hb h1
