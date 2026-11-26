import PEqualNP.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace PEqualNP.Outside.L_gct_168_aux

lemma not_mem_nonunits_of_mul_eq_one {K : Type} [Field K] (O : ValuationSubring K)
    {x y : K} (hxy : x * y = 1) (hy : y ∈ O) : x ∉ O.nonunits := by
  rw [O.mem_nonunits_iff_or]
  push_neg
  refine ⟨?_, ?_⟩
  · intro hx0
    rw [hx0, zero_mul] at hxy
    exact zero_ne_one hxy
  · have hinv : x⁻¹ = y := inv_eq_of_mul_eq_one_right hxy
    rwa [hinv]

end PEqualNP.Outside.L_gct_168_aux

theorem PEqualNP.Outside.L_gct_168 : ∀ (K : Type) [Field K] (O : ValuationSubring K) (a b c : K), a * b * c = 1 → (a ∈ O.nonunits ∨ b ∈ O.nonunits ∨ c ∈ O.nonunits) → (a ∉ O ∨ b ∉ O ∨ c ∉ O) := by
  intro K _ O a b c habc hnu
  by_contra h
  push_neg at h
  rcases h with ⟨ha, hb, hc⟩
  rcases hnu with hna | hnb | hnc
  · exact PEqualNP.Outside.L_gct_168_aux.not_mem_nonunits_of_mul_eq_one O
      (by calc a * (b * c) = a * b * c := by ring
        _ = 1 := habc) (mul_mem hb hc) hna
  · exact PEqualNP.Outside.L_gct_168_aux.not_mem_nonunits_of_mul_eq_one O
      (by calc b * (a * c) = a * b * c := by ring
        _ = 1 := habc) (mul_mem ha hc) hnb
  · exact PEqualNP.Outside.L_gct_168_aux.not_mem_nonunits_of_mul_eq_one O
      (by calc c * (a * b) = a * b * c := by ring
        _ = 1 := habc) (mul_mem ha hb) hnc
