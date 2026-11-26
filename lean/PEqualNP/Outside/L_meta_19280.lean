import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19280 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6015 : ℕ).testBit (4 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.or, [3, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [0, 10]⟩], 11⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
