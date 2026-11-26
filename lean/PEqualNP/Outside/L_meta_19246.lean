import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19246 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247934 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [14, 17]⟩], 18⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
