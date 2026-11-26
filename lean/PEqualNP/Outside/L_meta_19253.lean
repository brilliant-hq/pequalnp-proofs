import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19253 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577402 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.not, [1]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [0, 11]⟩, ⟨.not, [15]⟩, ⟨.or, [6, 16]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [12, 18]⟩], 19⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
