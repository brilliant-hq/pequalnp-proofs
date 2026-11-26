import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19191 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (318 : ℕ).testBit (4 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
