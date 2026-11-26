import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19229 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6079 : ℕ).testBit (4 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [4, 12]⟩], 13⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
