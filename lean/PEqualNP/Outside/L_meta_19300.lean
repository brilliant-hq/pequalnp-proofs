import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19300 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16240236 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [10]⟩, ⟨.and, [12, 13]⟩, ⟨.not, [9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [18, 17]⟩], 19⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
