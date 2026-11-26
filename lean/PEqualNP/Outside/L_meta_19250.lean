import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19250 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577150 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [1, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩, ⟨.not, [1]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [18, 17]⟩], 19⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
