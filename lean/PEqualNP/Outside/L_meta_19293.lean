import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19293 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16227576 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [0, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.and, [12, 8]⟩, ⟨.not, [0]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [15, 7]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [18, 17]⟩], 19⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
