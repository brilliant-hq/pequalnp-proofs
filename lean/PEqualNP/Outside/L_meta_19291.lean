import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19291 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7597924 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [0, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [18, 17]⟩], 19⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
