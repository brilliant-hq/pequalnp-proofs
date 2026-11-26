import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19294 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235582 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 11]⟩, ⟨.not, [0]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩, ⟨.not, [16]⟩], 17⟩
  exact ⟨C, by simp [C, FanInTwo], by decide +kernel, by decide +kernel⟩
