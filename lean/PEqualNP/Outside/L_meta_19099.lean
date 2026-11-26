import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19099 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 1 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4095 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.not, [3]⟩], 8⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  obtain rfl := List.mem_singleton.mp hg
  exact ⟨by simp, by decide⟩
