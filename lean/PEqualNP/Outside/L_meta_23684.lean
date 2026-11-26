import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit23684 : Circuit := ⟨[
  ⟨.or, [4, 5]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [0, 10]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.or, [2, 11]⟩,
  ⟨.or, [9, 14]⟩,
  ⟨.and, [13, 14]⟩,
  ⟨.or, [3, 15]⟩,
  ⟨.and, [12, 17]⟩,
  ⟨.or, [16, 18]⟩], 19⟩

theorem PEqualNP.Outside.L_meta_23684 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816696 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  refine ⟨circuit23684, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit23684, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

