import PEqualNP.Defs.Represents

open PEqualNP.CircuitLowerBounds

private def circuit22516 : Circuit := ⟨[
  ⟨.or, [8, 9]⟩,
  ⟨.or, [0, 5]⟩,
  ⟨.or, [1, 7]⟩,
  ⟨.or, [6, 11]⟩,
  ⟨.or, [6, 12]⟩,
  ⟨.and, [3, 13]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.and, [11, 14]⟩,
  ⟨.or, [10, 17]⟩,
  ⟨.or, [15, 18]⟩,
  ⟨.or, [2, 19]⟩,
  ⟨.and, [16, 20]⟩,
  ⟨.or, [4, 21]⟩], 22⟩

theorem PEqualNP.Outside.L_meta_22516 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899773 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨circuit22516, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [circuit22516, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [List.length]
