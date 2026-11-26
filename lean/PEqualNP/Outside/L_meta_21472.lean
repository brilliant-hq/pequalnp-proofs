import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21472_aux


def witness : PEqualNP.CircuitLowerBounds.Circuit where
  gates := [
      ⟨.or, [2, 3]⟩,
      ⟨.or, [5, 4]⟩,
      ⟨.and, [0, 6]⟩,
      ⟨.or, [2, 3]⟩,
      ⟨.or, [8, 4]⟩,
      ⟨.and, [1, 9]⟩,
      ⟨.and, [2, 3]⟩,
      ⟨.or, [7, 10]⟩,
      ⟨.or, [12, 11]⟩]
  output := 13

end PEqualNP.Outside.L_meta_21472_aux

theorem PEqualNP.Outside.L_meta_21472 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9116 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21472_aux.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_21472_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Set.mem_insert_iff]
