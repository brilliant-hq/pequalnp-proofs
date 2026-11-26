import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23547_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [11, 12]⟩], 13⟩

theorem shape : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23547_aux

theorem PEqualNP.Outside.L_meta_23547 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33585 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23547_aux.circuit, PEqualNP.Outside.L_meta_23547_aux.shape,
    by decide, by decide +kernel⟩
