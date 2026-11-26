import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23539_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩,
    ⟨.not, [5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.and, [7, 10]⟩,
    ⟨.or, [11, 12]⟩], 13⟩

theorem shape : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23539_aux

theorem PEqualNP.Outside.L_meta_23539 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18207 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23539_aux.circuit, PEqualNP.Outside.L_meta_23539_aux.shape,
    by decide, by decide +kernel⟩
