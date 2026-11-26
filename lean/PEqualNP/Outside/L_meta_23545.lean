import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23545_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.not, [12]⟩], 13⟩

theorem shape : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23545_aux

theorem PEqualNP.Outside.L_meta_23545 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20159 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23545_aux.circuit, PEqualNP.Outside.L_meta_23545_aux.shape,
    by decide, by decide +kernel⟩
