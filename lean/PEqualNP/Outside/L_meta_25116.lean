import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25116_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [5, 2]⟩,
     ⟨.not, [6]⟩,
     ⟨.or, [2, 1]⟩,
     ⟨.or, [5, 4]⟩,
     ⟨.or, [3, 9]⟩,
     ⟨.and, [8, 10]⟩,
     ⟨.or, [7, 11]⟩,
     ⟨.or, [0, 12]⟩], 13⟩

theorem shape : FanInTwo witness := by
  intro g h
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25116_aux

theorem PEqualNP.Outside.L_meta_25116 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274960063 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25116_aux.witness, PEqualNP.Outside.L_meta_25116_aux.shape, by decide, by decide +kernel⟩
