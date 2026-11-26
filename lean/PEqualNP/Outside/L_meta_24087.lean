import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24087_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
     ⟨.or, [3, 4]⟩,
     ⟨.and, [5, 6]⟩,
     ⟨.or, [5, 6]⟩,
     ⟨.or, [2, 4]⟩,
     ⟨.not, [9]⟩,
     ⟨.or, [0, 10]⟩,
     ⟨.and, [8, 11]⟩,
     ⟨.or, [7, 12]⟩], 13⟩

theorem shape : FanInTwo witness := by
  intro g h
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24087_aux

theorem PEqualNP.Outside.L_meta_24087 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (287582 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24087_aux.witness, PEqualNP.Outside.L_meta_24087_aux.shape, by decide, by decide +kernel⟩
