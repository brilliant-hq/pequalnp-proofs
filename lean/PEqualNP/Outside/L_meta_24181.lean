import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24181_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [0, 7]⟩, ⟨.not, [11]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem kind : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24181_aux

theorem PEqualNP.Outside.L_meta_24181 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266906 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24181_aux.circuit, PEqualNP.Outside.L_meta_24181_aux.kind, by decide, by decide +kernel⟩
