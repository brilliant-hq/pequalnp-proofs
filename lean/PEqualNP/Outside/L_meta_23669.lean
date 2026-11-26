import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23669_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [9, 12]⟩], 13⟩

theorem kind : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23669_aux

theorem PEqualNP.Outside.L_meta_23669 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36150 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23669_aux.circuit, PEqualNP.Outside.L_meta_23669_aux.kind, by decide, by decide +kernel⟩
