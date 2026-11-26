import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24361_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩, ⟨.not, [11]⟩], 12⟩

theorem kind : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24361_aux

theorem PEqualNP.Outside.L_meta_24361 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843965 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24361_aux.circuit, PEqualNP.Outside.L_meta_24361_aux.kind, by decide, by decide +kernel⟩
