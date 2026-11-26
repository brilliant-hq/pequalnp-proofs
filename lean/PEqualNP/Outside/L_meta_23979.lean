import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23979

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [6, 9]⟩], 10⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23979

theorem PEqualNP.Outside.L_meta_23979 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12761 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23979.witness, PEqualNP.Outside.L_meta_23979.legal, by decide +kernel, by decide +kernel⟩
