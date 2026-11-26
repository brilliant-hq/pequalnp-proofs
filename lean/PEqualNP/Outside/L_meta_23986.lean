import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23986_aux

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [6]⟩, ⟨.and, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23986_aux

theorem PEqualNP.Outside.L_meta_23986 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13147 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23986_aux.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, PEqualNP.Outside.L_meta_23986_aux.witness]
