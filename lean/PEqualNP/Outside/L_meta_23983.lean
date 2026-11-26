import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23983_aux

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [2, 5]⟩, ⟨.not, [7]⟩, ⟨.not, [3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [8, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23983_aux

theorem PEqualNP.Outside.L_meta_23983 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13019 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23983_aux.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, PEqualNP.Outside.L_meta_23983_aux.witness]
