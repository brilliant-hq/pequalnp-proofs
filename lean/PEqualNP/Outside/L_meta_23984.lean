import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23984_aux

def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [5, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23984_aux

theorem PEqualNP.Outside.L_meta_23984 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13085 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23984_aux.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, PEqualNP.Outside.L_meta_23984_aux.witness]
