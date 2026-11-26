import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23987_aux

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [7]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23987_aux

theorem PEqualNP.Outside.L_meta_23987 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13150 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23987_aux.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, PEqualNP.Outside.L_meta_23987_aux.witness]
