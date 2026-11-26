import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25063.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [10, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_25063.Helpers

theorem PEqualNP.Outside.L_meta_25063 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649254 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25063.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25063.Helpers.witness]
