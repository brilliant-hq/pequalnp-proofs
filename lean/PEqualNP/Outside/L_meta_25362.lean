import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25362.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25362.Helpers

theorem PEqualNP.Outside.L_meta_25362 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198071 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25362.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25362.Helpers.witness]
