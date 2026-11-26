import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25400.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25400.Helpers

theorem PEqualNP.Outside.L_meta_25400 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409149 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25400.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25400.Helpers.witness]
