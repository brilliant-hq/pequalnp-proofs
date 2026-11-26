import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25298.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25298.Helpers

theorem PEqualNP.Outside.L_meta_25298 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25298.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25298.Helpers.witness]
