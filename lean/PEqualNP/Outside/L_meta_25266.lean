import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25266.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25266.Helpers

theorem PEqualNP.Outside.L_meta_25266 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25266.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25266.Helpers.witness]
