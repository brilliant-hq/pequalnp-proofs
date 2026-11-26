import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25318.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [7, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25318.Helpers

theorem PEqualNP.Outside.L_meta_25318 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165679 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25318.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25318.Helpers.witness]
