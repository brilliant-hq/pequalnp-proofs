import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25370.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [10, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25370.Helpers

theorem PEqualNP.Outside.L_meta_25370 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377531 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25370.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25370.Helpers.witness]
