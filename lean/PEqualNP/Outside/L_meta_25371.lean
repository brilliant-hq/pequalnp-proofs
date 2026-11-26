import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25371.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25371.Helpers

theorem PEqualNP.Outside.L_meta_25371 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4378043 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25371.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25371.Helpers.witness]
