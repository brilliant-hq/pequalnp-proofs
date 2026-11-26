import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25361.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.not, [2]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25361.Helpers

theorem PEqualNP.Outside.L_meta_25361 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197435 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25361.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25361.Helpers.witness]
