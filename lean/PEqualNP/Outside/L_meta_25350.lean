import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25350.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [8, 13]⟩, ⟨GateOp.or, [10, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25350.Helpers

theorem PEqualNP.Outside.L_meta_25350 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197163 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25350.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25350.Helpers.witness]
