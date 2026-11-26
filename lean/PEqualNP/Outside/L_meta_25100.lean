import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25100.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_25100.Helpers

theorem PEqualNP.Outside.L_meta_25100 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274845501 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25100.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25100.Helpers.witness]
