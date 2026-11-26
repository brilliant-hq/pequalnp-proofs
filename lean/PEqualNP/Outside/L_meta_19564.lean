import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19564.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [13, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_19564.Helpers

theorem PEqualNP.Outside.L_meta_19564 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24489316 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19564.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19564.Helpers.witness]
