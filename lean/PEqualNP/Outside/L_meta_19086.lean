import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19086.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19086.Helpers

theorem PEqualNP.Outside.L_meta_19086 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (375 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19086.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19086.Helpers.witness]
