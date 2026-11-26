import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19068.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19068.Helpers

theorem PEqualNP.Outside.L_meta_19068 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (379 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19068.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19068.Helpers.witness]
