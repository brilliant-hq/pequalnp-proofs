import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19111.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [0, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19111.Helpers

theorem PEqualNP.Outside.L_meta_19111 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15855 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19111.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19111.Helpers.witness]
