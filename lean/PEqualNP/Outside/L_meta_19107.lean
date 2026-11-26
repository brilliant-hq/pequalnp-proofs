import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19107.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.not, [13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19107.Helpers

theorem PEqualNP.Outside.L_meta_19107 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (14303 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19107.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19107.Helpers.witness]
