import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19103.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19103.Helpers

theorem PEqualNP.Outside.L_meta_19103 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13278 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19103.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19103.Helpers.witness]
