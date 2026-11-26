import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19106.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19106.Helpers

theorem PEqualNP.Outside.L_meta_19106 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (14287 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19106.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19106.Helpers.witness]
