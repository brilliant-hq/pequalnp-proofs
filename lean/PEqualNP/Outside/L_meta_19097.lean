import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19097.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.not, [11]⟩], 12⟩

end PEqualNP.Outside.L_meta_19097.Helpers

theorem PEqualNP.Outside.L_meta_19097 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1983 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19097.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19097.Helpers.witness]
