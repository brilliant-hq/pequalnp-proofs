import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19109.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19109.Helpers

theorem PEqualNP.Outside.L_meta_19109 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15838 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19109.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19109.Helpers.witness]
