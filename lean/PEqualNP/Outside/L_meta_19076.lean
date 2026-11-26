import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19076.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [0, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19076.Helpers

theorem PEqualNP.Outside.L_meta_19076 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4735 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19076.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19076.Helpers.witness]
