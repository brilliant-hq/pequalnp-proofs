import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19077.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_19077.Helpers

theorem PEqualNP.Outside.L_meta_19077 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4813 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19077.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19077.Helpers.witness]
