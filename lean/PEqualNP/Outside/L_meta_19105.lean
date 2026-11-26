import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19105.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19105.Helpers

theorem PEqualNP.Outside.L_meta_19105 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13807 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19105.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19105.Helpers.witness]
