import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19108.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19108.Helpers

theorem PEqualNP.Outside.L_meta_19108 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15615 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19108.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19108.Helpers.witness]
