import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19113.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.not, [9]⟩], 10⟩

end PEqualNP.Outside.L_meta_19113.Helpers

theorem PEqualNP.Outside.L_meta_19113 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (16383 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19113.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19113.Helpers.witness]
