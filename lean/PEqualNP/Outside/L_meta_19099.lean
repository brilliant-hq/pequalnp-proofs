import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19099.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [3]⟩], 8⟩

end PEqualNP.Outside.L_meta_19099.Helpers

theorem PEqualNP.Outside.L_meta_19099 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 1 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4095 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19099.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19099.Helpers.witness]
