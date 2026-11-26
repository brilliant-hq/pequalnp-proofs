import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19094.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_19094.Helpers

theorem PEqualNP.Outside.L_meta_19094 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1919 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19094.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19094.Helpers.witness]
