import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19104.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [4, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19104.Helpers

theorem PEqualNP.Outside.L_meta_19104 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13279 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19104.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19104.Helpers.witness]
