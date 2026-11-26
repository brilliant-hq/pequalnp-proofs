import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19101.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19101.Helpers

theorem PEqualNP.Outside.L_meta_19101 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6127 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19101.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19101.Helpers.witness]
