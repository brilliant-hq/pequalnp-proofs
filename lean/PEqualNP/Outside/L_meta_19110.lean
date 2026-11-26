import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19110.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19110.Helpers

theorem PEqualNP.Outside.L_meta_19110 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (15839 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19110.Helpers.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19110.Helpers.witness]
