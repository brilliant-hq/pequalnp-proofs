import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19544

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [4, 8]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩], 12⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19544

theorem PEqualNP.Outside.L_meta_19544 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4590 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19544.witness, PEqualNP.Outside.L_meta_19544.legal, by decide, ?_⟩
  decide +kernel
