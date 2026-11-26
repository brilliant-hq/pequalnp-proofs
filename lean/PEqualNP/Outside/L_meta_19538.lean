import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19538

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩], 11⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19538

theorem PEqualNP.Outside.L_meta_19538 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (279 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19538.witness, PEqualNP.Outside.L_meta_19538.legal, by decide, ?_⟩
  decide +kernel
