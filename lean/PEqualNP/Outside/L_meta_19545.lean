import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19545

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩], 12⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19545

theorem PEqualNP.Outside.L_meta_19545 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19545.witness, PEqualNP.Outside.L_meta_19545.legal, by decide, ?_⟩
  decide +kernel
