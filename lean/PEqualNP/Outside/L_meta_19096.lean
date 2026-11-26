import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19096

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [2, 7]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩], 14⟩

theorem legal : FanInTwo witness := by simp [FanInTwo, witness]

theorem represents : PEqualNP.Represents.Represents
    (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_19096

theorem PEqualNP.Outside.L_meta_19096 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_19096.witness, PEqualNP.Outside.L_meta_19096.legal,
    by decide, PEqualNP.Outside.L_meta_19096.represents⟩
