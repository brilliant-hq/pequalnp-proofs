import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20714

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[], 4⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp [upperC] at hg

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (32505856 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20714

theorem PEqualNP.Outside.L_meta_20714 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32505856 : ℕ).testBit (5 * u.val + v.val)) 4 :=
  ⟨PEqualNP.Outside.L_meta_20714.upperC, PEqualNP.Outside.L_meta_20714.upper_mono, by decide, PEqualNP.Outside.L_meta_20714.upper_rep⟩
