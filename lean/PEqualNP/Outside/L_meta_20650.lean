import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [11, 10]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [13, 4]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (15826944 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20650

theorem PEqualNP.Outside.L_meta_20650 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15826944 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_20650.upperC, PEqualNP.Outside.L_meta_20650.upper_mono, by decide, PEqualNP.Outside.L_meta_20650.upper_rep⟩
