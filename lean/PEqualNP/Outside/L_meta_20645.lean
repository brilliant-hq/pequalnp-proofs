import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20645

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.and, [14, 12]⟩], 15⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7570432 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20645

theorem PEqualNP.Outside.L_meta_20645 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7570432 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_20645.upperC, PEqualNP.Outside.L_meta_20645.upper_mono, by decide, PEqualNP.Outside.L_meta_20645.upper_rep⟩
