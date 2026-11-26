import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20651

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [11, 5]⟩, ⟨GateOp.or, [12, 6]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.and, [14, 10]⟩], 15⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (15958016 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20651

theorem PEqualNP.Outside.L_meta_20651 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15958016 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_20651.upperC, PEqualNP.Outside.L_meta_20651.upper_mono, by decide, PEqualNP.Outside.L_meta_20651.upper_rep⟩
