import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20696

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [10, 5]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [14, 8]⟩, ⟨GateOp.and, [15, 13]⟩, ⟨GateOp.or, [16, 11]⟩], 17⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16201760 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20696

theorem PEqualNP.Outside.L_meta_20696 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16201760 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_20696.upperC, PEqualNP.Outside.L_meta_20696.upper_mono, by decide, PEqualNP.Outside.L_meta_20696.upper_rep⟩
