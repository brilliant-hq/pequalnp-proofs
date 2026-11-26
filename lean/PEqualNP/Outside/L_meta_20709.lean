import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20709

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [14, 8]⟩, ⟨GateOp.and, [15, 11]⟩, ⟨GateOp.or, [16, 13]⟩], 17⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (31917056 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20709

theorem PEqualNP.Outside.L_meta_20709 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31917056 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_20709.upperC, PEqualNP.Outside.L_meta_20709.upper_mono, by decide, PEqualNP.Outside.L_meta_20709.upper_rep⟩
