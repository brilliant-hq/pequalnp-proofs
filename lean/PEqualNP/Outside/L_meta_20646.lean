import Mathlib
import PEqualNP.Defs

-- A representing circuit found by exhaustive search; the kernel evaluates it at the 25 inputs.
namespace PEqualNP.Outside.L_meta_20646

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperC : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [10, 2]⟩, ⟨GateOp.and, [10, 7]⟩, ⟨GateOp.or, [12, 5]⟩, ⟨GateOp.or, [13, 6]⟩, ⟨GateOp.and, [14, 11]⟩], 15⟩

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem upper_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572480 : ℕ).testBit (5 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20646

theorem PEqualNP.Outside.L_meta_20646 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7572480 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_20646.upperC, PEqualNP.Outside.L_meta_20646.upper_mono, by decide, PEqualNP.Outside.L_meta_20646.upper_rep⟩
