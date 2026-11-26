import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20019

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [7, 2]⟩,
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.or, [16, 6]⟩,
    ⟨GateOp.or, [3, 18]⟩,
    ⟨GateOp.or, [0, 18]⟩,
    ⟨GateOp.or, [17, 0]⟩,
    ⟨GateOp.or, [3, 21]⟩,
    ⟨GateOp.or, [2, 21]⟩,
    ⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.or, [24, 25]⟩,
    ⟨GateOp.or, [4, 1]⟩,
    ⟨GateOp.or, [16, 27]⟩,
    ⟨GateOp.or, [25, 27]⟩,
    ⟨GateOp.or, [24, 0]⟩,
    ⟨GateOp.or, [7, 30]⟩,
    ⟨GateOp.and, [28, 8]⟩,
    ⟨GateOp.and, [26, 9]⟩,
    ⟨GateOp.and, [19, 10]⟩,
    ⟨GateOp.and, [31, 11]⟩,
    ⟨GateOp.and, [29, 12]⟩,
    ⟨GateOp.and, [20, 13]⟩,
    ⟨GateOp.and, [22, 14]⟩,
    ⟨GateOp.and, [23, 15]⟩,
    ⟨GateOp.or, [32, 33]⟩,
    ⟨GateOp.or, [40, 34]⟩,
    ⟨GateOp.or, [41, 35]⟩,
    ⟨GateOp.or, [42, 36]⟩,
    ⟨GateOp.or, [43, 37]⟩,
    ⟨GateOp.or, [44, 38]⟩,
    ⟨GateOp.or, [45, 39]⟩]
  output := 46

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_20019

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20019 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3258023176858573800 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  exact ⟨PEqualNP.Outside.L_meta_20019.circuit, PEqualNP.Outside.L_meta_20019.shape, by decide,
    by decide +kernel⟩
