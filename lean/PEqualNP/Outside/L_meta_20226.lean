import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20226

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 14]⟩,
    ⟨GateOp.or, [0, 13]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [7, 17]⟩,
    ⟨GateOp.or, [12, 2]⟩,
    ⟨GateOp.or, [16, 19]⟩,
    ⟨GateOp.or, [18, 19]⟩,
    ⟨GateOp.and, [20, 22]⟩,
    ⟨GateOp.or, [15, 5]⟩,
    ⟨GateOp.or, [20, 24]⟩,
    ⟨GateOp.or, [18, 1]⟩,
    ⟨GateOp.or, [25, 3]⟩,
    ⟨GateOp.or, [6, 26]⟩,
    ⟨GateOp.or, [6, 10]⟩,
    ⟨GateOp.or, [27, 1]⟩,
    ⟨GateOp.or, [29, 25]⟩,
    ⟨GateOp.or, [24, 26]⟩,
    ⟨GateOp.or, [31, 17]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.and, [11, 33]⟩,
    ⟨GateOp.or, [28, 16]⟩,
    ⟨GateOp.and, [21, 32]⟩,
    ⟨GateOp.and, [29, 30]⟩,
    ⟨GateOp.and, [36, 34]⟩,
    ⟨GateOp.or, [37, 39]⟩,
    ⟨GateOp.or, [23, 35]⟩,
    ⟨GateOp.or, [41, 40]⟩,
    ⟨GateOp.or, [42, 38]⟩]
  output := 43

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_20226

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20226 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15103503539490350745 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨PEqualNP.Outside.L_meta_20226.circuit, PEqualNP.Outside.L_meta_20226.shape, by decide,
    by decide +kernel⟩
