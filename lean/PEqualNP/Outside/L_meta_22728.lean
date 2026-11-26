import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22728

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [8, 2]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.or, [7, 11]⟩,
    ⟨GateOp.or, [6, 12]⟩,
    ⟨GateOp.and, [15, 3]⟩,
    ⟨GateOp.or, [0, 14]⟩,
    ⟨GateOp.or, [13, 6]⟩,
    ⟨GateOp.and, [17, 18]⟩,
    ⟨GateOp.or, [0, 13]⟩,
    ⟨GateOp.or, [19, 16]⟩,
    ⟨GateOp.and, [4, 20]⟩,
    ⟨GateOp.or, [22, 21]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22728

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22728 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883445 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22728.circuit, PEqualNP.Outside.L_meta_22728.shape, by decide,
    by decide +kernel⟩
