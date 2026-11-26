import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22560

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.or, [4, 10]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.or, [9, 13]⟩,
    ⟨GateOp.and, [12, 14]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.and, [16, 11]⟩,
    ⟨GateOp.or, [1, 16]⟩,
    ⟨GateOp.or, [17, 8]⟩,
    ⟨GateOp.or, [19, 7]⟩,
    ⟨GateOp.and, [18, 20]⟩,
    ⟨GateOp.or, [21, 15]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22560

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22560 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947644 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22560.circuit, PEqualNP.Outside.L_meta_22560.shape, by decide,
    by decide +kernel⟩
