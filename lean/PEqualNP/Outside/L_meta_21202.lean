import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21202

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [6, 1]⟩,
    ⟨GateOp.or, [8, 7]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [2, 11]⟩,
    ⟨GateOp.and, [12, 13]⟩,
    ⟨GateOp.or, [4, 14]⟩,
    ⟨GateOp.or, [3, 10]⟩,
    ⟨GateOp.and, [16, 9]⟩,
    ⟨GateOp.or, [15, 17]⟩]
  output := 18

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21202

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21202 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106365 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_21202.circuit, PEqualNP.Outside.L_meta_21202.shape, by decide,
    by decide +kernel⟩
