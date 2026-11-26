import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22876

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [7, 11]⟩,
    ⟨GateOp.or, [6, 10]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [2, 14]⟩,
    ⟨GateOp.and, [3, 13]⟩,
    ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.or, [8, 12]⟩,
    ⟨GateOp.or, [18, 19]⟩,
    ⟨GateOp.and, [15, 20]⟩,
    ⟨GateOp.or, [16, 21]⟩,
    ⟨GateOp.or, [17, 22]⟩], 23⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : circ.size ≤ 15 := by decide

end PEqualNP.Outside.L_meta_22876

theorem PEqualNP.Outside.L_meta_22876 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883965 : ℕ).testBit (6 * u.val + v.val)) 15) :=
  ⟨PEqualNP.Outside.L_meta_22876.circ, PEqualNP.Outside.L_meta_22876.mono, PEqualNP.Outside.L_meta_22876.size_le, by decide +kernel⟩
