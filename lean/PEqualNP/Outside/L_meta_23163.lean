import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23163

def witness : Circuit := ⟨[
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [12, 9]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.and, [2, 14]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [18, 17]⟩
  ], 19⟩

lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23163

theorem PEqualNP.Outside.L_meta_23163 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14190 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23163.witness, PEqualNP.Outside.L_meta_23163.witness_mono, by decide, by decide +kernel⟩
