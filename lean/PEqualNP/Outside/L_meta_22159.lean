import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22159

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [7, 6]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [0, 11]⟩,
        ⟨GateOp.or, [8, 6]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [9, 13]⟩,
        ⟨GateOp.and, [10, 14]⟩,
        ⟨GateOp.and, [15, 0]⟩,
        ⟨GateOp.and, [5, 12]⟩,
        ⟨GateOp.or, [4, 17]⟩,
        ⟨GateOp.or, [18, 19]⟩,
        ⟨GateOp.or, [20, 16]⟩ ],
    output := 21 }

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840695 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_22159

theorem PEqualNP.Outside.L_meta_22159 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840695 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_22159.circ, PEqualNP.Outside.L_meta_22159.circ_mono, by decide, PEqualNP.Outside.L_meta_22159.circ_rep⟩
