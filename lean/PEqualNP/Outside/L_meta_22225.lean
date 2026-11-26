import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22225

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [8, 2]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.or, [12, 6]⟩,
        ⟨GateOp.or, [11, 4]⟩,
        ⟨GateOp.or, [3, 10]⟩,
        ⟨GateOp.and, [15, 16]⟩,
        ⟨GateOp.or, [13, 15]⟩,
        ⟨GateOp.or, [14, 17]⟩,
        ⟨GateOp.and, [19, 18]⟩ ],
    output := 20 }

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma circ_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (849715 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_22225

theorem PEqualNP.Outside.L_meta_22225 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849715 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_22225.circ, PEqualNP.Outside.L_meta_22225.circ_mono, by decide, PEqualNP.Outside.L_meta_22225.circ_rep⟩
