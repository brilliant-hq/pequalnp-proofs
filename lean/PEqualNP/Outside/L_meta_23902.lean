import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23902

def witness : Circuit := ⟨[
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩
  ], 10⟩

lemma witness_properties :
    FanInTwo witness ∧ witness.size = 6 ∧ witness.depth 5 ≤ 3 := by
  refine ⟨?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23902

theorem PEqualNP.Outside.L_meta_23902 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274910 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23902.witness, PEqualNP.Outside.L_meta_23902.witness_properties.1, ?_, by decide +kernel⟩
  rw [PEqualNP.Outside.L_meta_23902.witness_properties.2.1]
  decide
