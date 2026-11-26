import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23941

def witness : Circuit := ⟨[
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [10, 11]⟩
  ], 12⟩

lemma witness_properties :
    FanInTwo witness ∧ witness.size ≤ 8 ∧ witness.depth 5 ≤ 5 := by
  refine ⟨?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23941

theorem PEqualNP.Outside.L_meta_23941 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4504 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23941.witness, PEqualNP.Outside.L_meta_23941.witness_properties.1,
    PEqualNP.Outside.L_meta_23941.witness_properties.2.1, by decide +kernel⟩
