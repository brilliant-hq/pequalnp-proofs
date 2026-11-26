import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23925

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.or, [8, 9]⟩], 10⟩

private theorem witness_fanInTwo : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23925

theorem PEqualNP.Outside.L_meta_23925 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (92 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23925.witness, PEqualNP.Outside.L_meta_23925.witness_fanInTwo, by decide, by decide +kernel⟩
