import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23969

private def witness23969 : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23969

open PEqualNP.Outside.L_meta_23969 in
theorem PEqualNP.Outside.L_meta_23969 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8661 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witness23969, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, witness23969]
