import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23973

private def witness23973 : Circuit :=
  ⟨[⟨.or, [0, 3]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_23973

open PEqualNP.Outside.L_meta_23973 in
theorem PEqualNP.Outside.L_meta_23973 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8917 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witness23973, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, witness23973]
