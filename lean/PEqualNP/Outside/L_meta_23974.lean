import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23974

private def witness23974 : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [8, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23974

open PEqualNP.Outside.L_meta_23974 in
theorem PEqualNP.Outside.L_meta_23974 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8921 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witness23974, ?_, by decide +kernel, by decide +kernel⟩
  simp [FanInTwo, witness23974]
