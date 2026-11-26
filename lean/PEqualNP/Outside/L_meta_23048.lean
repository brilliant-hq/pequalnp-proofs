import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23048

private def witness23048 : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [6, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23048

open PEqualNP.Outside.L_meta_23048 in
theorem PEqualNP.Outside.L_meta_23048 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3902 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness23048, ?_, by decide +kernel, by decide +kernel⟩
  simp [Monotone2, witness23048]
