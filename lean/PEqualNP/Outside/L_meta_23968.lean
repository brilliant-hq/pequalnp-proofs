import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23968
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness23968 : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [9, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_23968

open PEqualNP.Outside.L_meta_23968 in
theorem PEqualNP.Outside.L_meta_23968 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8653 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witness23968, ?_, by decide +kernel, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, witness23968]
