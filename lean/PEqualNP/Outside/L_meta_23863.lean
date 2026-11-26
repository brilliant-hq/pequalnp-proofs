import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23863

open PEqualNP.CircuitLowerBounds

private def circuit23863 : Circuit :=
  ⟨[⟨.or, [3, 4]⟩,
      ⟨.and, [1, 5]⟩,
      ⟨.or, [1, 5]⟩,
      ⟨.not, [7]⟩,
      ⟨.or, [6, 8]⟩,
      ⟨.or, [0, 9]⟩], 10⟩

end PEqualNP.Outside.L_meta_23863

theorem PEqualNP.Outside.L_meta_23863 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4895 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23863.circuit23863, ?_, by decide +kernel, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_23863.circuit23863]
