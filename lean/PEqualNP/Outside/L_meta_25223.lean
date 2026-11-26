import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25223

theorem main_proof : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36670 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 0]⟩, ⟨.and, [1, 0]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [8, 3]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [14, 10]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

end PEqualNP.Outside.L_meta_25223

theorem PEqualNP.Outside.L_meta_25223 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36670 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := PEqualNP.Outside.L_meta_25223.main_proof
