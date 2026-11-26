import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25388

theorem main_proof : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6376887 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [6, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [3, 0]⟩, ⟨.not, [11]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

end PEqualNP.Outside.L_meta_25388

theorem PEqualNP.Outside.L_meta_25388 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6376887 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := PEqualNP.Outside.L_meta_25388.main_proof
