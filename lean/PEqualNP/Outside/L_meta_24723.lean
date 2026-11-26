import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24723.Helpers

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩

end PEqualNP.Outside.L_meta_24723.Helpers

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_24723 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20026 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24723.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24723.Helpers.witness]
