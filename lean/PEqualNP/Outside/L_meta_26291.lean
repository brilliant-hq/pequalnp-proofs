import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_26291 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 7, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨GateOp.or, [3, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 9]⟩], 10⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
