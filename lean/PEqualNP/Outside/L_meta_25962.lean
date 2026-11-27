import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25962 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 7, 3, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.and, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
