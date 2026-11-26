import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24042

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [5, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24042

theorem PEqualNP.Outside.L_meta_24042 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4505 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24042.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24042.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
