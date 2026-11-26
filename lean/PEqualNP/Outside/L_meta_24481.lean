import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24481

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.not, [0]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24481

theorem PEqualNP.Outside.L_meta_24481 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24481.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24481.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
