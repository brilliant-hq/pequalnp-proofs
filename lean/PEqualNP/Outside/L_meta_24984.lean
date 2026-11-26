import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24984

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.not, [5]⟩, ⟨.and, [3, 8]⟩, ⟨.not, [2]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24984

theorem PEqualNP.Outside.L_meta_24984 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6524603 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24984.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24984.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
