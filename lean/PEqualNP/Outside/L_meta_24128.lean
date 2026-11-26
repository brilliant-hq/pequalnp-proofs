import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24128

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24128

theorem PEqualNP.Outside.L_meta_24128 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274963 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24128.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24128.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
