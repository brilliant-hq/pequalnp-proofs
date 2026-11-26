import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24089

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and, [2, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.not, [4]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [5, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24089

theorem PEqualNP.Outside.L_meta_24089 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (287709 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24089.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24089.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
