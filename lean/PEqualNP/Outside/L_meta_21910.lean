import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21910
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [1, 4]⟩,
  ⟨.and, [0, 7]⟩,
  ⟨.or, [3, 8]⟩,
  ⟨.or, [2, 9]⟩,
  ⟨.and, [6, 10]⟩], 11⟩

lemma valid : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21910

open PEqualNP.Outside.L_meta_21910 in
theorem PEqualNP.Outside.L_meta_21910 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (798 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
