import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_23974_aux
def witness : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 11]⟩], 12⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_23974_aux

open PEqualNP.Outside.L_meta_23974_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_23974 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8921 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
