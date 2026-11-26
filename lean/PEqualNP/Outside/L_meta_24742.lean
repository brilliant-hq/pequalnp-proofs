import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_24742_aux
def witness : Circuit := ⟨[⟨.or, [2, 4]⟩, ⟨.not, [6]⟩, ⟨.and, [7, 0]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_24742_aux

open PEqualNP.Outside.L_meta_24742_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_24742 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100139 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
