import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_24721_aux
def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [6, 1]⟩, ⟨.not, [0]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 1]⟩, ⟨.not, [12]⟩, ⟨.or, [7, 13]⟩], 14⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_24721_aux

open PEqualNP.Outside.L_meta_24721_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_24721 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17165 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
