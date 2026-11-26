import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_24980_aux
def witness : Circuit := ⟨[⟨.not, [4]⟩, ⟨.and, [6, 2]⟩, ⟨.not, [5]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_24980_aux

open PEqualNP.Outside.L_meta_24980_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_24980 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475580 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
