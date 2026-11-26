import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_23979_aux
def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [7]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [8, 10]⟩], 11⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_23979_aux

open PEqualNP.Outside.L_meta_23979_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_23979 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12761 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
