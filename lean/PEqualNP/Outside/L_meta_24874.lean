import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_24874_aux
def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [7, 3]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [11, 13]⟩], 14⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_24874_aux

open PEqualNP.Outside.L_meta_24874_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_24874 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
