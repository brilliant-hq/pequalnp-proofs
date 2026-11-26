import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_24840_aux
def witness : Circuit := ⟨[⟨.and, [2, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [7]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 2]⟩, ⟨.not, [11]⟩, ⟨.or, [6, 12]⟩], 13⟩

lemma fit : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_24840_aux

open PEqualNP.Outside.L_meta_24840_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_24840 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165419 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
