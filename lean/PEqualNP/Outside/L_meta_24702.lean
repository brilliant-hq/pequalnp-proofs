import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24702_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.not, [6]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [10, 12]⟩], 13⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24702_aux

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_24702 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16825 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24702_aux.circuit, PEqualNP.Outside.L_meta_24702_aux.fanin, by decide, by decide +kernel⟩
