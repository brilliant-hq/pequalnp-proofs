import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21887_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩], 10⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 5 := by decide +kernel

end PEqualNP.Outside.L_meta_21887_aux

theorem PEqualNP.Outside.L_meta_21887 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (282 : ℕ).testBit (6 * min i.val j.val + max i.val j.val))  := by
  exact ⟨PEqualNP.Outside.L_meta_21887_aux.circ, PEqualNP.Outside.L_meta_21887_aux.h_ok, PEqualNP.Outside.L_meta_21887_aux.h_sz, by decide +kernel⟩
