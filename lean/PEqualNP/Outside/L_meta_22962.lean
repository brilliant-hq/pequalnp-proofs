import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22962_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [8, 9]⟩], 10⟩

theorem h_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem h_sz : circ.size ≤ 5 := by
  decide +kernel

theorem h_eval : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (35888 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22962_aux

theorem PEqualNP.Outside.L_meta_22962 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (35888 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22962_aux.circ, PEqualNP.Outside.L_meta_22962_aux.h_mono, PEqualNP.Outside.L_meta_22962_aux.h_sz, PEqualNP.Outside.L_meta_22962_aux.h_eval⟩
