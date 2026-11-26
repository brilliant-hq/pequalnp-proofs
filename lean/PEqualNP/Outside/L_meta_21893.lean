import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21893_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [5, 7]⟩,
    ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩], 10⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21893_aux

theorem PEqualNP.Outside.L_meta_21893 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3903 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21893_aux.circuit, PEqualNP.Outside.L_meta_21893_aux.mono,
    by decide, by decide +kernel⟩
