import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22492

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.not, [0]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.not, [1]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.and, [7, 10]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.not, [12]⟩], 13⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22492

open PEqualNP.Outside.L_meta_22492
theorem PEqualNP.Outside.L_meta_22492 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (411 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, fan, by decide, by decide +kernel⟩
