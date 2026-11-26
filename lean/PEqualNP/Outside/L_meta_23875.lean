import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23875

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.and, [2, 3]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.or, [5, 10]⟩], 11⟩

lemma fanInTwo : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro gate hgate
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23875

theorem PEqualNP.Outside.L_meta_23875 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (8791 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23875.circuit, PEqualNP.Outside.L_meta_23875.fanInTwo,
    by decide, by decide +kernel⟩
