import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23864

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.not, [5]⟩, ⟨.or, [3, 4]⟩,
    ⟨.and, [6, 7]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [8, 9]⟩,
    ⟨.not, [10]⟩], 11⟩

end PEqualNP.Outside.L_meta_23864

open PEqualNP.Outside.L_meta_23864

theorem PEqualNP.Outside.L_meta_23864 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4955 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [witness] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp
