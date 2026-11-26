import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23670

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 5 are the points, gate j writes wire 6 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_23670

open PEqualNP.Outside.L_meta_23670 in
theorem PEqualNP.Outside.L_meta_23670 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36152 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
