import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22197

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 5 are the points, gate j writes wire 6 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩,
    ⟨.or, [0, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.not, [12]⟩,
    ⟨.and, [2, 13]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [16, 15]⟩], 17⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_22197

open PEqualNP.Outside.L_meta_22197 in
theorem PEqualNP.Outside.L_meta_22197 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17201 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
