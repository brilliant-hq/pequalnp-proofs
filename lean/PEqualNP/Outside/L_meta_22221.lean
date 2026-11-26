import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22221

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 5 are the points, gate j writes wire 6 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩,
    ⟨.not, [9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 12]⟩,
    ⟨.or, [3, 4]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_22221

open PEqualNP.Outside.L_meta_22221 in
theorem PEqualNP.Outside.L_meta_22221 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17960 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
