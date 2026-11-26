import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23975

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 4 are the points, gate j writes wire 5 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_23975

open PEqualNP.Outside.L_meta_23975 in
theorem PEqualNP.Outside.L_meta_23975 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9118 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
