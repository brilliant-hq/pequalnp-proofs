import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23987

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 4 are the points, gate j writes wire 5 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 6]⟩,
    ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_23987

open PEqualNP.Outside.L_meta_23987 in
theorem PEqualNP.Outside.L_meta_23987 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13150 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
