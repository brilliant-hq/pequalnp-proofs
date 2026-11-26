import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24361

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 5 are the points, gate j writes wire 6 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 8]⟩,
    ⟨.or, [5, 9]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_24361

open PEqualNP.Outside.L_meta_24361 in
theorem PEqualNP.Outside.L_meta_24361 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843965 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
