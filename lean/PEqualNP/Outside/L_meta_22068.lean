import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22068

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The gate list (inputs 0 to 5 are the points, gate j writes wire 6 + j, the output is the
last gate). -/
def witness : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 8]⟩,
    ⟨.not, [0]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 9]⟩,
    ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.not, [15]⟩], 16⟩

theorem gatesOk : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩

end PEqualNP.Outside.L_meta_22068

open PEqualNP.Outside.L_meta_22068 in
theorem PEqualNP.Outside.L_meta_22068 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gatesOk, by decide, by decide +kernel⟩
