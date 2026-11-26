import PEqualNP.Defs

-- An explicit circuit of fan-in two (7 AND/OR gates, 1 NOT gate(s)) found by a SAT search for exact
-- synthesis. Gate kinds by cases (the pattern of the merged L_meta_10258), the size
-- and the 16 promise inputs by `decide`.

namespace PEqualNP.Outside.L_meta_19181_aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 to 3 are the left vertices, 4 to 7 the right ones; gate `j` writes wire `8 + j`. -/
def C : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19181_aux

theorem PEqualNP.Outside.L_meta_19181 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5758 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19181_aux.C, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19181_aux.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
