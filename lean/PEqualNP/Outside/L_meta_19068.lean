import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19068_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness: wires 0 to 3 are the left vertices, 4 to 7 the right ones, gate j is wire 8 + j. -/
def witness : Circuit := ⟨[⟨.or, [3, 7]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩

theorem basis : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents
    (fun u v : Fin 4 => (379 : ℕ).testBit (4 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_19068_aux

theorem PEqualNP.Outside.L_meta_19068 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (379 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19068_aux.witness, PEqualNP.Outside.L_meta_19068_aux.basis, by decide,
    PEqualNP.Outside.L_meta_19068_aux.correct⟩
