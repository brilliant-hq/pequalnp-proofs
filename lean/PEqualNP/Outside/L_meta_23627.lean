import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23627_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness, found by a SAT search: wires 0 to 3 are the rows, 4 to 9 the columns, gate j is
wire 10 + j. -/
def witness : Circuit := ⟨[⟨.or, [2, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [12, 16]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (274810 : ℕ).testBit (6 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_23627_aux

theorem PEqualNP.Outside.L_meta_23627 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274810 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_23627_aux.witness, PEqualNP.Outside.L_meta_23627_aux.basis, by decide,
    PEqualNP.Outside.L_meta_23627_aux.correct⟩
