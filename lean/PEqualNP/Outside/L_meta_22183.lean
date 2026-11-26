import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22183_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness, found by a SAT search: wires 0 to 3 are the rows, 4 to 9 the columns, gate j is
wire 10 + j. -/
def witness : Circuit := ⟨[⟨.and, [1, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [6, 15]⟩, ⟨.and, [16, 18]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [19, 20]⟩], 21⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (841516 : ℕ).testBit (6 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_22183_aux

theorem PEqualNP.Outside.L_meta_22183 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841516 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22183_aux.witness, PEqualNP.Outside.L_meta_22183_aux.basis, by decide,
    PEqualNP.Outside.L_meta_22183_aux.correct⟩
