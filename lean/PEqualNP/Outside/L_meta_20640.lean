import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20640_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness, found by a SAT search: wires 0 to 4 are the left vertices, 5 to 9 the right ones,
gate j is wire 10 + j. -/
def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [10, 13]⟩], 14⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7438336 : ℕ).testBit (5 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_20640_aux

theorem PEqualNP.Outside.L_meta_20640 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7438336 : ℕ).testBit (5 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_20640_aux.witness, PEqualNP.Outside.L_meta_20640_aux.basis, by decide,
    PEqualNP.Outside.L_meta_20640_aux.correct⟩
