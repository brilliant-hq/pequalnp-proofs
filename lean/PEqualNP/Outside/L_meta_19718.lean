import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 64 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_19718_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [8, 22]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [15, 22]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [19, 31]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [18, 36]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [21, 39]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [28, 42]⟩, ⟨.or, [30, 43]⟩, ⟨.or, [33, 44]⟩, ⟨.or, [35, 45]⟩, ⟨.or, [38, 46]⟩, ⟨.or, [41, 47]⟩], 48⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_19718_aux

open PEqualNP.Outside.L_meta_19718_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_19718 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
