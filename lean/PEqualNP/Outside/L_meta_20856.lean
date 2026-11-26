import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20856_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 5]⟩
      , ⟨GateOp.and, [1, 6]⟩
      , ⟨GateOp.and, [2, 7]⟩
      , ⟨GateOp.or, [3, 4]⟩
      , ⟨GateOp.or, [5, 8]⟩
      , ⟨GateOp.or, [14, 9]⟩
      , ⟨GateOp.and, [13, 15]⟩
      , ⟨GateOp.or, [10, 11]⟩
      , ⟨GateOp.or, [17, 12]⟩
      , ⟨GateOp.or, [18, 16]⟩ ]
    output := 19 }

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (27037761 : ℕ).testBit (5 * u.val + v.val)) circ := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_20856_aux

theorem PEqualNP.Outside.L_meta_20856 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27037761 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_20856_aux.circ,
    PEqualNP.Outside.L_meta_20856_aux.mono,
    by decide,
    PEqualNP.Outside.L_meta_20856_aux.rep⟩
