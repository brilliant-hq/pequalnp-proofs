import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22392

open PEqualNP.CircuitLowerBounds

-- Wires 0 to 3 are the rows, 4 to 9 the columns; gate j writes wire 10 + j.
-- Four blocks, rows x columns: 0 x {2,4,5}, 1 x {4}, {1,2} x {2,3}, {2,3} x {0,1},
-- with the column group {4,5} built once and reused inside {2,4,5}.
def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.and, [1, 8]⟩,
        ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [16, 17]⟩,
        ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.or, [20, 21]⟩ ],
    output := 22 }

theorem circ_mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

theorem circ_rep : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (849716 : ℕ).testBit (6 * u.val + v.val)) circ := by
  unfold PEqualNP.Represents.Represents
  decide

end PEqualNP.Outside.L_meta_22392

theorem PEqualNP.Outside.L_meta_22392 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849716 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22392.circ, PEqualNP.Outside.L_meta_22392.circ_mono,
    by decide, PEqualNP.Outside.L_meta_22392.circ_rep⟩
