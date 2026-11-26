import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21373
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.and, [13, 0]⟩,
        ⟨GateOp.or, [9, 7]⟩,
        ⟨GateOp.and, [10, 15]⟩,
        ⟨GateOp.or, [11, 0]⟩,
        ⟨GateOp.or, [14, 16]⟩,
        ⟨GateOp.and, [17, 12]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

theorem fan : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

end PEqualNP.Outside.L_meta_21373

theorem PEqualNP.Outside.L_meta_21373 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 5) => (103895 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_21373.circuit,
    PEqualNP.Outside.L_meta_21373.fan, by decide, ?_⟩
  decide +kernel
