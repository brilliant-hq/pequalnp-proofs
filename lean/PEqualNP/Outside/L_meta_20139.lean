import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20139
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [12, 15]⟩,
        ⟨GateOp.and, [16, 17]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [19, 3]⟩,
        ⟨GateOp.and, [20, 14]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [8, 13]⟩,
        ⟨GateOp.and, [22, 23]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.or, [25, 15]⟩,
        ⟨GateOp.and, [5, 26]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.and, [28, 29]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [31, 6]⟩,
        ⟨GateOp.and, [32, 11]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.or, [34, 13]⟩,
        ⟨GateOp.and, [7, 35]⟩,
        ⟨GateOp.or, [18, 21]⟩,
        ⟨GateOp.or, [24, 27]⟩,
        ⟨GateOp.or, [30, 33]⟩,
        ⟨GateOp.or, [37, 38]⟩,
        ⟨GateOp.or, [40, 39]⟩,
        ⟨GateOp.or, [41, 36]⟩ ],
    output := 42 }

theorem fan : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

end PEqualNP.Outside.L_meta_20139

theorem PEqualNP.Outside.L_meta_20139 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (3751079755257373080 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨PEqualNP.Outside.L_meta_20139.circuit,
    PEqualNP.Outside.L_meta_20139.fan, by decide, ?_⟩
  decide +kernel
