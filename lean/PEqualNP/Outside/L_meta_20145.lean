import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20145_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [8, 13]⟩,
    ⟨GateOp.or, [10, 15]⟩,
    ⟨GateOp.or, [12, 17]⟩,
    ⟨GateOp.or, [16, 18]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [16, 12]⟩,
    ⟨GateOp.or, [19, 14]⟩,
    ⟨GateOp.or, [22, 21]⟩,
    ⟨GateOp.or, [10, 23]⟩,
    ⟨GateOp.or, [10, 22]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [19, 18]⟩,
    ⟨GateOp.or, [13, 20]⟩,
    ⟨GateOp.or, [11, 23]⟩,
    ⟨GateOp.or, [9, 27]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.or, [8, 26]⟩,
    ⟨GateOp.and, [0, 24]⟩,
    ⟨GateOp.and, [1, 32]⟩,
    ⟨GateOp.and, [2, 28]⟩,
    ⟨GateOp.and, [3, 33]⟩,
    ⟨GateOp.and, [4, 30]⟩,
    ⟨GateOp.and, [5, 25]⟩,
    ⟨GateOp.and, [6, 31]⟩,
    ⟨GateOp.and, [7, 29]⟩,
    ⟨GateOp.or, [34, 35]⟩,
    ⟨GateOp.or, [42, 36]⟩,
    ⟨GateOp.or, [43, 37]⟩,
    ⟨GateOp.or, [44, 38]⟩,
    ⟨GateOp.or, [45, 39]⟩,
    ⟨GateOp.or, [46, 40]⟩,
    ⟨GateOp.or, [47, 41]⟩
    ]
    output := 48 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 33 := by decide +kernel

set_option maxRecDepth 40000 in
theorem C_rep : Represents (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_20145_aux

theorem PEqualNP.Outside.L_meta_20145 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_20145_aux.C, PEqualNP.Outside.L_meta_20145_aux.C_ok, PEqualNP.Outside.L_meta_20145_aux.C_size, PEqualNP.Outside.L_meta_20145_aux.C_rep⟩
