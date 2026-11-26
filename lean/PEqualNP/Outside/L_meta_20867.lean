import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20867_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [10, 2]⟩,
    ⟨GateOp.and, [11, 5]⟩,
    ⟨GateOp.and, [3, 6]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.or, [14, 8]⟩,
    ⟨GateOp.or, [15, 9]⟩,
    ⟨GateOp.and, [4, 16]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [18, 17]⟩
    ]
    output := 19 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 10 := by decide +kernel

set_option maxRecDepth 40000 in
theorem C_rep : Represents (fun u v : Fin 5 => (30475297 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_20867_aux

theorem PEqualNP.Outside.L_meta_20867 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30475297 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_20867_aux.C, PEqualNP.Outside.L_meta_20867_aux.C_ok, PEqualNP.Outside.L_meta_20867_aux.C_size, PEqualNP.Outside.L_meta_20867_aux.C_rep⟩
