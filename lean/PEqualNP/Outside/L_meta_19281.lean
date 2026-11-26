import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19281_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.not, [9]⟩,
    ⟨GateOp.or, [10, 4]⟩
    ]
    output := 11 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 4 := by decide +kernel

theorem C_rep : Represents (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19281_aux

theorem PEqualNP.Outside.L_meta_19281 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19281_aux.C, PEqualNP.Outside.L_meta_19281_aux.C_fanInTwo, PEqualNP.Outside.L_meta_19281_aux.C_size, PEqualNP.Outside.L_meta_19281_aux.C_rep⟩
