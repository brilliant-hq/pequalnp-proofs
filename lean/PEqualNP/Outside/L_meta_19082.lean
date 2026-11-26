import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19082_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.and, [8, 0]⟩,
    ⟨GateOp.and, [5, 1]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [11, 12]⟩
    ]
    output := 13 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 6 := by decide

theorem C_rep : Represents (fun u v : Fin 4 => (295 : ℕ).testBit (4 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_19082_aux

theorem PEqualNP.Outside.L_meta_19082 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (295 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19082_aux.C, PEqualNP.Outside.L_meta_19082_aux.C_fanInTwo, PEqualNP.Outside.L_meta_19082_aux.C_size, PEqualNP.Outside.L_meta_19082_aux.C_rep⟩
