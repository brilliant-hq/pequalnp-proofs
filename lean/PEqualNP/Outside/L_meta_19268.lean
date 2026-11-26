import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19268_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.and, [10, 9]⟩
    ]
    output := 11 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 4 := by decide +kernel

theorem C_rep : Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19268_aux

theorem PEqualNP.Outside.L_meta_19268 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19268_aux.C, PEqualNP.Outside.L_meta_19268_aux.C_fanInTwo, PEqualNP.Outside.L_meta_19268_aux.C_size, PEqualNP.Outside.L_meta_19268_aux.C_rep⟩
