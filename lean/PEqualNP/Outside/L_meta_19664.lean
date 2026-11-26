import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19664_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.and, [5, 1]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [9, 4]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [13, 7]⟩,
    ⟨GateOp.or, [10, 13]⟩,
    ⟨GateOp.or, [11, 16]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.and, [17, 18]⟩
    ]
    output := 19 }

theorem C_ok : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 10 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun u v : Fin 5 => (16269874 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19664_aux

theorem PEqualNP.Outside.L_meta_19664 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269874 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19664_aux.C, PEqualNP.Outside.L_meta_19664_aux.C_ok, PEqualNP.Outside.L_meta_19664_aux.C_size, PEqualNP.Outside.L_meta_19664_aux.C_rep⟩
