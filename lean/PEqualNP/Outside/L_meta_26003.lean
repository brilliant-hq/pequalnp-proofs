import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26003_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 2] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 4] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }
    ],
    output := 14 }

end PEqualNP.Outside.L_meta_26003_aux

theorem PEqualNP.Outside.L_meta_26003 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 14, 7, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨PEqualNP.Outside.L_meta_26003_aux.witness, ?_, by decide, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_26003_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
