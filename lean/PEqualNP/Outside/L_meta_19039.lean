import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19039

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit := ⟨[⟨GateOp.or, [7, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [8, 0]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [13, 15]⟩], 16⟩

theorem gatesOK : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : C.size ≤ 9 := by decide

set_option maxRecDepth 20000 in
theorem repOK : PEqualNP.Represents.Represents (fun u v : Fin 4 => (4732 : ℕ).testBit (4 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19039

theorem PEqualNP.Outside.L_meta_19039 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4732 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19039.C, PEqualNP.Outside.L_meta_19039.gatesOK, PEqualNP.Outside.L_meta_19039.sizeOK, PEqualNP.Outside.L_meta_19039.repOK⟩
