import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19045

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit := ⟨[⟨GateOp.or, [3, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.and, [11, 9]⟩, ⟨GateOp.or, [13, 10]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [12, 15]⟩], 16⟩

theorem gatesOK : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : C.size ≤ 9 := by decide

set_option maxRecDepth 20000 in
theorem repOK : PEqualNP.Represents.Represents (fun u v : Fin 4 => (5822 : ℕ).testBit (4 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19045

theorem PEqualNP.Outside.L_meta_19045 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5822 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19045.C, PEqualNP.Outside.L_meta_19045.gatesOK, PEqualNP.Outside.L_meta_19045.sizeOK, PEqualNP.Outside.L_meta_19045.repOK⟩
