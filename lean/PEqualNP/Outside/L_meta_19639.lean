import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19639

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.not, [1]⟩,
    ⟨GateOp.and, [10, 14]⟩,
    ⟨GateOp.not, [13]⟩,
    ⟨GateOp.or, [12, 15]⟩,
    ⟨GateOp.or, [9, 16]⟩,
    ⟨GateOp.and, [17, 18]⟩], 19⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem represents :
    PEqualNP.Represents.Represents (fun u v : Fin 5 => (3260509 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19639

theorem PEqualNP.Outside.L_meta_19639 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3260509 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19639.circ, PEqualNP.Outside.L_meta_19639.fanin, by decide,
    PEqualNP.Outside.L_meta_19639.represents⟩
