import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19314

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7712116 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_19314

theorem PEqualNP.Outside.L_meta_19314 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7712116 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19314.circ, PEqualNP.Outside.L_meta_19314.fanin, by decide, PEqualNP.Outside.L_meta_19314.rep⟩
