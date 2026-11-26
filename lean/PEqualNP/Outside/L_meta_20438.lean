import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20438
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [11, 17]⟩], 18⟩

theorem shape : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : Represents (fun u v : Fin 5 => (16269393 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_20438

theorem PEqualNP.Outside.L_meta_20438 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269393 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_20438.circ, PEqualNP.Outside.L_meta_20438.shape, by decide, PEqualNP.Outside.L_meta_20438.right⟩
