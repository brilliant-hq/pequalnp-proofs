import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19546
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [14, 21]⟩, ⟨GateOp.and, [14, 21]⟩, ⟨GateOp.or, [24, 22]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [17, 18]⟩, ⟨GateOp.or, [19, 20]⟩, ⟨GateOp.and, [19, 20]⟩, ⟨GateOp.or, [26, 28]⟩, ⟨GateOp.and, [26, 28]⟩, ⟨GateOp.or, [31, 27]⟩, ⟨GateOp.or, [32, 29]⟩, ⟨GateOp.and, [23, 30]⟩, ⟨GateOp.or, [34, 25]⟩, ⟨GateOp.or, [35, 33]⟩], 36⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun u v : Fin 7 => decide (u ≠ v)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_19546

theorem PEqualNP.Outside.L_meta_19546 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 23 := by
  exact ⟨PEqualNP.Outside.L_meta_19546.circ, PEqualNP.Outside.L_meta_19546.mono, by decide, PEqualNP.Outside.L_meta_19546.rep⟩
