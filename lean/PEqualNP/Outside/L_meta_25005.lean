import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25005

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨GateOp.or, [3, 15]⟩, ⟨GateOp.or, [8, 16]⟩, ⟨GateOp.or, [17, 6]⟩, ⟨GateOp.or, [2, 14]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.or, [19, 20]⟩, ⟨GateOp.and, [18, 21]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.or, [6, 24]⟩, ⟨GateOp.or, [25, 10]⟩, ⟨GateOp.or, [23, 26]⟩, ⟨GateOp.or, [27, 16]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.and, [28, 29]⟩, ⟨GateOp.or, [22, 30]⟩, ⟨GateOp.or, [20, 10]⟩, ⟨GateOp.or, [32, 0]⟩, ⟨GateOp.or, [8, 25]⟩, ⟨GateOp.or, [19, 34]⟩, ⟨GateOp.and, [33, 35]⟩, ⟨GateOp.or, [31, 36]⟩, ⟨GateOp.or, [0, 24]⟩, ⟨GateOp.or, [38, 17]⟩, ⟨GateOp.and, [23, 39]⟩, ⟨GateOp.or, [37, 40]⟩], 41⟩

theorem shape : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25005

theorem PEqualNP.Outside.L_meta_25005 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 26) := by
  refine ⟨PEqualNP.Outside.L_meta_25005.circuit, PEqualNP.Outside.L_meta_25005.shape, ?_, ?_⟩
  · decide
  · decide +kernel
