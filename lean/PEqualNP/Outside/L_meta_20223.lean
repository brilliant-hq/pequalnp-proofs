import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20223 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [15, 18]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [1, 15]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.or, [17, 22]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [21, 24]⟩, ⟨GateOp.or, [11, 2]⟩, ⟨GateOp.or, [7, 28]⟩, ⟨GateOp.or, [24, 20]⟩, ⟨GateOp.or, [14, 29]⟩, ⟨GateOp.and, [14, 29]⟩, ⟨GateOp.or, [18, 28]⟩, ⟨GateOp.or, [26, 21]⟩, ⟨GateOp.or, [17, 4]⟩, ⟨GateOp.and, [23, 27]⟩, ⟨GateOp.and, [34, 33]⟩, ⟨GateOp.and, [25, 30]⟩, ⟨GateOp.or, [36, 32]⟩, ⟨GateOp.and, [35, 31]⟩, ⟨GateOp.or, [37, 38]⟩, ⟨GateOp.or, [41, 39]⟩, ⟨GateOp.or, [40, 42]⟩], 43⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · unfold Represents
    decide
