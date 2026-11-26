import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22853

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cm : Circuit := ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.and, [1, 15]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.or, [17, 4]⟩, ⟨GateOp.and, [2, 18]⟩, ⟨GateOp.and, [3, 14]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.or, [19, 20]⟩, ⟨GateOp.or, [21, 22]⟩], 23⟩

theorem cm_mono : Monotone2 cm := by
  intro g hg
  simp only [cm, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem cm_size : cm.size ≤ 15 := by decide

theorem cm_rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (908284 : ℕ).testBit (6 * u.val + v.val)) cm := by
  decide +kernel

end PEqualNP.Outside.L_meta_22853

theorem PEqualNP.Outside.L_meta_22853 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908284 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨PEqualNP.Outside.L_meta_22853.cm, PEqualNP.Outside.L_meta_22853.cm_mono, PEqualNP.Outside.L_meta_22853.cm_size, PEqualNP.Outside.L_meta_22853.cm_rep⟩
