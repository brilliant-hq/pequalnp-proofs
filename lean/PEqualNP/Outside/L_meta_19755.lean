import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19755

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 15]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [10, 14]⟩,
      ⟨GateOp.or, [10, 17]⟩,
      ⟨GateOp.or, [11, 19]⟩,
      ⟨GateOp.or, [9, 16]⟩,
      ⟨GateOp.or, [22, 19]⟩,
      ⟨GateOp.and, [0, 23]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.and, [1, 25]⟩,
      ⟨GateOp.or, [13, 16]⟩,
      ⟨GateOp.or, [27, 18]⟩,
      ⟨GateOp.and, [2, 28]⟩,
      ⟨GateOp.or, [18, 20]⟩,
      ⟨GateOp.and, [3, 30]⟩,
      ⟨GateOp.or, [17, 21]⟩,
      ⟨GateOp.and, [4, 32]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [34, 14]⟩,
      ⟨GateOp.or, [35, 17]⟩,
      ⟨GateOp.and, [5, 36]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.or, [38, 15]⟩,
      ⟨GateOp.or, [39, 18]⟩,
      ⟨GateOp.and, [6, 40]⟩,
      ⟨GateOp.or, [16, 21]⟩,
      ⟨GateOp.and, [7, 42]⟩,
      ⟨GateOp.or, [24, 26]⟩,
      ⟨GateOp.or, [44, 29]⟩,
      ⟨GateOp.or, [45, 31]⟩,
      ⟨GateOp.or, [46, 33]⟩,
      ⟨GateOp.or, [47, 37]⟩,
      ⟨GateOp.or, [48, 41]⟩,
      ⟨GateOp.or, [49, 43]⟩
    ],
    output := 50 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19755

theorem PEqualNP.Outside.L_meta_19755 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_meta_19755.ckt, PEqualNP.Outside.L_meta_19755.mono, by decide, PEqualNP.Outside.L_meta_19755.rep⟩
