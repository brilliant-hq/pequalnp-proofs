import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25009

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [4, 14]⟩,
      ⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.or, [6, 9]⟩,
      ⟨GateOp.or, [1, 12]⟩,
      ⟨GateOp.or, [3, 10]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.or, [18, 22]⟩,
      ⟨GateOp.or, [2, 13]⟩,
      ⟨GateOp.or, [24, 17]⟩,
      ⟨GateOp.or, [19, 21]⟩,
      ⟨GateOp.or, [7, 15]⟩,
      ⟨GateOp.or, [27, 16]⟩,
      ⟨GateOp.or, [28, 17]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.or, [21, 22]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [33, 15]⟩,
      ⟨GateOp.and, [23, 25]⟩,
      ⟨GateOp.and, [26, 29]⟩,
      ⟨GateOp.and, [30, 31]⟩,
      ⟨GateOp.and, [1, 15]⟩,
      ⟨GateOp.and, [32, 34]⟩,
      ⟨GateOp.or, [35, 36]⟩,
      ⟨GateOp.or, [40, 37]⟩,
      ⟨GateOp.or, [41, 38]⟩,
      ⟨GateOp.or, [42, 39]⟩
    ],
    output := 43 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_25009

theorem PEqualNP.Outside.L_meta_25009 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_25009.ckt, PEqualNP.Outside.L_meta_25009.mono, by decide, PEqualNP.Outside.L_meta_25009.rep⟩
