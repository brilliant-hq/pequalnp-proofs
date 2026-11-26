import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19919

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [18, 12]⟩,
      ⟨GateOp.and, [0, 19]⟩,
      ⟨GateOp.or, [14, 17]⟩,
      ⟨GateOp.and, [1, 21]⟩,
      ⟨GateOp.or, [11, 16]⟩,
      ⟨GateOp.and, [2, 23]⟩,
      ⟨GateOp.or, [11, 17]⟩,
      ⟨GateOp.and, [3, 25]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [27, 12]⟩,
      ⟨GateOp.and, [4, 28]⟩,
      ⟨GateOp.or, [9, 16]⟩,
      ⟨GateOp.and, [5, 30]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [32, 15]⟩,
      ⟨GateOp.and, [6, 33]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [35, 14]⟩,
      ⟨GateOp.and, [7, 36]⟩,
      ⟨GateOp.or, [20, 22]⟩,
      ⟨GateOp.or, [38, 24]⟩,
      ⟨GateOp.or, [39, 26]⟩,
      ⟨GateOp.or, [40, 29]⟩,
      ⟨GateOp.or, [41, 31]⟩,
      ⟨GateOp.or, [42, 34]⟩,
      ⟨GateOp.or, [43, 37]⟩
    ],
    output := 44 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (8125095274657465365 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19919

theorem PEqualNP.Outside.L_meta_19919 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8125095274657465365 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_meta_19919.ckt, PEqualNP.Outside.L_meta_19919.mono, by decide, PEqualNP.Outside.L_meta_19919.rep⟩
