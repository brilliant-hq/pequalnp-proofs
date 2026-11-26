import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19797

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [8, 14]⟩,
      ⟨GateOp.or, [11, 15]⟩,
      ⟨GateOp.or, [11, 16]⟩,
      ⟨GateOp.or, [14, 19]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [16, 21]⟩,
      ⟨GateOp.and, [0, 23]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [25, 13]⟩,
      ⟨GateOp.or, [26, 19]⟩,
      ⟨GateOp.and, [1, 27]⟩,
      ⟨GateOp.or, [9, 22]⟩,
      ⟨GateOp.and, [2, 29]⟩,
      ⟨GateOp.or, [18, 20]⟩,
      ⟨GateOp.and, [3, 31]⟩,
      ⟨GateOp.or, [17, 21]⟩,
      ⟨GateOp.and, [4, 33]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [35, 15]⟩,
      ⟨GateOp.or, [36, 16]⟩,
      ⟨GateOp.and, [5, 37]⟩,
      ⟨GateOp.or, [17, 20]⟩,
      ⟨GateOp.and, [6, 39]⟩,
      ⟨GateOp.or, [15, 22]⟩,
      ⟨GateOp.and, [7, 41]⟩,
      ⟨GateOp.or, [24, 28]⟩,
      ⟨GateOp.or, [43, 30]⟩,
      ⟨GateOp.or, [44, 32]⟩,
      ⟨GateOp.or, [45, 34]⟩,
      ⟨GateOp.or, [46, 38]⟩,
      ⟨GateOp.or, [47, 40]⟩,
      ⟨GateOp.or, [48, 42]⟩
    ],
    output := 49 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (15365916737909796330 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19797

theorem PEqualNP.Outside.L_meta_19797 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15365916737909796330 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19797.ckt, PEqualNP.Outside.L_meta_19797.mono, by decide, PEqualNP.Outside.L_meta_19797.rep⟩
