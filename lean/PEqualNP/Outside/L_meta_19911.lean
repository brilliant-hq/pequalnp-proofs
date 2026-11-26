import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19911

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.or, [12, 15]⟩,
      ⟨GateOp.or, [11, 18]⟩,
      ⟨GateOp.and, [0, 19]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.and, [1, 21]⟩,
      ⟨GateOp.or, [14, 17]⟩,
      ⟨GateOp.and, [2, 23]⟩,
      ⟨GateOp.or, [14, 18]⟩,
      ⟨GateOp.and, [3, 25]⟩,
      ⟨GateOp.or, [11, 16]⟩,
      ⟨GateOp.and, [4, 27]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [29, 15]⟩,
      ⟨GateOp.and, [5, 30]⟩,
      ⟨GateOp.or, [11, 17]⟩,
      ⟨GateOp.and, [6, 32]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [34, 13]⟩,
      ⟨GateOp.and, [7, 35]⟩,
      ⟨GateOp.or, [20, 22]⟩,
      ⟨GateOp.or, [37, 24]⟩,
      ⟨GateOp.or, [38, 26]⟩,
      ⟨GateOp.or, [39, 28]⟩,
      ⟨GateOp.or, [40, 31]⟩,
      ⟨GateOp.or, [41, 33]⟩,
      ⟨GateOp.or, [42, 36]⟩
    ],
    output := 43 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (3751079755257373080 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19911

theorem PEqualNP.Outside.L_meta_19911 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3751079755257373080 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19911.ckt, PEqualNP.Outside.L_meta_19911.mono, by decide, PEqualNP.Outside.L_meta_19911.rep⟩
