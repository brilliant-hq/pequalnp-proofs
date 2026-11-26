import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22251

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 2]⟩,
      ⟨GateOp.and, [11, 6]⟩,
      ⟨GateOp.or, [12, 4]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.or, [14, 5]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.and, [16, 0]⟩,
      ⟨GateOp.or, [17, 2]⟩,
      ⟨GateOp.or, [18, 3]⟩,
      ⟨GateOp.or, [19, 7]⟩,
      ⟨GateOp.or, [20, 8]⟩,
      ⟨GateOp.and, [21, 15]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816701 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22251

theorem PEqualNP.Outside.L_meta_22251 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816701 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22251.ckt, PEqualNP.Outside.L_meta_22251.mono, by decide, PEqualNP.Outside.L_meta_22251.rep⟩
