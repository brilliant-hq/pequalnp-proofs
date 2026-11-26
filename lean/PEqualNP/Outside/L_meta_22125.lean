import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22125

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [9, 2]⟩,
      ⟨GateOp.or, [7, 6]⟩,
      ⟨GateOp.and, [3, 10]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [12, 0]⟩,
      ⟨GateOp.or, [6, 14]⟩,
      ⟨GateOp.and, [1, 16]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.and, [18, 19]⟩,
      ⟨GateOp.or, [20, 17]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (837107 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22125

theorem PEqualNP.Outside.L_meta_22125 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837107 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22125.ckt, PEqualNP.Outside.L_meta_22125.mono, by decide, PEqualNP.Outside.L_meta_22125.rep⟩
