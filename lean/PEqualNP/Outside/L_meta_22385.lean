import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22385

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [6, 0]⟩,
      ⟨GateOp.or, [7, 1]⟩,
      ⟨GateOp.or, [4, 11]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.and, [3, 13]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.or, [15, 9]⟩,
      ⟨GateOp.or, [12, 10]⟩,
      ⟨GateOp.or, [7, 2]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.and, [16, 17]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.or, [19, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843064 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22385

theorem PEqualNP.Outside.L_meta_22385 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843064 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22385.ckt, PEqualNP.Outside.L_meta_22385.mono, by decide, PEqualNP.Outside.L_meta_22385.rep⟩
