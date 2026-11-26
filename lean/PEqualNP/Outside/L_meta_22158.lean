import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22158

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [6, 12]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.and, [14, 5]⟩,
      ⟨GateOp.and, [15, 0]⟩,
      ⟨GateOp.or, [4, 18]⟩,
      ⟨GateOp.or, [19, 13]⟩,
      ⟨GateOp.or, [20, 17]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840693 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22158

theorem PEqualNP.Outside.L_meta_22158 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840693 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22158.ckt, PEqualNP.Outside.L_meta_22158.mono, by decide, PEqualNP.Outside.L_meta_22158.rep⟩
