import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22189

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.or, [12, 7]⟩,
      ⟨GateOp.or, [13, 8]⟩,
      ⟨GateOp.and, [4, 10]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.and, [11, 16]⟩,
      ⟨GateOp.or, [0, 17]⟩,
      ⟨GateOp.and, [14, 10]⟩,
      ⟨GateOp.or, [19, 18]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841663 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22189

theorem PEqualNP.Outside.L_meta_22189 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841663 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_22189.ckt, PEqualNP.Outside.L_meta_22189.mono, by decide, PEqualNP.Outside.L_meta_22189.rep⟩
