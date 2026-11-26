import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22206

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.or, [11, 5]⟩,
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [14, 7]⟩,
      ⟨GateOp.or, [15, 4]⟩,
      ⟨GateOp.and, [16, 13]⟩,
      ⟨GateOp.or, [15, 8]⟩,
      ⟨GateOp.or, [18, 9]⟩,
      ⟨GateOp.and, [19, 12]⟩,
      ⟨GateOp.or, [20, 17]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843581 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22206

theorem PEqualNP.Outside.L_meta_22206 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843581 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22206.ckt, PEqualNP.Outside.L_meta_22206.mono, by decide, PEqualNP.Outside.L_meta_22206.rep⟩
