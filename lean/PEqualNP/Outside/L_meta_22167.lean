import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22167

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 7]⟩,
      ⟨GateOp.or, [6, 0]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [12, 9]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [3, 10]⟩,
      ⟨GateOp.and, [14, 15]⟩,
      ⟨GateOp.and, [5, 3]⟩,
      ⟨GateOp.or, [11, 16]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.and, [19, 18]⟩,
      ⟨GateOp.or, [4, 20]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841195 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22167

theorem PEqualNP.Outside.L_meta_22167 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841195 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22167.ckt, PEqualNP.Outside.L_meta_22167.mono, by decide, PEqualNP.Outside.L_meta_22167.rep⟩
