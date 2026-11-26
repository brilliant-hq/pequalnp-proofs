import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20497

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.and, [8, 9]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.and, [12, 13]⟩
    ],
    output := 14 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (3238 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_20497

theorem PEqualNP.Outside.L_meta_20497 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3238 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_20497.ckt, PEqualNP.Outside.L_meta_20497.mono, by decide, PEqualNP.Outside.L_meta_20497.rep⟩
