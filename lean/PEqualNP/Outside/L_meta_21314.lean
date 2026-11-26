import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21314

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [5, 9]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [1, 9]⟩,
      ⟨GateOp.or, [6, 13]⟩,
      ⟨GateOp.or, [5, 7]⟩,
      ⟨GateOp.or, [2, 15]⟩,
      ⟨GateOp.and, [14, 16]⟩,
      ⟨GateOp.and, [12, 10]⟩,
      ⟨GateOp.or, [17, 18]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (103802 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21314

theorem PEqualNP.Outside.L_meta_21314 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103802 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21314.ckt, PEqualNP.Outside.L_meta_21314.mono, by decide, PEqualNP.Outside.L_meta_21314.rep⟩
