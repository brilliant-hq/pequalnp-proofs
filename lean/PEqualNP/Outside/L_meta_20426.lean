import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20426

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [5, 8]⟩,
      ⟨GateOp.and, [7, 9]⟩,
      ⟨GateOp.or, [3, 10]⟩,
      ⟨GateOp.or, [0, 11]⟩
    ],
    output := 12 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (991 : ℕ).testBit (4 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_20426

theorem PEqualNP.Outside.L_meta_20426 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (991 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_20426.ckt, PEqualNP.Outside.L_meta_20426.mono, by decide, PEqualNP.Outside.L_meta_20426.rep⟩
