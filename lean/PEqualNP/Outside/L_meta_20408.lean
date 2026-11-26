import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20408

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.and, [4, 8]⟩,
      ⟨GateOp.or, [7, 9]⟩
    ],
    output := 10 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (319 : ℕ).testBit (4 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_20408

theorem PEqualNP.Outside.L_meta_20408 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (319 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨PEqualNP.Outside.L_meta_20408.ckt, PEqualNP.Outside.L_meta_20408.mono, by decide, PEqualNP.Outside.L_meta_20408.rep⟩
