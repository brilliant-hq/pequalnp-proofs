import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20415

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.or, [9, 10]⟩
    ],
    output := 11 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (383 : ℕ).testBit (4 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_20415

theorem PEqualNP.Outside.L_meta_20415 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (383 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_20415.ckt, PEqualNP.Outside.L_meta_20415.mono, by decide, PEqualNP.Outside.L_meta_20415.rep⟩
