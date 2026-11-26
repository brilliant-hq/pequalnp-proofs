import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20421

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [5, 1]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.and, [4, 2]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.or, [10, 0]⟩
    ],
    output := 11 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 3) (v : Fin 4) => (863 : ℕ).testBit (4 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_20421

theorem PEqualNP.Outside.L_meta_20421 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (863 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_20421.ckt, PEqualNP.Outside.L_meta_20421.mono, by decide, PEqualNP.Outside.L_meta_20421.rep⟩
