import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19398

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def A : Fin 5 → Fin 5 → Bool := fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [4, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.or, inputs := [3, 11] }, { op := GateOp.or, inputs := [7, 11] }, { op := GateOp.or, inputs := [12, 13] }, { op := GateOp.or, inputs := [2, 12] }, { op := GateOp.or, inputs := [4, 9] }, { op := GateOp.or, inputs := [8, 16] }, { op := GateOp.and, inputs := [14, 18] }, { op := GateOp.and, inputs := [15, 17] }, { op := GateOp.or, inputs := [19, 20] }],
    output := 21 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_19398

theorem PEqualNP.Outside.L_meta_19398 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_19398.upperC, PEqualNP.Outside.L_meta_19398.upper_mono, by decide, PEqualNP.Outside.L_meta_19398.upper_rep⟩
