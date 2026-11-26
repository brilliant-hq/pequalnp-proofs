import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18534

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.and, [13, 17]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [20, 19]⟩], 21⟩

theorem mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_18534

open PEqualNP.Outside.L_meta_18534 in
theorem PEqualNP.Outside.L_meta_18534 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) 12) := by
  exact ⟨C, mono, by decide, rep⟩
