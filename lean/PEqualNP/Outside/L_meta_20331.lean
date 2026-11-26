import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20331

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [8, 16]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [4, 17]⟩, ⟨GateOp.or, [11, 18]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.or, [4, 20]⟩, ⟨GateOp.or, [0, 22]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [26, 19]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [11, 19]⟩, ⟨GateOp.or, [29, 21]⟩, ⟨GateOp.or, [2, 15]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [5, 17]⟩, ⟨GateOp.or, [33, 20]⟩, ⟨GateOp.or, [34, 22]⟩, ⟨GateOp.and, [23, 24]⟩, ⟨GateOp.and, [21, 25]⟩, ⟨GateOp.and, [27, 28]⟩, ⟨GateOp.and, [30, 31]⟩, ⟨GateOp.and, [32, 35]⟩, ⟨GateOp.or, [36, 37]⟩, ⟨GateOp.or, [41, 38]⟩, ⟨GateOp.or, [42, 39]⟩, ⟨GateOp.or, [43, 40]⟩], 44⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5146091177712921810 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20331

theorem PEqualNP.Outside.L_meta_20331 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5146091177712921810 : ℕ).testBit (8 * u.val + v.val)) 29) :=
  PEqualNP.Outside.L_meta_20331.main_aux
