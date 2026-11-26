import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20186

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [21, 13]⟩, ⟨GateOp.or, [22, 17]⟩, ⟨GateOp.or, [3, 15]⟩, ⟨GateOp.or, [24, 18]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [26, 19]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.or, [28, 18]⟩, ⟨GateOp.or, [3, 19]⟩, ⟨GateOp.or, [30, 20]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [33, 20]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.and, [23, 25]⟩, ⟨GateOp.and, [27, 29]⟩, ⟨GateOp.and, [31, 32]⟩, ⟨GateOp.and, [34, 35]⟩, ⟨GateOp.or, [36, 37]⟩, ⟨GateOp.or, [40, 38]⟩, ⟨GateOp.or, [41, 39]⟩], 42⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20186

theorem PEqualNP.Outside.L_meta_20186 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  PEqualNP.Outside.L_meta_20186.main_aux
