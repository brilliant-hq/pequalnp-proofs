import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20203

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 14]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [5, 22]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [13, 19]⟩, ⟨GateOp.or, [27, 23]⟩, ⟨GateOp.or, [20, 21]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.or, [30, 18]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.or, [32, 20]⟩, ⟨GateOp.or, [21, 22]⟩, ⟨GateOp.or, [34, 23]⟩, ⟨GateOp.and, [24, 25]⟩, ⟨GateOp.and, [26, 28]⟩, ⟨GateOp.and, [29, 31]⟩, ⟨GateOp.and, [33, 35]⟩, ⟨GateOp.or, [36, 37]⟩, ⟨GateOp.or, [40, 38]⟩, ⟨GateOp.or, [41, 39]⟩], 42⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14348455746820602255 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20203

theorem PEqualNP.Outside.L_meta_20203 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14348455746820602255 : ℕ).testBit (8 * u.val + v.val)) 27) :=
  PEqualNP.Outside.L_meta_20203.main_aux
