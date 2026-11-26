import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20381

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 12]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [3, 15]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [22, 21]⟩, ⟨GateOp.or, [11, 19]⟩, ⟨GateOp.or, [24, 21]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [27, 17]⟩, ⟨GateOp.or, [5, 14]⟩, ⟨GateOp.or, [29, 18]⟩, ⟨GateOp.or, [30, 20]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [32, 20]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [34, 17]⟩, ⟨GateOp.or, [35, 18]⟩, ⟨GateOp.and, [19, 23]⟩, ⟨GateOp.and, [25, 26]⟩, ⟨GateOp.and, [28, 31]⟩, ⟨GateOp.and, [33, 36]⟩, ⟨GateOp.or, [37, 38]⟩, ⟨GateOp.or, [41, 39]⟩, ⟨GateOp.or, [42, 40]⟩], 43⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20381

theorem PEqualNP.Outside.L_meta_20381 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  PEqualNP.Outside.L_meta_20381.main_aux
