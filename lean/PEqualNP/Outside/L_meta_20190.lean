import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20190

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 15]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.or, [20, 17]⟩, ⟨GateOp.or, [21, 19]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [25, 16]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [27, 18]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [29, 19]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.or, [32, 18]⟩, ⟨GateOp.and, [22, 23]⟩, ⟨GateOp.and, [24, 26]⟩, ⟨GateOp.and, [28, 30]⟩, ⟨GateOp.and, [31, 33]⟩, ⟨GateOp.or, [34, 35]⟩, ⟨GateOp.or, [38, 36]⟩, ⟨GateOp.or, [39, 37]⟩], 40⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6355890012357600705 : ℕ).testBit (8 * u.val + v.val)) 25 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20190

theorem PEqualNP.Outside.L_meta_20190 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6355890012357600705 : ℕ).testBit (8 * u.val + v.val)) 25) :=
  PEqualNP.Outside.L_meta_20190.main_aux
