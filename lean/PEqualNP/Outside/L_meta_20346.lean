import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20346

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 14]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [21, 10]⟩, ⟨GateOp.or, [22, 20]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [4, 17]⟩, ⟨GateOp.or, [8, 16]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [27, 17]⟩, ⟨GateOp.or, [28, 19]⟩, ⟨GateOp.or, [0, 18]⟩, ⟨GateOp.or, [30, 20]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [32, 10]⟩, ⟨GateOp.or, [4, 18]⟩, ⟨GateOp.and, [23, 24]⟩, ⟨GateOp.and, [25, 26]⟩, ⟨GateOp.and, [29, 31]⟩, ⟨GateOp.and, [33, 34]⟩, ⟨GateOp.or, [35, 36]⟩, ⟨GateOp.or, [39, 37]⟩, ⟨GateOp.or, [40, 38]⟩], 41⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8280023251922031930 : ℕ).testBit (8 * u.val + v.val)) 26 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20346

theorem PEqualNP.Outside.L_meta_20346 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8280023251922031930 : ℕ).testBit (8 * u.val + v.val)) 26) :=
  PEqualNP.Outside.L_meta_20346.main_aux
