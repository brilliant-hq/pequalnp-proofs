import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20185

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [2, 14]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [22, 19]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [24, 20]⟩, ⟨GateOp.or, [4, 15]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [27, 18]⟩, ⟨GateOp.or, [19, 20]⟩, ⟨GateOp.or, [5, 17]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [31, 16]⟩, ⟨GateOp.and, [21, 23]⟩, ⟨GateOp.and, [25, 26]⟩, ⟨GateOp.and, [28, 29]⟩, ⟨GateOp.and, [30, 32]⟩, ⟨GateOp.or, [33, 34]⟩, ⟨GateOp.or, [37, 35]⟩, ⟨GateOp.or, [38, 36]⟩], 39⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20185

theorem PEqualNP.Outside.L_meta_20185 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 24) :=
  PEqualNP.Outside.L_meta_20185.main_aux
