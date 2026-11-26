import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20223

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 15]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [20, 8]⟩, ⟨GateOp.or, [21, 14]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [23, 17]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [25, 18]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [27, 19]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [30, 16]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [32, 8]⟩, ⟨GateOp.or, [33, 18]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [35, 16]⟩, ⟨GateOp.and, [22, 24]⟩, ⟨GateOp.and, [26, 28]⟩, ⟨GateOp.and, [29, 31]⟩, ⟨GateOp.and, [34, 36]⟩, ⟨GateOp.or, [37, 38]⟩, ⟨GateOp.or, [41, 39]⟩, ⟨GateOp.or, [42, 40]⟩], 43⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_20223

theorem PEqualNP.Outside.L_meta_20223 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7184026854491237685 : ℕ).testBit (8 * u.val + v.val)) 28) :=
  PEqualNP.Outside.L_meta_20223.main_aux
