import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20077

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.or, [1, 17]⟩, ⟨GateOp.or, [18, 16]⟩, ⟨GateOp.or, [16, 10]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [7, 21]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [24, 22]⟩, ⟨GateOp.or, [9, 19]⟩, ⟨GateOp.and, [26, 24]⟩, ⟨GateOp.or, [27, 11]⟩, ⟨GateOp.and, [1, 15]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.or, [7, 28]⟩, ⟨GateOp.or, [3, 26]⟩, ⟨GateOp.or, [17, 23]⟩, ⟨GateOp.and, [31, 32]⟩, ⟨GateOp.and, [2, 32]⟩, ⟨GateOp.and, [30, 33]⟩, ⟨GateOp.or, [22, 10]⟩, ⟨GateOp.or, [34, 36]⟩, ⟨GateOp.or, [25, 20]⟩, ⟨GateOp.and, [39, 37]⟩, ⟨GateOp.or, [40, 38]⟩, ⟨GateOp.or, [41, 29]⟩], 42⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7107882128747567250 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20077

theorem PEqualNP.Outside.L_meta_20077 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7107882128747567250 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20077.main_aux
