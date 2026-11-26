import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19781

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit := ⟨[
  ⟨GateOp.or, [8, 9]⟩,
  ⟨GateOp.or, [11, 12]⟩,
  ⟨GateOp.or, [17, 16]⟩,
  ⟨GateOp.or, [10, 13]⟩,
  ⟨GateOp.or, [16, 19]⟩,
  ⟨GateOp.or, [14, 17]⟩,
  ⟨GateOp.or, [8, 21]⟩,
  ⟨GateOp.or, [13, 21]⟩,
  ⟨GateOp.or, [9, 15]⟩,
  ⟨GateOp.or, [10, 24]⟩,
  ⟨GateOp.or, [11, 25]⟩,
  ⟨GateOp.or, [12, 24]⟩,
  ⟨GateOp.or, [15, 19]⟩,
  ⟨GateOp.or, [8, 28]⟩,
  ⟨GateOp.or, [14, 27]⟩,
  ⟨GateOp.or, [14, 28]⟩,
  ⟨GateOp.and, [0, 23]⟩,
  ⟨GateOp.and, [1, 26]⟩,
  ⟨GateOp.and, [2, 29]⟩,
  ⟨GateOp.and, [3, 18]⟩,
  ⟨GateOp.and, [4, 20]⟩,
  ⟨GateOp.and, [5, 22]⟩,
  ⟨GateOp.and, [6, 30]⟩,
  ⟨GateOp.and, [7, 31]⟩,
  ⟨GateOp.or, [32, 33]⟩,
  ⟨GateOp.or, [34, 35]⟩,
  ⟨GateOp.or, [36, 37]⟩,
  ⟨GateOp.or, [38, 39]⟩,
  ⟨GateOp.or, [40, 41]⟩,
  ⟨GateOp.or, [42, 43]⟩,
  ⟨GateOp.or, [44, 45]⟩
], 46⟩

theorem mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeC : C.size ≤ 31 := by decide

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19781

theorem PEqualNP.Outside.L_meta_19781 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 31) :=
  ⟨PEqualNP.Outside.L_meta_19781.C, PEqualNP.Outside.L_meta_19781.mono, PEqualNP.Outside.L_meta_19781.sizeC, PEqualNP.Outside.L_meta_19781.rep⟩
