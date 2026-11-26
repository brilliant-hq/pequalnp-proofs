import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24171

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit := ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [5, 14]⟩], 15⟩

theorem ok : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sz : C.size ≤ 11 := by
  simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]

theorem ev : ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283354 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24171

theorem PEqualNP.Outside.L_meta_24171 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283354 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24171.C, PEqualNP.Outside.L_meta_24171.ok, PEqualNP.Outside.L_meta_24171.sz, PEqualNP.Outside.L_meta_24171.ev⟩
