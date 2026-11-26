import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24185

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [5, 13]⟩], 14⟩

theorem ok : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sz : C.size ≤ 13 := by
  simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]

theorem ev : ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266770 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24185

theorem PEqualNP.Outside.L_meta_24185 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266770 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24185.C, PEqualNP.Outside.L_meta_24185.ok, PEqualNP.Outside.L_meta_24185.sz, PEqualNP.Outside.L_meta_24185.ev⟩
