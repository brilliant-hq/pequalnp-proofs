import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21474_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21474_aux

theorem PEqualNP.Outside.L_meta_21474 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9118 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21474_aux.wit, PEqualNP.Outside.L_meta_21474_aux.wit_mono, by decide, by decide +kernel⟩
