import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.or, [11, 5]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [9, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_22592_aux

theorem PEqualNP.Outside.L_meta_22592 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (3900 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22592_aux.wit, PEqualNP.Outside.L_meta_22592_aux.wit_p, by decide, by decide +kernel⟩
