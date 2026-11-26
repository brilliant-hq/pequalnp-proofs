import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25381_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25381_aux

theorem PEqualNP.Outside.L_meta_25381 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375325 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25381_aux.wit, PEqualNP.Outside.L_meta_25381_aux.wit_p, by decide, by decide +kernel⟩
