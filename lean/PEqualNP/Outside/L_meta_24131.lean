import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24131_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24131_aux

theorem PEqualNP.Outside.L_meta_24131 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275094 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24131_aux.wit, PEqualNP.Outside.L_meta_24131_aux.wit_p, by decide, by decide +kernel⟩
