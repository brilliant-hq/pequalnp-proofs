import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24136_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24136_aux

theorem PEqualNP.Outside.L_meta_24136 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24136_aux.wit, PEqualNP.Outside.L_meta_24136_aux.wit_p, by decide, by decide +kernel⟩
