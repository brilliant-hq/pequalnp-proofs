import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24094_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [9, 12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24094_aux

theorem PEqualNP.Outside.L_meta_24094 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807511 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24094_aux.wit, PEqualNP.Outside.L_meta_24094_aux.wit_p, by decide, by decide +kernel⟩
