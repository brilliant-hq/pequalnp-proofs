import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21569_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.not, [9]⟩], 10⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21569_aux

theorem PEqualNP.Outside.L_meta_21569 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275167 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21569_aux.wit, PEqualNP.Outside.L_meta_21569_aux.wit_p, by decide, by decide +kernel⟩
