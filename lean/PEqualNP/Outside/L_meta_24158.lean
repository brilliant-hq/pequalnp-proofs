import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24158_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24158_aux

theorem PEqualNP.Outside.L_meta_24158 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266326 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24158_aux.wit, PEqualNP.Outside.L_meta_24158_aux.wit_p, by decide, by decide +kernel⟩
