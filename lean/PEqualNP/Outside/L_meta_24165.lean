import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24165_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [9, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24165_aux

theorem PEqualNP.Outside.L_meta_24165 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24165_aux.wit, PEqualNP.Outside.L_meta_24165_aux.wit_p, by decide, by decide +kernel⟩
