import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22593_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [11, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.not, [13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_22593_aux

theorem PEqualNP.Outside.L_meta_22593 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16543 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22593_aux.wit, PEqualNP.Outside.L_meta_22593_aux.wit_p, by decide, by decide +kernel⟩
