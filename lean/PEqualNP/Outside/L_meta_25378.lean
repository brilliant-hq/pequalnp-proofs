import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25378_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [8, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25378_aux

theorem PEqualNP.Outside.L_meta_25378 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374551 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25378_aux.wit, PEqualNP.Outside.L_meta_25378_aux.wit_p, by decide, by decide +kernel⟩
