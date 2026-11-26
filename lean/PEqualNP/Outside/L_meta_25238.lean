import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25238_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25238_aux

theorem PEqualNP.Outside.L_meta_25238 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50331 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25238_aux.wit, PEqualNP.Outside.L_meta_25238_aux.wit_p, by decide, by decide +kernel⟩
