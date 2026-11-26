import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25262_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25262_aux

theorem PEqualNP.Outside.L_meta_25262 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50871 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25262_aux.wit, PEqualNP.Outside.L_meta_25262_aux.wit_p, by decide, by decide +kernel⟩
