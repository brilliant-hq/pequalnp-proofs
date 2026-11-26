import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25411_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [5]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.and, [11, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25411_aux

theorem PEqualNP.Outside.L_meta_25411 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475709 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25411_aux.wit, PEqualNP.Outside.L_meta_25411_aux.wit_p, by decide, by decide +kernel⟩
