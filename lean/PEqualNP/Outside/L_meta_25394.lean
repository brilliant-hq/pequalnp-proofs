import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25394_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.and, [11, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25394_aux

theorem PEqualNP.Outside.L_meta_25394 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408631 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25394_aux.wit, PEqualNP.Outside.L_meta_25394_aux.wit_p, by decide, by decide +kernel⟩
