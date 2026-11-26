import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24092_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [7, 12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24092_aux

theorem PEqualNP.Outside.L_meta_24092 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (553819 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24092_aux.wit, PEqualNP.Outside.L_meta_24092_aux.wit_p, by decide, by decide +kernel⟩
