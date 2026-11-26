import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25266_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25266_aux

theorem PEqualNP.Outside.L_meta_25266 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25266_aux.wit, PEqualNP.Outside.L_meta_25266_aux.wit_p, by decide, by decide +kernel⟩
