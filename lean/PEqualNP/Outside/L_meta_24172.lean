import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24172_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24172_aux

theorem PEqualNP.Outside.L_meta_24172 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283422 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24172_aux.wit, PEqualNP.Outside.L_meta_24172_aux.wit_p, by decide, by decide +kernel⟩
