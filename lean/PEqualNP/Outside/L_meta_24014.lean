import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24014_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [10, 11]⟩], 12⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24014_aux

theorem PEqualNP.Outside.L_meta_24014 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275357 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24014_aux.wit, PEqualNP.Outside.L_meta_24014_aux.wit_p, by decide, by decide +kernel⟩
