import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24028_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [11]⟩], 12⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24028_aux

theorem PEqualNP.Outside.L_meta_24028 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17043659 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24028_aux.wit, PEqualNP.Outside.L_meta_24028_aux.wit_p, by decide, by decide +kernel⟩
