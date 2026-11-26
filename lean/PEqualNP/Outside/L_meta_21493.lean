import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21493_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.not, [7]⟩], 8⟩

theorem wit_fan : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21493_aux

theorem PEqualNP.Outside.L_meta_21493 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266447 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21493_aux.wit, PEqualNP.Outside.L_meta_21493_aux.wit_fan, by decide, by decide +kernel⟩
