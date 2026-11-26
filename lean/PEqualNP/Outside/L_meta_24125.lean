import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24125_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [10, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24125_aux

theorem PEqualNP.Outside.L_meta_24125 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266905 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24125_aux.wit, PEqualNP.Outside.L_meta_24125_aux.wit_p, by decide, by decide +kernel⟩
