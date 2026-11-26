import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24115_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24115_aux

theorem PEqualNP.Outside.L_meta_24115 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (29529 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24115_aux.wit, PEqualNP.Outside.L_meta_24115_aux.wit_p, by decide, by decide +kernel⟩
