import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24123_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24123_aux

theorem PEqualNP.Outside.L_meta_24123 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266901 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24123_aux.wit, PEqualNP.Outside.L_meta_24123_aux.wit_p, by decide, by decide +kernel⟩
