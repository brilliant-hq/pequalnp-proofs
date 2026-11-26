import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24120_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24120_aux

theorem PEqualNP.Outside.L_meta_24120 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266718 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24120_aux.wit, PEqualNP.Outside.L_meta_24120_aux.wit_p, by decide, by decide +kernel⟩
