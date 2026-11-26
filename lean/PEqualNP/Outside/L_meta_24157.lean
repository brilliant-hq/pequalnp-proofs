import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24157_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [7, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24157_aux

theorem PEqualNP.Outside.L_meta_24157 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266322 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24157_aux.wit, PEqualNP.Outside.L_meta_24157_aux.wit_p, by decide, by decide +kernel⟩
