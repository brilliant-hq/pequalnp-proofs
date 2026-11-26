import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21698_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [13, 12]⟩, ⟨GateOp.not, [14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21698_aux

theorem PEqualNP.Outside.L_meta_21698 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266775 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21698_aux.wit, PEqualNP.Outside.L_meta_21698_aux.wit_p, by decide, by decide +kernel⟩
