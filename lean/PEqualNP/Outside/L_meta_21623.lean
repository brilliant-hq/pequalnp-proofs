import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21623_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [11, 10]⟩, ⟨GateOp.not, [12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21623_aux

theorem PEqualNP.Outside.L_meta_21623 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4437 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21623_aux.wit, PEqualNP.Outside.L_meta_21623_aux.wit_p, by decide, by decide +kernel⟩
