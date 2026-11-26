import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24184_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.not, [15]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24184_aux

theorem PEqualNP.Outside.L_meta_24184 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (553817 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24184_aux.wit, PEqualNP.Outside.L_meta_24184_aux.wit_p, by decide, by decide +kernel⟩
