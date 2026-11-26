import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24187_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24187_aux

theorem PEqualNP.Outside.L_meta_24187 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266846 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24187_aux.wit, PEqualNP.Outside.L_meta_24187_aux.wit_p, by decide, by decide +kernel⟩
