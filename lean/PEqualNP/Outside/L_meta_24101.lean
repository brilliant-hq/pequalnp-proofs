import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24101_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [6, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24101_aux

theorem PEqualNP.Outside.L_meta_24101 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4371 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24101_aux.wit, PEqualNP.Outside.L_meta_24101_aux.wit_p, by decide, by decide +kernel⟩
