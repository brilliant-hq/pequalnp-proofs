import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25415_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [8, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25415_aux

theorem PEqualNP.Outside.L_meta_25415 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6491967 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25415_aux.wit, PEqualNP.Outside.L_meta_25415_aux.wit_p, by decide, by decide +kernel⟩
