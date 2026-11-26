import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25407_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [9, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25407_aux

theorem PEqualNP.Outside.L_meta_25407 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475068 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25407_aux.wit, PEqualNP.Outside.L_meta_25407_aux.wit_p, by decide, by decide +kernel⟩
