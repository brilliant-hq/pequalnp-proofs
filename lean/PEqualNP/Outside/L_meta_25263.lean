import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25263_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25263_aux

theorem PEqualNP.Outside.L_meta_25263 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50994 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25263_aux.wit, PEqualNP.Outside.L_meta_25263_aux.wit_p, by decide, by decide +kernel⟩
