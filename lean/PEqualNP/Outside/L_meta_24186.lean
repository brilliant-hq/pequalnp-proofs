import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24186_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [11, 16]⟩], 17⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24186_aux

theorem PEqualNP.Outside.L_meta_24186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266774 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24186_aux.wit, PEqualNP.Outside.L_meta_24186_aux.wit_p, by decide, by decide +kernel⟩
