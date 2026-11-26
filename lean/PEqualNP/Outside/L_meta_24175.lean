import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24175_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.and, [13, 15]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24175_aux

theorem PEqualNP.Outside.L_meta_24175 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266334 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24175_aux.wit, PEqualNP.Outside.L_meta_24175_aux.wit_p, by decide, by decide +kernel⟩
