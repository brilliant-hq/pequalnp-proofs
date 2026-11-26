import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24188_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24188_aux

theorem PEqualNP.Outside.L_meta_24188 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283226 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24188_aux.wit, PEqualNP.Outside.L_meta_24188_aux.wit_p, by decide, by decide +kernel⟩
