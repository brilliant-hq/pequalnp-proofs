import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24155_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24155_aux

theorem PEqualNP.Outside.L_meta_24155 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12889 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24155_aux.wit, PEqualNP.Outside.L_meta_24155_aux.wit_p, by decide, by decide +kernel⟩
