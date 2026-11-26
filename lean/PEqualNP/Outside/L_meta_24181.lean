import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24181_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [11, 15]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24181_aux

theorem PEqualNP.Outside.L_meta_24181 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266906 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24181_aux.wit, PEqualNP.Outside.L_meta_24181_aux.wit_p, by decide, by decide +kernel⟩
