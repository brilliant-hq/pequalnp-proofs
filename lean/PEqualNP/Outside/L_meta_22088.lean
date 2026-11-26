import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22088_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_22088_aux

theorem PEqualNP.Outside.L_meta_22088 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16955 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22088_aux.wit, PEqualNP.Outside.L_meta_22088_aux.wit_p, by decide, by decide +kernel⟩
