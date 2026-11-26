import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22086_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_22086_aux

theorem PEqualNP.Outside.L_meta_22086 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16949 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22086_aux.wit, PEqualNP.Outside.L_meta_22086_aux.wit_p, by decide, by decide +kernel⟩
