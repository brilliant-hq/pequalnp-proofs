import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22068_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.not, [15]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_22068_aux

theorem PEqualNP.Outside.L_meta_22068 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22068_aux.wit, PEqualNP.Outside.L_meta_22068_aux.wit_p, by decide, by decide +kernel⟩
