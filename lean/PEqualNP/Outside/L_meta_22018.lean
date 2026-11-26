import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22018_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_22018_aux

theorem PEqualNP.Outside.L_meta_22018 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20413 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22018_aux.wit, PEqualNP.Outside.L_meta_22018_aux.wit_p, by decide, by decide +kernel⟩
