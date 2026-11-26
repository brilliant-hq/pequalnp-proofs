import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24176_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [14, 15]⟩], 16⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24176_aux

theorem PEqualNP.Outside.L_meta_24176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266771 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24176_aux.wit, PEqualNP.Outside.L_meta_24176_aux.wit_p, by decide, by decide +kernel⟩
