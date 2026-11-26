import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24171_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [9, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24171_aux

theorem PEqualNP.Outside.L_meta_24171 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283354 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24171_aux.wit, PEqualNP.Outside.L_meta_24171_aux.wit_p, by decide, by decide +kernel⟩
