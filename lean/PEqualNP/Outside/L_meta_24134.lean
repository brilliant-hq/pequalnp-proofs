import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24134_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24134_aux

theorem PEqualNP.Outside.L_meta_24134 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275099 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24134_aux.wit, PEqualNP.Outside.L_meta_24134_aux.wit_p, by decide, by decide +kernel⟩
