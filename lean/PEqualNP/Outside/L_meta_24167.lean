import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24167_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24167_aux

theorem PEqualNP.Outside.L_meta_24167 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275030 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24167_aux.wit, PEqualNP.Outside.L_meta_24167_aux.wit_p, by decide, by decide +kernel⟩
