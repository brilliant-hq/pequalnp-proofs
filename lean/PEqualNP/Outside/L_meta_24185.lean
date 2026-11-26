import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24185_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [8, 16]⟩], 17⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24185_aux

theorem PEqualNP.Outside.L_meta_24185 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266770 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24185_aux.wit, PEqualNP.Outside.L_meta_24185_aux.wit_p, by decide, by decide +kernel⟩
