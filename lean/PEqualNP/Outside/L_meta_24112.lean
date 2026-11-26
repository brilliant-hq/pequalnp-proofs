import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24112_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [7, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24112_aux

theorem PEqualNP.Outside.L_meta_24112 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12890 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24112_aux.wit, PEqualNP.Outside.L_meta_24112_aux.wit_p, by decide, by decide +kernel⟩
