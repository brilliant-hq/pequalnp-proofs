import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24151_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24151_aux

theorem PEqualNP.Outside.L_meta_24151 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4442 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24151_aux.wit, PEqualNP.Outside.L_meta_24151_aux.wit_p, by decide, by decide +kernel⟩
