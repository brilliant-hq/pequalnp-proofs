import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24098_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24098_aux

theorem PEqualNP.Outside.L_meta_24098 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4184 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24098_aux.wit, PEqualNP.Outside.L_meta_24098_aux.wit_p, by decide, by decide +kernel⟩
