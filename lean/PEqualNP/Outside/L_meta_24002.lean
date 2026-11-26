import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24002_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [10, 11]⟩], 12⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24002_aux

theorem PEqualNP.Outside.L_meta_24002 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266708 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24002_aux.wit, PEqualNP.Outside.L_meta_24002_aux.wit_p, by decide, by decide +kernel⟩
