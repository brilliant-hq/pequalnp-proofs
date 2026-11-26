import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24119_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [8, 13]⟩], 14⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24119_aux

theorem PEqualNP.Outside.L_meta_24119 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266462 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24119_aux.wit, PEqualNP.Outside.L_meta_24119_aux.wit_p, by decide, by decide +kernel⟩
