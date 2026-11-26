import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24007_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24007_aux

theorem PEqualNP.Outside.L_meta_24007 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266969 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24007_aux.wit, PEqualNP.Outside.L_meta_24007_aux.wit_p, by decide, by decide +kernel⟩
