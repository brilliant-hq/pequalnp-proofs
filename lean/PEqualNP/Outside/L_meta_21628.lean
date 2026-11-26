import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21628_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21628_aux

theorem PEqualNP.Outside.L_meta_21628 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4507 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21628_aux.wit, PEqualNP.Outside.L_meta_21628_aux.wit_p, by decide, by decide +kernel⟩
