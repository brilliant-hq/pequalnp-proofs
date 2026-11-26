import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25371_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25371_aux

theorem PEqualNP.Outside.L_meta_25371 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4378043 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25371_aux.wit, PEqualNP.Outside.L_meta_25371_aux.wit_p, by decide, by decide +kernel⟩
