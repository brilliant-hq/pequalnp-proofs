import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24166_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [10, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24166_aux

theorem PEqualNP.Outside.L_meta_24166 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274966 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24166_aux.wit, PEqualNP.Outside.L_meta_24166_aux.wit_p, by decide, by decide +kernel⟩
