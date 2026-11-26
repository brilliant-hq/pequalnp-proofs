import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

theorem wit_p : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21904_aux

theorem PEqualNP.Outside.L_meta_21904 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1852 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21904_aux.wit, PEqualNP.Outside.L_meta_21904_aux.wit_p, by decide, by decide +kernel⟩
