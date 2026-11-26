import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21918_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [10, 12]⟩], 13⟩

theorem wit_p : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21918_aux

theorem PEqualNP.Outside.L_meta_21918 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21918_aux.wit, PEqualNP.Outside.L_meta_21918_aux.wit_p, by decide, by decide +kernel⟩
