import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21464_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [10, 9]⟩], 11⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21464_aux

theorem PEqualNP.Outside.L_meta_21464 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25503 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21464_aux.wit, PEqualNP.Outside.L_meta_21464_aux.wit_mono, by decide, by decide +kernel⟩
