import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21458_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [9, 8]⟩], 10⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21458_aux

theorem PEqualNP.Outside.L_meta_21458 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25375 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21458_aux.wit, PEqualNP.Outside.L_meta_21458_aux.wit_mono, by decide, by decide +kernel⟩
