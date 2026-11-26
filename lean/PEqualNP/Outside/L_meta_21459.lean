import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21459_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [8, 6]⟩, ⟨GateOp.or, [9, 7]⟩], 10⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21459_aux

theorem PEqualNP.Outside.L_meta_21459 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (549855 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21459_aux.wit, PEqualNP.Outside.L_meta_21459_aux.wit_mono, by decide, by decide +kernel⟩
