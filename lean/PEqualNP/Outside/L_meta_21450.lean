import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21450_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [8, 7]⟩], 9⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21450_aux

theorem PEqualNP.Outside.L_meta_21450 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8607 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21450_aux.wit, PEqualNP.Outside.L_meta_21450_aux.wit_mono, by decide, by decide +kernel⟩
