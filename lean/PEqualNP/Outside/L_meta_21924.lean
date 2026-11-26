import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21924_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem wit_p : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21924_aux

theorem PEqualNP.Outside.L_meta_21924 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33586 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21924_aux.wit, PEqualNP.Outside.L_meta_21924_aux.wit_p, by decide, by decide +kernel⟩
