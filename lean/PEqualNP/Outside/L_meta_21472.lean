import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21472_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21472_aux

theorem PEqualNP.Outside.L_meta_21472 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (9116 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21472_aux.wit, PEqualNP.Outside.L_meta_21472_aux.wit_mono, by decide, by decide +kernel⟩
