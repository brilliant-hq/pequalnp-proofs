import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24058_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [9, 12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24058_aux

theorem PEqualNP.Outside.L_meta_24058 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13016 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24058_aux.wit, PEqualNP.Outside.L_meta_24058_aux.wit_p, by decide, by decide +kernel⟩
