import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24884

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [10, 13]⟩], 14⟩

theorem wit_ok : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213822 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨wit, wit_ok, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_24884

theorem PEqualNP.Outside.L_meta_24884 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213822 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_24884.main_aux
