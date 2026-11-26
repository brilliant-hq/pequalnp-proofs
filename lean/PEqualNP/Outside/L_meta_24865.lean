import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24865

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩

theorem wit_ok : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨wit, wit_ok, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_24865

theorem PEqualNP.Outside.L_meta_24865 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_24865.main_aux
