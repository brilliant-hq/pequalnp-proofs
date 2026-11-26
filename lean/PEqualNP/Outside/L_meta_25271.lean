import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25271

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [5, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [7, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [13, 11]⟩, ⟨.not, [14]⟩], 15⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ i j : Fin 6, witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147511 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25271

theorem PEqualNP.Outside.L_meta_25271 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147511 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_25271.witness, by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25271.witness], by decide, PEqualNP.Outside.L_meta_25271.witness_ok⟩
