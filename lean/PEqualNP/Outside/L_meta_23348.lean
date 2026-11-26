import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23348

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.not, [4]⟩, ⟨.not, [5]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [9, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [8, 11]⟩], 12⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50079 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide +kernel⟩


end PEqualNP.Outside.L_meta_23348

theorem PEqualNP.Outside.L_meta_23348 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50079 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_23348.solve
