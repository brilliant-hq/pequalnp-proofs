import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23244

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.not, [2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (102075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide +kernel⟩


end PEqualNP.Outside.L_meta_23244

theorem PEqualNP.Outside.L_meta_23244 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (102075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_23244.solve
