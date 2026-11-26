import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23256

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 10]⟩], 11⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147216 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, by simp [FanInTwo, witness], by decide, by decide +kernel⟩


end PEqualNP.Outside.L_meta_23256

theorem PEqualNP.Outside.L_meta_23256 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147216 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_23256.solve
