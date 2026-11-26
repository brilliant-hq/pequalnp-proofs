import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20425

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [10, 13]⟩], 14⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun (u : Fin 3) (v : Fin 4) => (990 : ℕ).testBit (4 * u.val + v.val)) witness := by
  decide +kernel

theorem solve : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (990 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  ⟨witness, by simp [Monotone2, witness], by decide, witness_ok⟩


end PEqualNP.Outside.L_meta_20425

theorem PEqualNP.Outside.L_meta_20425 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (990 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20425.solve
