import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19546

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [5, 12]⟩,
    ⟨.or, [6, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [21, 22]⟩,
    ⟨.or, [23, 20]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [28, 18]⟩,
    ⟨.or, [15, 17]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [24, 25]⟩, ⟨.and, [26, 27]⟩, ⟨.and, [29, 31]⟩,
    ⟨.or, [32, 33]⟩, ⟨.or, [35, 34]⟩], 36⟩

theorem legal : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_19546

theorem PEqualNP.Outside.L_meta_19546 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 23 := by
  refine ⟨PEqualNP.Outside.L_meta_19546.witness, PEqualNP.Outside.L_meta_19546.legal, by decide, ?_⟩
  decide +kernel
