import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22185

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [2, 15]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 17]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [19, 16]⟩, ⟨GateOp.or, [20, 18]⟩], output := 21 }

theorem mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
  simp [PEqualNP.MetaComplexity.Monotone2, C0]

end PEqualNP.Outside.L_meta_22185

theorem PEqualNP.Outside.L_meta_22185 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841532 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22185.C0, PEqualNP.Outside.L_meta_22185.mono, by decide, by decide⟩
