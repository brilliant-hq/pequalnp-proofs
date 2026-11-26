import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19114

open PEqualNP.CircuitLowerBounds

private def witness : Circuit where
  gates := [
      ⟨.and, [1, 5]⟩,
      ⟨.and, [2, 6]⟩,
      ⟨.and, [3, 7]⟩,
      ⟨.or, [9, 10]⟩,
      ⟨.or, [8, 11]⟩,
      ⟨.not, [12]⟩]
  output := 13

end PEqualNP.Outside.L_meta_19114

theorem PEqualNP.Outside.L_meta_19114 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 4 => (31711 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19114.witness, ?_, by decide +kernel, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19114.witness,
    Set.mem_insert_iff, Set.mem_singleton_iff]
