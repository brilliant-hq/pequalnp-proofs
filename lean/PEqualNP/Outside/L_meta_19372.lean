import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19372 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 8 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577398 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [10, 6]⟩,
      ⟨GateOp.or, [5, 1]⟩,
      ⟨GateOp.or, [12, 8]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.and, [13, 11]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [16, 14]⟩],
      output := 17 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
