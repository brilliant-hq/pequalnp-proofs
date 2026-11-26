import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19375 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 8 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7595814 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.or, [7, 6]⟩,
      ⟨GateOp.or, [12, 0]⟩,
      ⟨GateOp.and, [13, 11]⟩,
      ⟨GateOp.or, [12, 11]⟩,
      ⟨GateOp.not, [14]⟩,
      ⟨GateOp.and, [16, 15]⟩],
      output := 17 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
