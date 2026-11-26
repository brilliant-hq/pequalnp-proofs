import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19437 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3574717 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [9, 3]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.and, [5, 12]⟩,
      ⟨GateOp.or, [2, 12]⟩,
      ⟨GateOp.and, [6, 14]⟩,
      ⟨GateOp.or, [14, 6]⟩,
      ⟨GateOp.not, [16]⟩,
      ⟨GateOp.or, [15, 17]⟩,
      ⟨GateOp.or, [13, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
