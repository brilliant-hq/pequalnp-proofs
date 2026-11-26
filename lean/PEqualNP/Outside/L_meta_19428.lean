import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19428 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [8, 0]⟩,
      ⟨GateOp.and, [9, 1]⟩,
      ⟨GateOp.or, [10, 1]⟩,
      ⟨GateOp.and, [1, 1]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.or, [7, 13]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.or, [15, 6]⟩,
      ⟨GateOp.and, [16, 17]⟩,
      ⟨GateOp.or, [14, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
