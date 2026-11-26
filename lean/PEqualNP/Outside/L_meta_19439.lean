import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19439 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3957566 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [1, 0]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.or, [0, 11]⟩,
      ⟨GateOp.and, [5, 10]⟩,
      ⟨GateOp.or, [7, 12]⟩,
      ⟨GateOp.or, [13, 4]⟩,
      ⟨GateOp.or, [15, 12]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.not, [17]⟩,
      ⟨GateOp.and, [18, 16]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
