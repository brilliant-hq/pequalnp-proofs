import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19364 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 7 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [5, 1]⟩,
      ⟨GateOp.and, [12, 11]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.or, [11, 5]⟩,
      ⟨GateOp.and, [15, 14]⟩],
      output := 16 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
