import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19424 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.or, [10, 7]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [1, 13]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.or, [8, 7]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [16, 0]⟩,
      ⟨GateOp.or, [18, 17]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
