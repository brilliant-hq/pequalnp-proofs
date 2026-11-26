import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19418 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236082 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [1, 5]⟩,
      ⟨GateOp.or, [4, 3]⟩,
      ⟨GateOp.and, [6, 0]⟩,
      ⟨GateOp.or, [12, 10]⟩,
      ⟨GateOp.or, [13, 11]⟩,
      ⟨GateOp.or, [2, 14]⟩,
      ⟨GateOp.and, [15, 9]⟩,
      ⟨GateOp.or, [9, 15]⟩,
      ⟨GateOp.not, [16]⟩,
      ⟨GateOp.and, [17, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
