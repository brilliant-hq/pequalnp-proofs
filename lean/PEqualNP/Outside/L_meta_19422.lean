import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19422 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24489316 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [10, 9]⟩,
      ⟨GateOp.and, [10, 7]⟩,
      ⟨GateOp.not, [8]⟩,
      ⟨GateOp.or, [7, 12]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.or, [13, 4]⟩,
      ⟨GateOp.and, [17, 14]⟩,
      ⟨GateOp.or, [16, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
