import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19427 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894510 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [1, 5]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [8, 0]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [1, 13]⟩,
      ⟨GateOp.or, [5, 12]⟩,
      ⟨GateOp.and, [15, 16]⟩,
      ⟨GateOp.not, [17]⟩,
      ⟨GateOp.or, [18, 10]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
