import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19489 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3573853 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [9, 3]⟩,
      ⟨GateOp.or, [10, 1]⟩,
      ⟨GateOp.or, [11, 4]⟩,
      ⟨GateOp.and, [5, 4]⟩,
      ⟨GateOp.or, [12, 2]⟩,
      ⟨GateOp.and, [14, 6]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.or, [14, 6]⟩,
      ⟨GateOp.not, [17]⟩,
      ⟨GateOp.or, [16, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

