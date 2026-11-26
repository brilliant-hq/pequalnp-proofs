import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19605 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3251479 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.and, [7, 2]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [8, 1]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.or, [12, 0]⟩,
      ⟨GateOp.and, [1, 8]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.or, [16, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

