import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19347 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 8 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16227576 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.and, [10, 8]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [12, 0]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.and, [15, 0]⟩,
      ⟨GateOp.or, [14, 16]⟩],
      output := 17 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel
