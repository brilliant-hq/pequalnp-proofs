import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19486 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3382551 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [9, 1]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.and, [4, 7]⟩,
      ⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.or, [8, 4]⟩,
      ⟨GateOp.or, [12, 11]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.and, [15, 17]⟩,
      ⟨GateOp.or, [18, 16]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

