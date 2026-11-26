import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19584 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (8151870 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [1, 5]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.or, [11, 0]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.and, [14, 13]⟩,
      ⟨GateOp.or, [13, 12]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [16, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

