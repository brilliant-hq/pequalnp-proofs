import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19480 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3245886 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [5, 0]⟩,
      ⟨GateOp.or, [6, 0]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.and, [1, 11]⟩,
      ⟨GateOp.or, [12, 2]⟩,
      ⟨GateOp.or, [12, 11]⟩,
      ⟨GateOp.or, [7, 11]⟩,
      ⟨GateOp.and, [16, 14]⟩,
      ⟨GateOp.not, [17]⟩,
      ⟨GateOp.and, [15, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

