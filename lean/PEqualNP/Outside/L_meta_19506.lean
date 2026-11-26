import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19506 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16221265 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [1, 9]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.and, [14, 2]⟩,
      ⟨GateOp.or, [12, 0]⟩,
      ⟨GateOp.or, [16, 6]⟩,
      ⟨GateOp.and, [14, 17]⟩,
      ⟨GateOp.not, [18]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

