import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19595 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16240236 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [8, 7]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [0, 10]⟩,
      ⟨GateOp.or, [12, 1]⟩,
      ⟨GateOp.or, [14, 10]⟩,
      ⟨GateOp.and, [13, 14]⟩,
      ⟨GateOp.not, [16]⟩,
      ⟨GateOp.and, [15, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

