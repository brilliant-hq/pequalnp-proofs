import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19612 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3384055 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [9, 10]⟩,
      ⟨GateOp.and, [4, 7]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [13, 8]⟩,
      ⟨GateOp.or, [2, 14]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [14, 2]⟩,
      ⟨GateOp.or, [16, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

