import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19603 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3249245 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [5, 0]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [10, 6]⟩,
      ⟨GateOp.or, [6, 1]⟩,
      ⟨GateOp.and, [13, 11]⟩,
      ⟨GateOp.not, [14]⟩,
      ⟨GateOp.and, [7, 2]⟩,
      ⟨GateOp.and, [12, 15]⟩,
      ⟨GateOp.or, [16, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

