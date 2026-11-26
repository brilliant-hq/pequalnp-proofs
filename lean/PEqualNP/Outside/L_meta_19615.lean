import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19615 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3585117 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [1, 9]⟩,
      ⟨GateOp.or, [4, 10]⟩,
      ⟨GateOp.or, [6, 0]⟩,
      ⟨GateOp.and, [4, 5]⟩,
      ⟨GateOp.and, [11, 12]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.or, [16, 14]⟩,
      ⟨GateOp.or, [13, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

