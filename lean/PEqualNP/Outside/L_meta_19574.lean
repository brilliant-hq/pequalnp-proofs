import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19574 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [7, 4]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.or, [0, 12]⟩,
      ⟨GateOp.and, [12, 0]⟩,
      ⟨GateOp.and, [3, 7]⟩,
      ⟨GateOp.not, [14]⟩,
      ⟨GateOp.and, [16, 13]⟩,
      ⟨GateOp.or, [15, 17]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

