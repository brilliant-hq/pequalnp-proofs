import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19513 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269878 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [5, 1]⟩,
      ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.and, [9, 4]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.and, [14, 11]⟩,
      ⟨GateOp.or, [10, 16]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [17, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

