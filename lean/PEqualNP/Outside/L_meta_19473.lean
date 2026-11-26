import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19473 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066039 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.and, [4, 8]⟩,
      ⟨GateOp.and, [4, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [3, 12]⟩,
      ⟨GateOp.or, [13, 11]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.not, [14]⟩,
      ⟨GateOp.or, [10, 16]⟩,
      ⟨GateOp.and, [9, 15]⟩,
      ⟨GateOp.or, [17, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

