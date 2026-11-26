import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19563 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [8, 0]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.and, [11, 12]⟩,
      ⟨GateOp.or, [7, 6]⟩,
      ⟨GateOp.or, [14, 8]⟩,
      ⟨GateOp.and, [15, 0]⟩,
      ⟨GateOp.or, [5, 8]⟩,
      ⟨GateOp.or, [13, 16]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

