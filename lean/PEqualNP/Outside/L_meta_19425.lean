import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19425 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24880422 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [5, 8]⟩,
      ⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.or, [11, 8]⟩,
      ⟨GateOp.or, [4, 7]⟩,
      ⟨GateOp.and, [11, 10]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.and, [16, 17]⟩,
      ⟨GateOp.or, [14, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
