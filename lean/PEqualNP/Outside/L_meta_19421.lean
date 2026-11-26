import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19421 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24151502 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [11, 9]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.or, [12, 8]⟩,
      ⟨GateOp.and, [14, 16]⟩,
      ⟨GateOp.or, [17, 15]⟩,
      ⟨GateOp.not, [18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
