import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19423 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.not, [9]⟩,
      ⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.and, [3, 3]⟩,
      ⟨GateOp.and, [0, 10]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.and, [15, 11]⟩,
      ⟨GateOp.or, [15, 14]⟩,
      ⟨GateOp.not, [16]⟩,
      ⟨GateOp.and, [18, 17]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
