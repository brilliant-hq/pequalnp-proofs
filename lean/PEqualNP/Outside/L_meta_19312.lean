import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside

theorem L_meta_19312 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7644470 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.and, [4, 11]⟩,
      ⟨GateOp.or, [8, 5]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.not, [14]⟩,
      ⟨GateOp.and, [13, 0]⟩,
      ⟨GateOp.or, [12, 16]⟩,
      ⟨GateOp.or, [15, 17]⟩,
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
