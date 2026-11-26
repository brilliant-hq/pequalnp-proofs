import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside

theorem L_meta_19306 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247802 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.and, [1, 10]⟩,
      ⟨GateOp.or, [6, 5]⟩,
      ⟨GateOp.or, [0, 11]⟩,
      ⟨GateOp.or, [12, 1]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.and, [0, 15]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.and, [14, 17]⟩,
      ⟨GateOp.or, [18, 16]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
