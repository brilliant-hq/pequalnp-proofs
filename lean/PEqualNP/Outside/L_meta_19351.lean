import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside

theorem L_meta_19351 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 9 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7595814 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [11, 1]⟩,
      ⟨GateOp.or, [6, 10]⟩,
      ⟨GateOp.or, [12, 6]⟩,
      ⟨GateOp.or, [14, 7]⟩,
      ⟨GateOp.and, [13, 12]⟩,
      ⟨GateOp.not, [16]⟩,
      ⟨GateOp.and, [17, 15]⟩],
      output := 18 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
