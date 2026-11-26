import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside

theorem L_meta_19307 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7570494 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [10, 1]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [5, 13]⟩,
      ⟨GateOp.or, [6, 14]⟩,
      ⟨GateOp.and, [15, 17]⟩,
      ⟨GateOp.or, [16, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside
