import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19478 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237106 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [9, 0]⟩,
      ⟨GateOp.and, [6, 0]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.or, [13, 5]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.and, [16, 17]⟩,
      ⟨GateOp.or, [18, 11]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

