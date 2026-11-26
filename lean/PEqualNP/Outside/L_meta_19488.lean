import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19488 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (3384055 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [8, 0]⟩,
      ⟨GateOp.or, [1, 10]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.and, [7, 4]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [9, 2]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [16, 11]⟩,
      ⟨GateOp.or, [17, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

