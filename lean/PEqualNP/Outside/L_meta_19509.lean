import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19509 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223379 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [1, 0]⟩,
      ⟨GateOp.or, [7, 0]⟩,
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [1, 9]⟩,
      ⟨GateOp.and, [12, 13]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.not, [16]⟩,
      ⟨GateOp.and, [14, 11]⟩,
      ⟨GateOp.or, [17, 18]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

