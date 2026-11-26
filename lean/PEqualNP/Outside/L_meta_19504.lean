import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19504 :
    ∃ C : Circuit,
      FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881278 : ℕ).testBit (5 * u.val + v.val)) C := by
  let C : Circuit :=
    { gates := [⟨GateOp.or, [0, 9]⟩,
      ⟨GateOp.or, [4, 10]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [1, 12]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.or, [10, 8]⟩,
      ⟨GateOp.and, [12, 15]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.not, [17]⟩,
      ⟨GateOp.or, [18, 13]⟩],
      output := 19 }
  have hfan : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; simp, by decide⟩
  refine ⟨C, hfan, by decide, ?_⟩
  decide +kernel

