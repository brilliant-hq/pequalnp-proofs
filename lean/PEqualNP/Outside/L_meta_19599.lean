import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19599 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[
    ⟨.or, [5, 9]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.not, [17]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
