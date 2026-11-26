import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22443 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881908 : ℕ).testBit (6 * u.val + v.val)) 13) := by

  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 14]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · decide +kernel
