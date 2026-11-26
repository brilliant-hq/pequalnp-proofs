import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19566 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [5, 8]⟩,
      ⟨.and, [1, 10]⟩,
      ⟨.or, [9, 10]⟩,
      ⟨.or, [0, 8]⟩,
      ⟨.and, [12, 13]⟩,
      ⟨.or, [1, 14]⟩,
      ⟨.not, [15]⟩,
      ⟨.or, [11, 16]⟩], 17⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide
  · change PEqualNP.Represents.Represents
      (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) C
    decide +kernel
