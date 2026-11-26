import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19214
open PEqualNP.CircuitLowerBounds

-- Rows 0 and 1 accept every column except column 1. Row 2 accepts columns 0 and 1.
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [10, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_19214

theorem PEqualNP.Outside.L_meta_19214 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (989 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19214.witness, ?_, by decide +kernel, ?_⟩
  · intro g mem
    simp only [PEqualNP.Outside.L_meta_19214.witness, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with h|h|h|h|h|h <;> subst g <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
