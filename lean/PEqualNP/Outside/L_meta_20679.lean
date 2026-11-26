import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20679

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [3, 11]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [4, 14]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [16, 15]⟩], 17⟩

end PEqualNP.Outside.L_meta_20679

open PEqualNP.Outside.L_meta_20679

theorem PEqualNP.Outside.L_meta_20679 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11731968 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp [witness] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp
