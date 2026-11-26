import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22698_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [2, 3]⟩,
     ⟨.or, [4, 5]⟩,
     ⟨.and, [10, 11]⟩,
     ⟨.or, [6, 0]⟩,
     ⟨.or, [7, 1]⟩,
     ⟨.or, [13, 14]⟩,
     ⟨.or, [8, 9]⟩,
     ⟨.or, [2, 16]⟩,
     ⟨.and, [15, 17]⟩,
     ⟨.or, [18, 12]⟩,
     ⟨.or, [4, 14]⟩,
     ⟨.and, [13, 20]⟩,
     ⟨.or, [21, 19]⟩], 22⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22698_aux

theorem PEqualNP.Outside.L_meta_22698 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851257 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22698_aux.circuit, PEqualNP.Outside.L_meta_22698_aux.mono, by decide, by decide +kernel⟩
