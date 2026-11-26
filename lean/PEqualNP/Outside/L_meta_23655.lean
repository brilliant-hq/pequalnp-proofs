import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23655_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [4, 1]⟩,
     ⟨.or, [5, 0]⟩,
     ⟨.or, [5, 3]⟩,
     ⟨.or, [6, 2]⟩,
     ⟨.or, [12, 13]⟩,
     ⟨.or, [7, 14]⟩,
     ⟨.and, [10, 15]⟩,
     ⟨.or, [8, 13]⟩,
     ⟨.or, [9, 17]⟩,
     ⟨.and, [11, 18]⟩,
     ⟨.or, [16, 19]⟩], 20⟩

theorem shape : Monotone2 witness := by
  intro g h
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23655_aux

theorem PEqualNP.Outside.L_meta_23655 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275380 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23655_aux.witness, PEqualNP.Outside.L_meta_23655_aux.shape, by decide, by decide +kernel⟩
