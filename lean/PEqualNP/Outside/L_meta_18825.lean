import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18825_aux

open PEqualNP.HeptadCover

theorem main_proof :
    ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := by
  decide

end PEqualNP.Outside.L_meta_18825_aux

theorem PEqualNP.Outside.L_meta_18825 : (∀ (x1 x2 : Fin (13 : ℕ)), x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 ↔ x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)))  := by
  exact PEqualNP.Outside.L_meta_18825_aux.main_proof
