import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18823 : ∀ (x1 x2 : Fin (13 : ℕ)), x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 ↔ -x2 ∈ PEqualNP.HeptadCover.singerLines3 (-x1) := by
  decide
