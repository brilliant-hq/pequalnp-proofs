import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18823_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

set_option maxHeartbeats 800000 in
theorem Ant_R_meta_18798_417_polarity : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ -l ∈ singerLines3 (-p) := by
  set_option maxHeartbeats 20000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; aesop)

end PEqualNP.Outside.L_meta_18823_aux

theorem PEqualNP.Outside.L_meta_18823 : ∀ (x1 x2 : Fin (13 : ℕ)), x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 ↔ -x2 ∈ PEqualNP.HeptadCover.singerLines3 (-x1) := by
  first
  | exact PEqualNP.Outside.L_meta_18823_aux.Ant_R_meta_18798_417_polarity
  | (intros; apply PEqualNP.Outside.L_meta_18823_aux.Ant_R_meta_18798_417_polarity <;> assumption)
  | simpa using PEqualNP.Outside.L_meta_18823_aux.Ant_R_meta_18798_417_polarity
