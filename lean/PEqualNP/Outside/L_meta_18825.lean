import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18825_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

set_option maxHeartbeats 1200000 in
theorem Ant_R_meta_18796_416_encoding : (
                ∀ p l : Fin 13, p ∈ singerLines3 l ↔
      p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) := by
  set_option maxHeartbeats 20000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; aesop)

end PEqualNP.Outside.L_meta_18825_aux

theorem PEqualNP.Outside.L_meta_18825 : ∀ (x1 x2 : Fin (13 : ℕ)), x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 ↔ x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)) := by
  first
  | exact PEqualNP.Outside.L_meta_18825_aux.Ant_R_meta_18796_416_encoding
  | (intros; apply PEqualNP.Outside.L_meta_18825_aux.Ant_R_meta_18796_416_encoding <;> assumption)
  | simpa using PEqualNP.Outside.L_meta_18825_aux.Ant_R_meta_18796_416_encoding
