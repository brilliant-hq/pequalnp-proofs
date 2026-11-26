import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_19384_1 :
  (∀ (n s : ℕ) (A : Fin n → Fin n → Bool), n = 3 → PEqualNP.Represents.RepSizeAtMost (fun u v => !A u v) s → PEqualNP.Represents.RepSizeAtMost A (s + (2 * n - 4))) →
  (∀ (n s : ℕ) (A : Fin n → Fin n → Bool), 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v => !A u v) s → PEqualNP.Represents.RepSizeAtMost A (s + (2 * n - 4))) →
  (∀ (n s : ℕ) (A : Fin n → Fin n → Bool), 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v => !A u v) s → PEqualNP.Represents.RepSizeAtMost A (s + (2 * n - 4))) := by
  intro h1 h2 n s A hn hs
  have hcases : n = 3 ∨ 4 ≤ n := by omega
  exact hcases.elim
    (fun heq => h1 n s A heq hs)
    (fun hge => h2 n s A hge hs)
