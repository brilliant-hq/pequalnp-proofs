import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_127_aux

theorem digits2_eq (n : ℕ) (hn : 0 < n) :
    (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n / 2)).sum := by
  rw [Nat.digits_def' (by omega) hn, List.sum_cons]

theorem digits2_succ_le (n : ℕ) : (Nat.digits 2 (n + 1)).sum ≤ (Nat.digits 2 n).sum + 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; decide
    · rw [digits2_eq (n + 1) (by omega), digits2_eq n (by omega)]
      by_cases hp : n % 2 = 0
      · have h1 : (n + 1) % 2 = 1 := by omega
        have h2 : (n + 1) / 2 = n / 2 := by omega
        rw [h1, h2, hp]; omega
      · have h1 : n % 2 = 1 := by omega
        have h2 : (n + 1) % 2 = 0 := by omega
        have h3 : (n + 1) / 2 = n / 2 + 1 := by omega
        have hrec := ih (n / 2) (by omega)
        rw [h1, h2, h3]; omega

theorem digits2_add_le : ∀ s a b : ℕ, a + b ≤ s →
    (Nat.digits 2 (a + b)).sum ≤ (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  intro s
  induction s with
  | zero =>
    intro a b hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb; simp
  | succ s ih =>
    intro a b hab
    by_cases ha : a = 0
    · subst ha; simp
    by_cases hb : b = 0
    · subst hb; simp
    rw [digits2_eq (a + b) (by omega), digits2_eq a (by omega), digits2_eq b (by omega)]
    by_cases hc : a % 2 + b % 2 < 2
    · have hm : (a + b) % 2 = a % 2 + b % 2 := by omega
      have hd : (a + b) / 2 = a / 2 + b / 2 := by omega
      have hrec := ih (a / 2) (b / 2) (by omega)
      rw [hm, hd]; omega
    · have hm : (a + b) % 2 = 0 := by omega
      have hd : (a + b) / 2 = a / 2 + b / 2 + 1 := by omega
      have hrec := ih (a / 2) (b / 2) (by omega)
      have hsucc := digits2_succ_le (a / 2 + b / 2)
      rw [hm, hd]; omega

end PEqualNP.Outside.L_gct_127_aux

theorem PEqualNP.Outside.L_gct_127 : ∀ a b : ℕ, (Nat.digits 2 (a + b)).sum ≤ (Nat.digits 2 a).sum + (Nat.digits 2 b).sum :=
  fun a b => PEqualNP.Outside.L_gct_127_aux.digits2_add_le (a + b) a b le_rfl
