import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_149_aux

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

theorem digits2_mul_two_pow (c j : ℕ) :
    (Nat.digits 2 (c * 2 ^ j)).sum = (Nat.digits 2 c).sum := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hc : c = 0
    · subst hc; simp
    · have hpos : 0 < c * 2 ^ (j + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hc) (by positivity)
      rw [digits2_eq _ hpos]
      have hpow : c * 2 ^ (j + 1) = (c * 2 ^ j) * 2 := by ring
      rw [hpow, Nat.mul_mod_left, Nat.mul_div_cancel _ (by omega), zero_add, ih]

theorem digits2_le_self (c : ℕ) : (Nat.digits 2 c).sum ≤ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    exact (digits2_succ_le c).trans (by omega)

theorem digits2_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (Nat.digits 2 (∑ i ∈ s, f i)).sum ≤ ∑ i ∈ s, (Nat.digits 2 (f i)).sum := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (digits2_add_le _ _ _ le_rfl).trans (Nat.add_le_add_left ih _)

end PEqualNP.Outside.L_gct_149_aux

open PEqualNP.Outside.L_gct_149_aux in
theorem PEqualNP.Outside.L_gct_149 : ∀ (n : ℕ) (α : Fin n → ℕ), (Nat.digits 2 (∑ j, α j * 2 ^ (j : ℕ))).sum ≤ ∑ j, α j ∧ 2 * ∑ j, α j * 2 ^ (j : ℕ) ≤ (∑ j, α j) * 2 ^ n := by
  intro n α
  constructor
  · calc (Nat.digits 2 (∑ j, α j * 2 ^ (j : ℕ))).sum
        ≤ ∑ j, (Nat.digits 2 (α j * 2 ^ (j : ℕ))).sum := digits2_finset_sum_le _ _
      _ = ∑ j, (Nat.digits 2 (α j)).sum := by
          apply Finset.sum_congr rfl; intro j _; exact digits2_mul_two_pow _ _
      _ ≤ ∑ j, α j := Finset.sum_le_sum (fun j _ => digits2_le_self (α j))
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hpow : 2 * 2 ^ (j : ℕ) ≤ 2 ^ n := by
      have : 2 * 2 ^ (j : ℕ) = 2 ^ ((j : ℕ) + 1) := by ring
      rw [this]
      exact Nat.pow_le_pow_right (by omega) j.isLt
    calc 2 * (α j * 2 ^ (j : ℕ)) = α j * (2 * 2 ^ (j : ℕ)) := by ring
      _ ≤ α j * 2 ^ n := Nat.mul_le_mul_left (α j) hpow
