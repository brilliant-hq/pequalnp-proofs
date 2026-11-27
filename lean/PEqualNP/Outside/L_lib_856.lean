import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_856

open Finset

theorem mul_choose_id (i j : ℕ) :
    i * i.choose j = (j + 1) * i.choose (j + 1) + j * i.choose j := by
  have h := Nat.choose_succ_right_eq i j
  rcases le_or_gt j i with hji | hji
  · rw [show i * i.choose j = (i - j) * i.choose j + j * i.choose j by
      rw [← add_mul, Nat.sub_add_cancel hji]]
    rw [mul_comm (i - j), ← h]
    ring
  · rw [Nat.choose_eq_zero_of_lt hji, Nat.choose_eq_zero_of_lt (by omega)]
    ring

theorem closure_mom (F G : ℕ → ℕ) (N d : ℕ)
    (h : ∀ j ≤ d, ∑ i ∈ range N, F i * i.choose j = ∑ i ∈ range N, G i * i.choose j) :
    ∀ a j, a + j ≤ d →
      ∑ i ∈ range N, F i * (i ^ a * i.choose j) = ∑ i ∈ range N, G i * (i ^ a * i.choose j) := by
  intro a
  induction a with
  | zero =>
    intro j hj
    simp only [pow_zero, one_mul]
    exact h j (by omega)
  | succ a ih =>
    intro j hj
    have e : ∀ (H : ℕ → ℕ), ∑ i ∈ range N, H i * (i ^ (a + 1) * i.choose j) =
        (j + 1) * ∑ i ∈ range N, H i * (i ^ a * i.choose (j + 1)) +
          j * ∑ i ∈ range N, H i * (i ^ a * i.choose j) := by
      intro H
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have := mul_choose_id i j
      calc H i * (i ^ (a + 1) * i.choose j) = H i * i ^ a * (i * i.choose j) := by ring
        _ = H i * i ^ a * ((j + 1) * i.choose (j + 1) + j * i.choose j) := by rw [this]
        _ = _ := by ring
    rw [e F, e G, ih (j + 1) (by omega), ih j (by omega)]

theorem shift (F G : ℕ → ℕ) (N k d : ℕ) (hk : ∀ i < k, F i = G i)
    (hm : ∀ n ≤ d, ∑ i ∈ range N, F i * i ^ n = ∑ i ∈ range N, G i * i ^ n)
    (hF : ∀ i, N ≤ i → F i = 0) (hG : ∀ i, N ≤ i → G i = 0) :
    ∀ n ≤ d, ∑ i ∈ range N, F (k + i) * i ^ n = ∑ i ∈ range N, G (k + i) * i ^ n := by
  intro n hn
  have hT : ∀ H : ℕ → ℕ, (∀ i, N ≤ i → H i = 0) →
      ∑ j ∈ range (k + N), (H j : ℤ) * ((j : ℤ) - k) ^ n =
        ∑ l ∈ range (n + 1), ((n.choose l : ℤ) * (-(k : ℤ)) ^ (n - l)) *
          ((∑ i ∈ range N, H i * i ^ l : ℕ) : ℤ) := by
    intro H hH
    have hext : ∀ l, ∑ j ∈ range (k + N), (H j : ℤ) * (j : ℤ) ^ l =
        ((∑ i ∈ range N, H i * i ^ l : ℕ) : ℤ) := by
      intro l
      push_cast
      rw [add_comm k N, Finset.sum_range_add]
      have : ∑ x ∈ range k, (H (N + x) : ℤ) * ((N + x : ℕ) : ℤ) ^ l = 0 :=
        Finset.sum_eq_zero (fun x _ => by rw [hH (N + x) (by omega)]; simp)
      rw [this, add_zero]
    simp_rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← hext l, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hsplit : ∀ H : ℕ → ℕ, ∑ j ∈ range (k + N), (H j : ℤ) * ((j : ℤ) - k) ^ n =
      ∑ j ∈ range k, (H j : ℤ) * ((j : ℤ) - k) ^ n +
        ((∑ i ∈ range N, H (k + i) * i ^ n : ℕ) : ℤ) := by
    intro H
    rw [Finset.sum_range_add]
    push_cast
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpre : ∑ j ∈ range k, (F j : ℤ) * ((j : ℤ) - k) ^ n =
      ∑ j ∈ range k, (G j : ℤ) * ((j : ℤ) - k) ^ n :=
    Finset.sum_congr rfl (fun j hj => by rw [hk j (Finset.mem_range.mp hj)])
  have hTT : ∑ l ∈ range (n + 1), ((n.choose l : ℤ) * (-(k : ℤ)) ^ (n - l)) *
          ((∑ i ∈ range N, F i * i ^ l : ℕ) : ℤ) =
      ∑ l ∈ range (n + 1), ((n.choose l : ℤ) * (-(k : ℤ)) ^ (n - l)) *
          ((∑ i ∈ range N, G i * i ^ l : ℕ) : ℤ) :=
    Finset.sum_congr rfl (fun l hl => by
      rw [hm l (by have := Finset.mem_range.mp hl; omega)])
  have h1 := hsplit F
  have h2 := hsplit G
  rw [hT F hF] at h1
  rw [hT G hG] at h2
  have : ((∑ i ∈ range N, F (k + i) * i ^ n : ℕ) : ℤ) =
      ((∑ i ∈ range N, G (k + i) * i ^ n : ℕ) : ℤ) := by linarith
  exact_mod_cast this

def ext (D : ℕ) (φ : Fin (D + 1) → ℕ) (i : ℕ) : ℕ := if h : i < D + 1 then φ ⟨i, h⟩ else 0

theorem ext_sum (D : ℕ) (φ : Fin (D + 1) → ℕ) (c : ℕ → ℕ) :
    ∑ i : Fin (D + 1), φ i * c i.val = ∑ i ∈ range (D + 1), ext D φ i * c i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext D φ i * c i) (D + 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [ext, i.isLt]

theorem ext_zero (D : ℕ) (φ : Fin (D + 1) → ℕ) (i : ℕ) (hi : D + 1 ≤ i) : ext D φ i = 0 := by
  simp [ext]; omega

theorem from_ne (D d P : ℕ) (x y : Fin (D + 1) → ℕ) (hx : ∑ i, x i = P) (hy : ∑ i, y i = P)
    (hne : x ≠ y)
    (hb : ∀ j ≤ d, ∑ i : Fin (D + 1), x i * i.val.choose j = ∑ i : Fin (D + 1), y i * i.val.choose j) :
    ∃ (f g : Fin (D + 1) → ℕ),
      (∑ i, f i) = P ∧ (∑ i, g i) = P ∧ f 0 ≠ g 0 ∧
        ∀ n ≤ d, (∑ i : Fin (D + 1), f i * i.val ^ n) = ∑ i : Fin (D + 1), g i * i.val ^ n := by
  set F := ext D x
  set G := ext D y
  have hbF : ∀ j ≤ d, ∑ i ∈ range (D + 1), F i * i.choose j = ∑ i ∈ range (D + 1), G i * i.choose j := by
    intro j hj
    rw [← ext_sum D x (fun i => i.choose j), ← ext_sum D y (fun i => i.choose j)]
    exact hb j hj
  have hpow : ∀ n ≤ d, ∑ i ∈ range (D + 1), F i * i ^ n = ∑ i ∈ range (D + 1), G i * i ^ n := by
    intro n hn
    have := closure_mom F G (D + 1) d hbF n 0 (by omega)
    simpa using this
  have hex : ∃ i, F i ≠ G i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨i.val, ?_⟩
    simpa [F, G, ext, i.isLt] using hi
  classical
  set k := Nat.find hex
  have hkspec : F k ≠ G k := Nat.find_spec hex
  have hkmin : ∀ i < k, F i = G i := fun i hi => by
    by_contra h
    exact Nat.find_min hex hi h
  have hFz : ∀ i, D + 1 ≤ i → F i = 0 := ext_zero D x
  have hGz : ∀ i, D + 1 ≤ i → G i = 0 := ext_zero D y
  have hsh := shift F G (D + 1) k d hkmin hpow hFz hGz
  set R := ∑ i ∈ range k, F i
  have hR : ∑ i ∈ range k, G i = R := Finset.sum_congr rfl (fun i hi => (hkmin i (Finset.mem_range.mp hi)).symm)
  have htot : ∀ H : ℕ → ℕ, (∀ i, D + 1 ≤ i → H i = 0) →
      ∑ i ∈ range k, H i + ∑ i ∈ range (D + 1), H (k + i) = ∑ i ∈ range (D + 1), H i := by
    intro H hH
    rw [← Finset.sum_range_add, add_comm k (D + 1), Finset.sum_range_add]
    have : ∑ x ∈ range k, H (D + 1 + x) = 0 := Finset.sum_eq_zero (fun x _ => hH _ (by omega))
    rw [this, add_zero]
  have hsF : ∑ i ∈ range (D + 1), F i = P := by
    rw [← hx]; have := ext_sum D x (fun _ => 1); simpa using this.symm
  have hsG : ∑ i ∈ range (D + 1), G i = P := by
    rw [← hy]; have := ext_sum D y (fun _ => 1); simpa using this.symm
  have hite : ∀ c : ℕ → ℕ, ∑ i : Fin (D + 1), (if i.val = 0 then R else 0) * c i.val = R * c 0 := by
    intro c
    rw [Fin.sum_univ_succ]
    simp
  refine ⟨fun i => (if i.val = 0 then R else 0) + F (k + i.val),
    fun i => (if i.val = 0 then R else 0) + G (k + i.val), ?_, ?_, ?_, ?_⟩
  · have := hite (fun _ => 1)
    simp only [mul_one] at this
    rw [Finset.sum_add_distrib, this, Fin.sum_univ_eq_sum_range (fun i => F (k + i)) (D + 1),
      htot F hFz, hsF]
  · have := hite (fun _ => 1)
    simp only [mul_one] at this
    rw [Finset.sum_add_distrib, this, Fin.sum_univ_eq_sum_range (fun i => G (k + i)) (D + 1), ← hR,
      htot G hGz, hsG]
  · simp only [Fin.val_zero, ite_true, add_zero]
    intro h
    exact hkspec (by omega)
  · intro n hn
    simp only [add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hite (fun i => i ^ n),
      Fin.sum_univ_eq_sum_range (fun i => F (k + i) * i ^ n) (D + 1),
      Fin.sum_univ_eq_sum_range (fun i => G (k + i) * i ^ n) (D + 1), hsh n hn]

theorem main_first (D d P : ℕ)
    (h : ∏ j ∈ Finset.range d, (P * Nat.choose D (j + 1) + 1) < Nat.choose (P + D) D) :
    ∃ (f g : Fin (D + 1) → ℕ),
      (∑ i, f i) = P ∧ (∑ i, g i) = P ∧ f 0 ≠ g 0 ∧
        ∀ n ≤ d, (∑ i : Fin (D + 1), f i * i.val ^ n) = ∑ i : Fin (D + 1), g i * i.val ^ n := by
  classical
  set s := (univ : Finset (Fin (D + 1))).finsuppAntidiag P
  set t := Fintype.piFinset (fun j : Fin d => range (P * Nat.choose D (j.val + 1) + 1))
  have hs : s.card = Nat.choose (P + D) D := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
      show D + 1 + P - 1 = P + D by omega, Nat.choose_symm_add]
  have ht : t.card = ∏ j ∈ Finset.range d, (P * Nat.choose D (j + 1) + 1) := by
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    exact Fin.prod_univ_eq_prod_range (fun j => P * Nat.choose D (j + 1) + 1) d
  let Φ : (Fin (D + 1) →₀ ℕ) → (Fin d → ℕ) :=
    fun f j => ∑ i : Fin (D + 1), f i * i.val.choose (j.val + 1)
  have hmaps : ∀ f ∈ s, Φ f ∈ t := by
    intro f hf
    rw [Finset.mem_finsuppAntidiag] at hf
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc Φ f j ≤ ∑ i : Fin (D + 1), f i * D.choose (j.val + 1) :=
          Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _
            (Nat.choose_le_choose _ (Nat.lt_succ_iff.mp i.isLt)))
      _ = P * D.choose (j.val + 1) := by rw [← Finset.sum_mul, hf.1]
  obtain ⟨x, hx, y, hy, hne, hxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hs, ht]; exact h) hmaps
  rw [Finset.mem_finsuppAntidiag] at hx hy
  apply from_ne D d P x y hx.1 hy.1
  · intro he
    exact hne (DFunLike.coe_injective he)
  · intro j hj
    rcases j with _ | j
    · simp only [Nat.choose_zero_right, mul_one]
      rw [hx.1, hy.1]
    · exact congrFun hxy ⟨j, by omega⟩

theorem desc_lower (D : ℕ) : ∀ k, k ≤ D → (D + 1) ^ k * D.descFactorial k ≤ (D * D + D).descFactorial k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ]
    have h1 := ih (by omega)
    have h2 : (D + 1) * (D - k) ≤ D * D + D - k := by
      obtain ⟨e, rfl⟩ : ∃ e, D = k + 1 + e := ⟨D - (k + 1), by omega⟩
      rw [show k + 1 + e - k = e + 1 by omega]
      have : (k + 1 + e) * (k + 1 + e) + (k + 1 + e) - k = (k + 1 + e) * (k + 1 + e) + e + 1 := by omega
      rw [this]
      nlinarith
    calc (D + 1) ^ k * (D + 1) * ((D - k) * D.descFactorial k)
        = ((D + 1) * (D - k)) * ((D + 1) ^ k * D.descFactorial k) := by ring
      _ ≤ (D * D + D - k) * (D * D + D).descFactorial k := Nat.mul_le_mul h2 h1

theorem choose_lower (D : ℕ) : (D + 1) ^ D ≤ Nat.choose (D * D + D) D := by
  have h := desc_lower D D le_rfl
  rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, mul_comm] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos D)

theorem second_to_first (D d P : ℕ)
    (h : ∃ k : ℕ, 0 < k ∧ D = 2 ^ k ∧ P = D ^ 2 ∧ d * (d + 7) < 2 * D) :
    ∏ j ∈ Finset.range d, (P * Nat.choose D (j + 1) + 1) < Nat.choose (P + D) D := by
  obtain ⟨k, hk, hD, hP, hd⟩ := h
  have hD2 : 2 ≤ D := by
    rw [hD]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  subst hP
  have hterm : ∀ j ∈ Finset.range d, D ^ 2 * Nat.choose D (j + 1) + 1 ≤ D ^ (j + 4) := by
    intro j _
    have hc := Nat.choose_le_pow D (j + 1)
    have hpos : 1 ≤ D ^ (j + 3) := Nat.one_le_pow _ _ (by omega)
    calc D ^ 2 * Nat.choose D (j + 1) + 1 ≤ D ^ 2 * D ^ (j + 1) + 1 :=
          by have := Nat.mul_le_mul_left (D ^ 2) hc; omega
      _ = D ^ (j + 3) + 1 := by rw [← pow_add]; ring_nf
      _ ≤ D * D ^ (j + 3) := by nlinarith
      _ = D ^ (j + 4) := by rw [← pow_succ']
  have hprod := Finset.prod_le_prod' hterm
  rw [Finset.prod_pow_eq_pow_sum] at hprod
  have hE : (∑ j ∈ Finset.range d, (j + 4)) * 2 = d * (d + 7) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, add_mul,
      Finset.sum_range_id_mul_two]
    rcases d with _ | e
    · simp
    · simp only [smul_eq_mul, Nat.add_sub_cancel]; ring
  have hlt : ∑ j ∈ Finset.range d, (j + 4) < D := by omega
  calc ∏ j ∈ Finset.range d, (D ^ 2 * Nat.choose D (j + 1) + 1)
      ≤ D ^ (∑ j ∈ Finset.range d, (j + 4)) := hprod
    _ < D ^ D := Nat.pow_lt_pow_right (by omega) hlt
    _ ≤ (D + 1) ^ D := Nat.pow_le_pow_left (by omega) D
    _ ≤ Nat.choose (D * D + D) D := choose_lower D
    _ = Nat.choose (D ^ 2 + D) D := by rw [sq]

end PEqualNP.Outside.L_lib_856

open PEqualNP.Outside.L_lib_856 in
theorem PEqualNP.Outside.L_lib_856 : ∀ (D d P : ℕ),
  let slots := ∏ j ∈ Finset.range d, (P * Nat.choose D (j+1) + 1)
  (slots < Nat.choose (P+D) D ∨
    (∃ k : ℕ, 0 < k ∧ D = 2^k ∧ P = D^2 ∧ d*(d+7) < 2*D)) →
  ∃ (f g : Fin (D+1) → ℕ),
    (∑ i, f i) = P ∧ (∑ i, g i) = P ∧ f 0 ≠ g 0 ∧
      ∀ n ≤ d, (∑ i : Fin (D+1), f i * i.val^n) =
        ∑ i : Fin (D+1), g i * i.val^n := by
  intro D d P slots h
  rcases h with h | h
  · exact main_first D d P h
  · exact main_first D d P (second_to_first D d P h)
