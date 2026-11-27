import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_828

open Finset

theorem split_le {ι : Type} [DecidableEq ι] (w : ι → ℕ) :
    ∀ (s : Finset ι) (n : ℕ), n ≤ ∑ j ∈ s, w j →
      ∃ a : ι → ℕ, (∀ j, a j ≤ w j) ∧ ∑ j ∈ s, a j = n := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro n hn; exact ⟨0, fun _ => Nat.zero_le _, by simp at hn; simp; omega⟩
  | insert x s hx ih =>
    intro n hn
    rw [sum_insert hx] at hn
    by_cases h : n ≤ ∑ j ∈ s, w j
    · obtain ⟨a, ha, hs⟩ := ih n h
      refine ⟨Function.update a x 0, ?_, ?_⟩
      · intro j
        by_cases hj : j = x
        · subst hj; simp
        · rw [Function.update_of_ne hj]; exact ha j
      · rw [sum_insert hx, Function.update_self, zero_add, ← hs]
        apply sum_congr rfl
        intro j hj
        rw [Function.update_of_ne]
        rintro rfl
        exact hx hj
    · push Not at h
      obtain ⟨a, ha, hs⟩ := ih (∑ j ∈ s, w j) le_rfl
      refine ⟨Function.update a x (n - ∑ j ∈ s, w j), ?_, ?_⟩
      · intro j
        by_cases hj : j = x
        · subst hj; simp; omega
        · rw [Function.update_of_ne hj]; exact ha j
      · rw [sum_insert hx, Function.update_self]
        have e : ∑ j ∈ s, Function.update a x (n - ∑ j ∈ s, w j) j = ∑ j ∈ s, a j := by
          apply sum_congr rfl
          intro j hj
          rw [Function.update_of_ne]
          rintro rfl
          exact hx hj
        rw [e, hs]
        omega

theorem shift_Ico (f : ℕ → ℕ) (k p : ℕ) :
    ∑ i ∈ Ico (k+1) (p+1), f i * 2^(i-(k+1)) = ∑ i ∈ Ico k p, f (i+1) * 2^(i-k) := by
  rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
  have : p + 1 - (k + 1) = p - k := by omega
  rw [this]
  apply sum_congr rfl
  intro i _
  have h1 : k + 1 + i - (k + 1) = i := by omega
  have h2 : k + i - k = i := by omega
  have h3 : k + 1 + i = k + i + 1 := by omega
  rw [h1, h2, h3]

theorem pack (q : ℕ) (hq : 0 < q) : ∀ (p C : ℕ) (n : ℕ → ℕ),
    ∑ i ∈ range p, n i * 2^i = q * C →
    (∀ k, ∑ i ∈ Ico k p, n i * 2^(i-k) ≤ q * (C / 2^k)) →
    ∃ v : ℕ → Fin q → ℕ, (∀ i < p, ∑ j, v i j = n i) ∧
      ∀ j, ∑ i ∈ range p, 2^i * v i j = C := by
  intro p
  induction p with
  | zero =>
    intro C n htot _
    simp only [range_zero, sum_empty] at htot
    refine ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), fun j => ?_⟩
    simp only [range_zero, sum_empty]
    rcases Nat.mul_eq_zero.mp htot.symm with h | h <;> omega
  | succ p ih =>
    intro C n htot hcut
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · refine ⟨fun _ _ => C, ?_, ?_⟩
      · intro i hi
        have : i = 0 := by omega
        subst this
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        simp at htot
        omega
      · intro j; simp
    set S := ∑ i ∈ range p, n (i+1) * 2^i with hS
    have htot' : n 0 + 2 * S = q * C := by
      rw [← htot, sum_range_succ', hS, mul_sum]
      simp only [pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      ring
    have h1 : S ≤ q * (C / 2) := by
      have := hcut 1
      rw [shift_Ico n 0 p] at this
      simpa [hS, sum_Ico_eq_sum_range] using this
    set C' := C / 2 with hC'
    set c := C % 2 with hc
    have hCd : C = 2 * C' + c := (Nat.div_add_mod C 2).symm
    have hqC : q * C = 2 * (q * C') + q * c := by rw [hCd]; ring
    set P := q * C' - S with hP
    have hn0 : n 0 = 2 * P + q * c := by omega
    let n' : ℕ → ℕ := fun i => n (i+1) + if i = 0 then P else 0
    have htot2 : ∑ i ∈ range p, n' i * 2^i = q * C' := by
      simp only [n', add_mul, sum_add_distrib, ite_mul, zero_mul]
      rw [← hS, sum_ite_eq' (range p) 0 (fun i => P * 2^i)]
      rw [if_pos (mem_range.mpr hp)]
      simp
      omega
    have hcut2 : ∀ k, ∑ i ∈ Ico k p, n' i * 2^(i-k) ≤ q * (C' / 2^k) := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [Nat.sub_zero, pow_zero, Nat.div_one]
        rw [← Finset.range_eq_Ico]
        exact le_of_eq htot2
      · have := hcut (k+1)
        rw [shift_Ico n k p] at this
        have e : ∑ i ∈ Ico k p, n' i * 2^(i-k) = ∑ i ∈ Ico k p, n (i+1) * 2^(i-k) := by
          apply sum_congr rfl
          intro i hi
          rw [mem_Ico] at hi
          have : i ≠ 0 := by omega
          simp [n', this]
        rw [e]
        have e2 : C / 2^(k+1) = C' / 2^k := by
          rw [hC', Nat.div_div_eq_div_mul, pow_succ']
        rwa [e2] at this
    obtain ⟨v', hrow', hbin'⟩ := ih C' n' htot2 hcut2
    have hle : n 1 ≤ ∑ j, v' 0 j := by
      rw [hrow' 0 hp]; simp [n']
    obtain ⟨a, ha, hsa⟩ := split_le (v' 0) univ (n 1) hle
    refine ⟨fun i j => if i = 0 then c + 2 * (v' 0 j - a j)
        else if i = 1 then a j else v' (i-1) j, ?_, ?_⟩
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [if_true]
        rw [sum_add_distrib, ← mul_sum, sum_tsub_distrib _ (fun j _ => ha j), hsa, hrow' 0 hp]
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, n', if_true]
        have e01 : n (0+1) = n 1 := rfl
        rw [e01]
        omega
      · by_cases h1 : i = 1
        · subst h1; simp [hsa]
        · have hi1 : i ≠ 0 := by omega
          simp only [hi1, h1, if_false]
          rw [hrow' (i-1) (by omega)]
          have : i - 1 ≠ 0 := by omega
          simp only [n', this, if_false, add_zero]
          congr 1
          omega
    · intro j
      have hb := hbin' j
      let v'' : ℕ → ℕ := fun i => if i = 0 then a j else v' i j
      have e1 : ∑ i ∈ range p, 2^i * v' i j
          = ∑ i ∈ range p, 2^i * v'' i + (v' 0 j - a j) := by
        have : ∀ i ∈ range p, 2^i * v' i j
            = 2^i * v'' i + (if i = 0 then (v' 0 j - a j) else 0) := by
          intro i _
          by_cases h : i = 0
          · subst h; simp [v'']; have := ha j; omega
          · simp [v'', h]
        rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq' (range p) 0, if_pos (mem_range.mpr hp)]
      rw [sum_range_succ']
      have e2 : ∑ i ∈ range p, 2^(i+1) * (if i + 1 = 0 then c + 2 * (v' 0 j - a j)
          else if i + 1 = 1 then a j else v' (i + 1 - 1) j) = 2 * ∑ i ∈ range p, 2^i * v'' i := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        by_cases h : i = 0
        · subst h; simp [v'']
        · simp only [v'', h, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            Nat.add_sub_cancel]
          have : i + 1 ≠ 1 := by omega
          rw [if_neg this, pow_succ]
          ring
      rw [e2]
      simp only [if_true, pow_zero, one_mul]
      omega

theorem cut_nec (q p C : ℕ) (n : ℕ → ℕ) (v : ℕ → Fin q → ℕ)
    (hrow : ∀ i < p, ∑ j, v i j = n i) (hbin : ∀ j, ∑ i ∈ range p, 2^i * v i j = C) (k : ℕ) :
    ∑ i ∈ Ico k p, n i * 2^(i-k) ≤ q * (C / 2^k) := by
  have hb : ∀ j, ∑ i ∈ Ico k p, 2^(i-k) * v i j ≤ C / 2^k := by
    intro j
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc (∑ i ∈ Ico k p, 2^(i-k) * v i j) * 2^k = ∑ i ∈ Ico k p, 2^i * v i j := by
          rw [sum_mul]
          apply sum_congr rfl
          intro i hi
          rw [mem_Ico] at hi
          have : 2^i = 2^(i-k) * 2^k := by rw [← pow_add]; congr 1; omega
          rw [this]
          ring
      _ ≤ ∑ i ∈ range p, 2^i * v i j := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro i hi
            rw [mem_Ico] at hi
            rw [mem_range]
            omega
          · intros; positivity
      _ = C := hbin j
  calc ∑ i ∈ Ico k p, n i * 2^(i-k) = ∑ j, ∑ i ∈ Ico k p, 2^(i-k) * v i j := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i hi
        rw [mem_Ico] at hi
        rw [← mul_sum, hrow i hi.2, mul_comm]
    _ ≤ ∑ _j : Fin q, C / 2^k := sum_le_sum fun j _ => hb j
    _ = q * (C / 2^k) := by simp

theorem geom (b : ℕ) : ∑ i ∈ range b, 2^i + 1 = 2^b := by
  induction b with
  | zero => simp
  | succ b ih => rw [sum_range_succ, pow_succ]; omega

theorem cutE (E k p : ℕ) (hk : k ≤ p) :
    ∑ i ∈ Ico k p, E * 2^(i-k) + E = E * 2^(p-k) := by
  rw [sum_Ico_eq_sum_range, ← geom (p-k), mul_add, mul_sum, mul_one]
  congr 1
  apply sum_congr rfl
  intro i _
  congr 2
  omega

theorem cut_iff (q E p D k : ℕ) (hq : 1 < q) (hE : E < q) (hD : 2^p = q * D + 1)
    (hk1 : 1 ≤ k) (hkp : k ≤ p) :
    (∑ i ∈ Ico k p, E * 2^(i-k) ≤ q * (D * E / 2^k)) ↔ (2^(p-k) * E) % q ≤ E := by
  set b := p - k with hb
  set A := 2^b * E / q
  set r := 2^b * E % q
  have hAr : 2^b * E = q * A + r := (Nat.div_add_mod _ _).symm
  have hrq : r < q := Nat.mod_lt _ (by omega)
  have hpk : 2^p = 2^k * 2^b := by rw [← pow_add]; congr 1; omega
  have hmain : q * (D * E) + E = 2^k * (q * A + r) := by
    rw [← hAr, show 2^k * (2^b * E) = 2^p * E by rw [hpk]; ring, hD]; ring
  have hmod1 : (2^p) % q = 1 % q := by
    rw [hD, Nat.mul_add_mod]
  have hErk : E ≤ 2^k * r := by
    have h1 : (2^k * r) % q = E % q := by
      have e1 : (2^k * r) % q = (2^k * (2^b * E)) % q := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [e1, ← mul_assoc, ← hpk, Nat.mul_mod, hmod1, ← Nat.mul_mod, one_mul]
    rw [Nat.mod_eq_of_lt hE] at h1
    rw [← h1]
    exact Nat.mod_le _ _
  have hpos : 0 < 2^k := by positivity
  have hdiv : D * E / 2^k = A := by
    apply Nat.div_eq_of_lt_le
    · apply Nat.le_of_mul_le_mul_left _ (show 0 < q by omega)
      nlinarith
    · apply Nat.lt_of_mul_lt_mul_left (a := q)
      have : 2^k * r < 2^k * q := Nat.mul_lt_mul_of_pos_left hrq hpos
      nlinarith
  have hc := cutE E k p hkp
  rw [hdiv]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end PEqualNP.Outside.L_lib_828

open PEqualNP.Outside.L_lib_828 Finset in
theorem PEqualNP.Outside.L_lib_828 : ∀ (q E p : ℕ), 1 < q → 0 < E → E < q → 0 < p → 2^p % q = 1 →
  ((∃ v : Fin p → Fin q → ℕ,
    (∀ i, (∑ j, v i j) = E) ∧
    ∀ j, q*(∑ i : Fin p, 2^i.val * v i j) = (2^p-1)*E) ↔
   ∀ b < p, (2^b*E) % q ≤ E) := by
  intro q E p hq hE hEq hp hmod
  set D := 2^p / q
  have hD : 2^p = q * D + 1 := by
    have := (Nat.div_add_mod (2^p) q).symm
    rw [hmod] at this
    exact this
  have hM : (2^p - 1) * E = q * (D * E) := by rw [hD]; simp [mul_assoc]
  have hq0 : 0 < q := by omega
  constructor
  · rintro ⟨v, hrow, hbin⟩ b hb
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simp [Nat.mod_eq_of_lt hEq]
    let V : ℕ → Fin q → ℕ := fun i j => if h : i < p then v ⟨i, h⟩ j else 0
    have hrowV : ∀ i < p, ∑ j, V i j = E := by
      intro i hi
      simp only [V, dif_pos hi]
      exact hrow _
    have hbinV : ∀ j, ∑ i ∈ range p, 2^i * V i j = D * E := by
      intro j
      have h := hbin j
      rw [hM] at h
      have h2 := Nat.eq_of_mul_eq_mul_left hq0 h
      rw [← h2, ← Fin.sum_univ_eq_sum_range (fun i => 2^i * V i j) p]
      apply sum_congr rfl
      intro i _
      simp [V, i.isLt]
    have hc := cut_nec q p (D * E) (fun _ => E) V hrowV hbinV (p - b)
    have h3 := (cut_iff q E p D (p - b) hq hEq hD (by omega) (by omega)).mp hc
    have : p - (p - b) = b := by omega
    rwa [this] at h3
  · intro hres
    have htot : ∑ i ∈ range p, (fun _ => E) i * 2^i = q * (D * E) := by
      rw [← mul_sum, ← hM, ← geom p, Nat.add_sub_cancel, mul_comm]
    have hcut : ∀ k, ∑ i ∈ Ico k p, (fun _ => E) i * 2^(i-k) ≤ q * (D * E / 2^k) := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [Nat.sub_zero, pow_zero, Nat.div_one]
        rw [← Finset.range_eq_Ico]
        exact le_of_eq htot
      · by_cases hkp : p ≤ k
        · rw [Ico_eq_empty (by omega)]
          simp
        · exact (cut_iff q E p D k hq hEq hD hk (by omega)).mpr (hres _ (by omega))
    obtain ⟨V, hrowV, hbinV⟩ := pack q hq0 p (D * E) (fun _ => E) htot hcut
    refine ⟨fun i j => V i j, fun i => hrowV i i.isLt, fun j => ?_⟩
    rw [hM, Fin.sum_univ_eq_sum_range (fun i => 2^i * V i j) p, hbinV j]
