import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_532_aux

lemma cell (x t s : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h : 0 < x → 0 < t ∧ 0 < s) :
    -x * Real.log (x/t) ≤ t*s-x-x*Real.log s := by
  rcases hx.eq_or_lt with he | hp
  · subst x; simpa using mul_nonneg ht hs
  · obtain ⟨ht', hs'⟩ := h hp
    have hz := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos (mul_pos ht' hs') hp)) hp.le
    rw [Real.log_div (mul_pos ht' hs').ne' hp.ne', Real.log_mul ht'.ne' hs'.ne'] at hz
    rw [Real.log_div hp.ne' ht'.ne']
    have hk : t*s/x*x = t*s := div_mul_cancel₀ _ hp.ne'
    nlinarith

end PEqualNP.Outside.L_lib_532_aux

theorem PEqualNP.Outside.L_lib_532 : ∀ (m h : ℕ) (p : Fin h → Fin m → ℝ) (dec : Fin h → Fin m),
  2 ≤ m → (∀ y i, 0 ≤ p y i) → (∑ y, ∑ i, p y i) = 1 →
  let mass := fun y => ∑ i, p y i
  let e := ∑ y, ∑ i, if dec y = i then (0:ℝ) else p y i
  let H := ∑ y, ∑ i, -(p y i) * Real.log (p y i / mass y)
  H ≤ -e*Real.log e - (1-e)*Real.log (1-e) + e*Real.log ((m:ℝ)-1) := by
  classical
  intro m h p dec hm hp htot mass e H
  let err := fun y i => if dec y = i then (0:ℝ) else p y i
  let ok := fun y i => if dec y = i then p y i else 0
  have he0 : ∀ y i, 0 ≤ err y i := by intro y i; dsimp [err]; split <;> simp [hp]
  have ho0 : ∀ y i, 0 ≤ ok y i := by intro y i; dsimp [ok]; split <;> simp [hp]
  have hbnd (f : Fin h → Fin m → ℝ) (hf : ∀ y i, 0 ≤ f y i) (y i) : f y i ≤ ∑ y, ∑ i, f y i :=
    (Finset.single_le_sum (f := f y) (fun j _ => hf y j) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, f k j) (fun k _ => Finset.sum_nonneg fun j _ => hf k j) (Finset.mem_univ y))
  have hsum : (∑ y, ∑ i, ok y i) = 1-e := by
    apply eq_sub_of_add_eq
    change (∑ y, ∑ i, ok y i) + (∑ y, ∑ i, err y i) = 1
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    have splitcell (y i) : ok y i + err y i = p y i := by by_cases hc : dec y = i <;> simp [ok, err, hc]
    simpa only [splitcell] using (show (∑ y, ∑ i, p y i) = 1 from htot)
  have he : 0 ≤ e := Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => he0 y i
  have ha : 0 ≤ 1-e := by rw [← hsum]; exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => ho0 y i
  have hd : 0 < (m:ℝ)-1 := by apply sub_pos.mpr; exact_mod_cast (show 1 < m by omega)
  let b := e/((m:ℝ)-1)
  let s := fun y i => if dec y = i then 1-e else b
  have hs (y i) : 0 ≤ s y i := by dsimp [s]; split; exact ha; exact div_nonneg he hd.le
  have hnorm (y) : (∑ i, s y i) = 1 := by
    have hrewrite (i) : s y i = (if dec y = i then (1-e-b) else 0) + b := by dsimp [s]; split <;> ring
    simp_rw [hrewrite, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [b]; field_simp [hd.ne']; ring
  have hcell (y i) := PEqualNP.Outside.L_lib_532_aux.cell (p y i) (mass y) (s y i) (hp y i)
    (Finset.sum_nonneg fun j _ => hp y j) (hs y i) (by
      intro hpos
      refine ⟨lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => hp y j) (Finset.mem_univ i)), ?_⟩
      by_cases hc : dec y = i
      · have hk := hbnd ok ho0 y i
        rw [hsum] at hk
        simpa [s, hc] using (lt_of_lt_of_le hpos (by simpa [ok, hc] using hk) : 0 < 1-e)
      · have hk : p y i ≤ e := by simpa only [err, if_neg hc] using hbnd err he0 y i
        simpa [s, hc, b] using div_pos (hpos.trans_le hk) hd)
  have hcost (y i) : p y i * Real.log (s y i) = ok y i * Real.log (1-e) + err y i * Real.log b := by
    by_cases hc : dec y = i <;> simp [s, ok, err, hc]
  have hc := Finset.sum_le_sum (s := Finset.univ) fun y _ => Finset.sum_le_sum (s := Finset.univ) fun i _ => hcell y i
  simp_rw [hcost, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hnorm, mul_one] at hc
  change H ≤ (∑ y, mass y) - (∑ y, mass y) - ((∑ y, ∑ i, ok y i)*Real.log (1-e) + e*Real.log b) at hc
  rw [hsum] at hc
  by_cases hz : e = 0
  · simpa [hz] using hc
  · rw [show Real.log b = Real.log e - Real.log ((m:ℝ)-1) from Real.log_div hz hd.ne'] at hc
    linarith
