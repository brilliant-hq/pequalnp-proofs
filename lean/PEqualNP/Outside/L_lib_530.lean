import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_530_aux

def ext (u : List Bool) (k : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (List.Vector Bool k)).image (fun v => u ++ v.1)

lemma card_ext (u : List Bool) (k : ℕ) : (ext u k).card = 2 ^ k := by
  unfold ext
  rw [Finset.card_image_of_injective]
  · simp
  · intro v w h
    exact Subtype.ext (List.append_cancel_left h)

lemma mem_ext {u : List Bool} {k : ℕ} {w : List Bool} (t : List Bool) (ht : t.length = k)
    (h : w = u ++ t) : w ∈ ext u k := by
  unfold ext
  exact Finset.mem_image.2 ⟨⟨t, ht⟩, Finset.mem_univ _, h.symm⟩

lemma kraft_conv {ι : Type} [DecidableEq ι] (l : ι → ℕ) (s : Finset ι) :
    (∑ i ∈ s, ((1:ℝ)/2)^(l i)) ≤ 1 →
      ∃ c : ι → List Bool, (∀ i ∈ s, (c i).length = l i) ∧
        ∀ i ∈ s, ∀ j ∈ s, c i <+: c j → i = j := by
  induction s using Finset.induction_on_max_value l with
  | empty => intro _; exact ⟨fun _ => [], by simp⟩
  | insert a s ha hmax ih =>
    intro hsum
    rw [Finset.sum_insert ha] at hsum
    have hpos : (0:ℝ) < (1/2)^(l a) := by positivity
    obtain ⟨c, hlen, hpf⟩ := ih (by linarith)
    have hw : ∃ w : List Bool, w.length = l a ∧ ∀ i ∈ s, ¬ c i <+: w := by
      by_contra hcon
      push_neg at hcon
      have hsub : ext [] (l a) ⊆ s.biUnion (fun i => ext (c i) (l a - l i)) := by
        intro w hw
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw
        obtain ⟨i, hi, t, ht⟩ := hcon ([] ++ v.1) (by simp)
        refine Finset.mem_biUnion.2 ⟨i, hi, mem_ext t ?_ ht.symm⟩
        have h1 := congrArg List.length ht
        have h2 := hlen i hi
        have h3 := v.2
        simp at h1
        omega
      have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      rw [card_ext] at hcard
      simp only [card_ext] at hcard
      have hreal : ((2:ℝ)^(l a)) ≤ ∑ i ∈ s, (2:ℝ)^(l a - l i) := by exact_mod_cast hcard
      have hterm : ∀ i ∈ s, (2:ℝ)^(l a - l i) = 2^(l a) * (1/2)^(l i) := by
        intro i hi
        have h1 : (2:ℝ)^(l a) = 2^(l a - l i) * 2^(l i) := by
          rw [← pow_add, Nat.sub_add_cancel (hmax i hi)]
        rw [h1, one_div, inv_pow]
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hreal
      have h2 : (0:ℝ) < 2^(l a) := by positivity
      have h3 : (2:ℝ)^(l a) * (1/2)^(l a) = 1 := by
        rw [one_div, inv_pow]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left hsum h2.le]
    obtain ⟨w, hwl, hwn⟩ := hw
    refine ⟨Function.update c a w, ?_, ?_⟩
    · intro i hi
      by_cases h : i = a
      · subst h; simp [hwl]
      · rw [Function.update_of_ne h]
        exact hlen i ((Finset.mem_insert.1 hi).resolve_left h)
    · intro i hi j hj hp
      by_cases hia : i = a
      · by_cases hja : j = a
        · rw [hia, hja]
        · exfalso
          subst hia
          rw [Function.update_self, Function.update_of_ne hja] at hp
          have hjs : j ∈ s := (Finset.mem_insert.1 hj).resolve_left hja
          have h1 := hp.length_le
          have h2 := hlen j hjs
          have h3 := hmax j hjs
          have h4 : w = c j := hp.eq_of_length (by omega)
          exact hwn j hjs (h4 ▸ List.prefix_refl _)
      · have his : i ∈ s := (Finset.mem_insert.1 hi).resolve_left hia
        by_cases hja : j = a
        · exfalso
          subst hja
          rw [Function.update_self, Function.update_of_ne hia] at hp
          exact hwn i his hp
        · have hjs : j ∈ s := (Finset.mem_insert.1 hj).resolve_left hja
          rw [Function.update_of_ne hia, Function.update_of_ne hja] at hp
          exact hpf i his j hjs hp

lemma shannon_len (x : ℝ) (hx : 1 ≤ x) : ∃ n : ℕ, x ≤ 2^n ∧ (2:ℝ)^n < 2 * x := by
  classical
  have H : ∃ n : ℕ, x ≤ (2:ℝ)^n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (one_lt_two (α := ℝ))
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find H, Nat.find_spec H, ?_⟩
  rcases hn : Nat.find H with _ | k
  · simp; linarith
  · have h1 : ¬ x ≤ (2:ℝ)^k := Nat.find_min H (by omega)
    rw [pow_succ]
    linarith

end PEqualNP.Outside.L_lib_530_aux

open PEqualNP.Outside.L_lib_530_aux in
theorem PEqualNP.Outside.L_lib_530 :
    ∀ (m h : ℕ) (p : Fin h → Fin m → ℝ) (e : Fin m → ℝ), 0 < m → 0 < h →
  (∀ j i, 0 < p j i) → (∀ j, (∑ i, p j i) = 1) →
  (∀ i, (∀ j, p j i ≤ e i) ∧ ∃ j, p j i = e i) →
  let prefixCode := fun (code : Fin m → List Bool) =>
    ∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j
  let Z := ∑ i, e i
  (∀ i j, p j i ≤ Z*(e i/Z)) ∧ (∑ i, e i/Z) = 1 ∧
  (∀ q : Fin m → ℝ, (∀ i, 0 < q i) → (∑ i, q i) = 1 →
    ∃ i j, Z*q i ≤ p j i) ∧
  (∀ c, prefixCode c → ∃ i j, Z ≤ p j i * (2:ℝ)^(c i).length) ∧
  ∃ c, prefixCode c ∧ ∀ i j, p j i * (2:ℝ)^(c i).length < 2*Z := by
  intro m h p e hm hh hp hsum he prefixCode Z
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hepos : ∀ i, 0 < e i := fun i => by
    obtain ⟨j, hj⟩ := (he i).2
    rw [← hj]; exact hp j i
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => hepos i) Finset.univ_nonempty
  have heZ : ∀ i, e i ≤ Z := fun i =>
    Finset.single_le_sum (f := e) (fun k _ => (hepos k).le) (Finset.mem_univ i)
  have hnorm : (∑ i, e i/Z) = 1 := by
    rw [← Finset.sum_div]; exact div_self hZ.ne'
  refine ⟨?_, hnorm, ?_, ?_, ?_⟩
  · intro i j
    rw [mul_div_cancel₀ _ hZ.ne']
    exact (he i).1 j
  · intro q hq hq1
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ i, e i < ∑ i, Z * q i := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      obtain ⟨j, hj⟩ := (he i).2
      rw [← hj]; exact hcon i j
    rw [← Finset.mul_sum, hq1, mul_one] at hlt
    exact lt_irrefl _ hlt
  · intro c hc
    by_contra hcon
    push_neg at hcon
    have hinj : Function.Injective c := fun i j hij => hc i j ⟨[], by simp [hij]⟩
    have hfree : InformationTheory.IsPrefixFree
        ((Finset.univ.image c : Finset (List Bool)) : Set (List Bool)) := by
      intro x hx y hy hxy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      obtain ⟨t, ht⟩ := hxy
      rw [hc i j ⟨t, ht.symm⟩]
    have hk := hfree.finsetSum_one_div_card_pow_length_le_one
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)] at hk
    simp only [Fintype.card_bool, Nat.cast_ofNat] at hk
    have hlt : ∑ i, e i < ∑ i, Z * ((1:ℝ)/2)^(c i).length := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      obtain ⟨j, hj⟩ := (he i).2
      have h1 := hcon i j
      rw [hj] at h1
      have h2 : (0:ℝ) < 2^(c i).length := by positivity
      rw [one_div, inv_pow, ← div_eq_mul_inv, lt_div_iff₀ h2]
      exact h1
    rw [← Finset.mul_sum] at hlt
    have : Z * ∑ i, ((1:ℝ)/2)^(c i).length ≤ Z * 1 := mul_le_mul_of_nonneg_left hk hZ.le
    change Z < _ at hlt
    linarith
  · have hx : ∀ i, 1 ≤ Z / e i := fun i => by
      rw [le_div_iff₀ (hepos i)]; linarith [heZ i]
    choose l hl1 hl2 using fun i => shannon_len (Z / e i) (hx i)
    have hks : (∑ i ∈ (Finset.univ : Finset (Fin m)), ((1:ℝ)/2)^(l i)) ≤ 1 := by
      refine le_of_le_of_eq (Finset.sum_le_sum ?_) hnorm
      intro i _
      have h2 : (0:ℝ) < 2^(l i) := by positivity
      rw [one_div, inv_pow, ← one_div, div_le_div_iff₀ h2 hZ]
      have := hl1 i
      rw [div_le_iff₀ (hepos i)] at this
      linarith
    obtain ⟨c, hlen, hpf⟩ := kraft_conv l Finset.univ hks
    refine ⟨c, ?_, ?_⟩
    · intro i j hij
      obtain ⟨t, ht⟩ := hij
      exact hpf i (Finset.mem_univ _) j (Finset.mem_univ _) ⟨t, ht.symm⟩
    · intro i j
      rw [hlen i (Finset.mem_univ _)]
      have h2 : (0:ℝ) < 2^(l i) := by positivity
      have h3 : e i * 2^(l i) < e i * (2 * (Z / e i)) :=
        mul_lt_mul_of_pos_left (hl2 i) (hepos i)
      have h4 : e i * (2 * (Z / e i)) = 2 * Z := by
        field_simp [(hepos i).ne']
      have h5 : p j i * 2^(l i) ≤ e i * 2^(l i) :=
        mul_le_mul_of_nonneg_right ((he i).1 j) h2.le
      linarith
