import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27440

open PEqualNP.CircuitLowerBounds

def pm (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def flip (t : Fin 9) (z : Fin 9 → Bool) : Fin 9 → Bool := fun i => if i = t then !z i else z i

def zw (l : List ℕ) : Fin 9 → Bool := fun i => decide (i.val ∈ l)

theorem flip_ne {t i : Fin 9} (z : Fin 9 → Bool) (h : i ≠ t) : flip t z i = z i := by
  simp [flip, h]

theorem flip_flip (t : Fin 9) (z : Fin 9 → Bool) : flip t (flip t z) = z := by
  funext i
  unfold flip
  by_cases h : i = t <;> simp [h]

def GateSpec (W : ℕ → (Fin 9 → Bool) → Bool) (inp : ℕ → List ℕ) (j : ℕ) : Prop :=
  (∃ a, a < 9 + j ∧ inp j = [a] ∧ ∀ x, W (9 + j) x = !W a x) ∨
  (∃ a b, a < b ∧ b < 9 + j ∧ inp j = [a, b] ∧
    ((∀ x, W (9 + j) x = (W a x && W b x)) ∨ (∀ x, W (9 + j) x = (W a x || W b x))))

def D (s : ℕ) (inp : ℕ → List ℕ) (t k : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P t → (∀ j, j < s → ∀ a, a ∈ inp j → P a → P (9 + j)) → P k

def Tight (s : ℕ) (inp : ℕ → List ℕ) : Prop :=
  ∀ w, 3 ≤ w → ∀ j j', j < s → j' < s → w ∈ inp j → w ∈ inp j' → j = j'

def Meet (s : ℕ) (inp : ℕ → List ℕ) (u v G : ℕ) : Prop :=
  D s inp u G ∧ D s inp v G ∧ ∀ k, k < G → ¬ (D s inp u k ∧ D s inp v k)

theorem bh_and1 : ∀ A A' B : Bool, (A && B) ≠ (A' && B) → B = true := by decide
theorem bh_and2 : ∀ A B B' : Bool, (A && B) ≠ (A && B') → A = true := by decide
theorem bh_or1 : ∀ A A' B : Bool, (A || B) ≠ (A' || B) → B = false := by decide
theorem bh_or2 : ∀ A B B' : Bool, (A || B) ≠ (A || B') → A = false := by decide
theorem p_and_l : ∀ A A' C g p : Bool, (A && C) ≠ (A' && C) → (A ≠ A' → A = xor g p) →
    (A && C) = xor g p := by decide
theorem p_and_r : ∀ A A' C g p : Bool, (C && A) ≠ (C && A') → (A ≠ A' → A = xor g p) →
    (C && A) = xor g p := by decide
theorem p_or_l : ∀ A A' C g p : Bool, (A || C) ≠ (A' || C) → (A ≠ A' → A = xor g p) →
    (A || C) = xor g p := by decide
theorem p_or_r : ∀ A A' C g p : Bool, (C || A) ≠ (C || A') → (A ≠ A' → A = xor g p) →
    (C || A) = xor g p := by decide
theorem p_not : ∀ A A' g p : Bool, (!A) ≠ (!A') → (A ≠ A' → A = xor g p) →
    (!A) = xor g (!p) := by decide

theorem len_le (g : ℕ → List ℕ) : ∀ n, (∀ j, j < n → (g j).length ≤ 2) →
    ((List.range n).flatMap g).length ≤ 2 * n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

theorem len_lt (g : ℕ → List ℕ) : ∀ n, (∀ j, j < n → (g j).length ≤ 2) →
    ∀ j0, j0 < n → (g j0).length ≤ 1 → ((List.range n).flatMap g).length + 1 ≤ 2 * n := by
  intro n
  induction n with
  | zero => intro _ j0 h; omega
  | succ n ih =>
    intro h j0 hj0 h1
    have h2 := h n (by omega)
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases e : j0 = n
    · subst e
      have := len_le g j0 (fun j hj => h j (by omega))
      omega
    · have := ih (fun j hj => h j (by omega)) j0 (by omega) h1
      omega

theorem nodup_of_card (L : List ℕ) (h : L.length ≤ L.toFinset.card) : L.Nodup := by
  rw [List.card_toFinset] at h
  have e : L.dedup = L := (List.dedup_sublist L).eq_of_length_le h
  rw [← e]
  exact List.nodup_dedup L

theorem tight_range (g : ℕ → List ℕ) : ∀ n, ((List.range n).flatMap g).Nodup →
    ∀ i j, i < n → j < n → ∀ w, w ∈ g i → w ∈ g j → i = j := by
  intro n
  induction n with
  | zero => intro _ i j hi; omega
  | succ n ih =>
    intro h i j hi hj w hwi hwj
    rw [List.range_succ, List.flatMap_append] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
    have hd := List.disjoint_of_nodup_append h
    have hn := h.of_append_left
    have key : ∀ i, i < n → ∀ w, w ∈ g i → w ∈ g n → False := fun i hi w h1 h2 =>
      hd (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h1⟩) h2
    by_cases ei : i = n <;> by_cases ej : j = n
    · omega
    · subst ei
      exact (key j (by omega) w hwj hwi).elim
    · subst ej
      exact (key i (by omega) w hwi hwj).elim
    · exact ih hn i j (by omega) (by omega) w hwi hwj

def reads (s : ℕ) (inp : ℕ → List ℕ) : List ℕ := (List.range (s - 2)).flatMap (fun j => inp (j + 2))

section core
variable {s : ℕ} {W : ℕ → (Fin 9 → Bool) → Bool} {inp : ℕ → List ℕ}

theorem inp_lt (hg : ∀ j, j < s → GateSpec W inp j) {j a : ℕ} (hj : j < s) (ha : a ∈ inp j) :
    a < 9 + j := by
  rcases hg j hj with ⟨a0, h1, h2, _⟩ | ⟨a0, b0, h1, h2, h3, _⟩
  · rw [h2] at ha; simp at ha; omega
  · rw [h3] at ha; simp at ha; omega

theorem inp_len (hg : ∀ j, j < s → GateSpec W inp j) {j : ℕ} (hj : j < s) :
    (inp j).length ≤ 2 := by
  rcases hg j hj with ⟨a0, h1, h2, _⟩ | ⟨a0, b0, h1, h2, h3, _⟩
  · rw [h2]; simp
  · rw [h3]; simp

theorem D_refl {t : ℕ} : D s inp t t := fun _ h _ => h

theorem D_step {t j a : ℕ} (hj : j < s) (ha : a ∈ inp j) (hd : D s inp t a) :
    D s inp t (9 + j) := fun P h0 hs => hs j hj a ha (hd P h0 hs)

theorem D_lt9 {t k : ℕ} (hd : D s inp t k) (hk : k < 9) : k = t :=
  hd (fun k => k < 9 → k = t) (fun _ => rfl) (fun j _ a _ _ h => by omega) hk

theorem D_bound {t k : ℕ} (hd : D s inp t k) (ht : t < 9) : k < 9 + s :=
  hd (fun k => k < 9 + s) (by omega) (fun j hj a _ _ => by omega)

theorem D_ge3 {t k : ℕ} (hd : D s inp t k) (ht : 3 ≤ t) : 3 ≤ k :=
  hd (fun k => 3 ≤ k) ht (fun j _ _ _ _ => by omega)

theorem D_gate {t k : ℕ} (hd : D s inp t k) (ht : t < 9) (hk : 9 ≤ k) :
    ∃ a, a ∈ inp (k - 9) ∧ D s inp t a := by
  have h : D s inp t k ∧ (9 ≤ k → ∃ a, a ∈ inp (k - 9) ∧ D s inp t a) :=
    hd (fun k => D s inp t k ∧ (9 ≤ k → ∃ a, a ∈ inp (k - 9) ∧ D s inp t a))
      ⟨D_refl, fun h => by omega⟩
      (fun j hj a ha hp => ⟨D_step hj ha hp.1, fun _ => ⟨a, by simpa using ha, hp.1⟩⟩)
  exact h.2 hk

theorem D_gate' {t j : ℕ} (hd : D s inp t (9 + j)) (ht : t < 9) :
    ∃ a, a ∈ inp j ∧ D s inp t a := by
  obtain ⟨a, ha, hda⟩ := D_gate hd ht (by omega)
  exact ⟨a, by simpa using ha, hda⟩

theorem indep (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (t : Fin 9) :
    ∀ k, k < 9 + s → ¬ D s inp t.val k → ∀ z, W k z = W k (flip t z) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hnd z
    by_cases h9 : k < 9
    · rw [hin k h9, hin k h9, flip_ne]
      intro h
      apply hnd
      subst h
      exact D_refl
    · obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
      have hj : j < s := by omega
      rcases hg j hj with ⟨a, ha, hi, hv⟩ | ⟨a, b, hab, hb, hi, hv⟩
      · have hda : ¬ D s inp t.val a := fun h => hnd (D_step hj (by rw [hi]; simp) h)
        rw [hv, hv, ih a (by omega) (by omega) hda z]
      · have hda : ¬ D s inp t.val a := fun h => hnd (D_step hj (by rw [hi]; simp) h)
        have hdb : ¬ D s inp t.val b := fun h => hnd (D_step hj (by rw [hi]; simp) h)
        have ea := ih a (by omega) (by omega) hda z
        have eb := ih b (by omega) (by omega) hdb z
        rcases hv with hv | hv <;> rw [hv, hv, ea, eb]

theorem dep_of_sens (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) {t : Fin 9} {k : ℕ} (hk : k < 9 + s)
    {z : Fin 9 → Bool} (h : W k z ≠ W k (flip t z)) : D s inp t.val k := by
  by_contra hd
  exact h (indep hin hg t k hk hd z)

theorem chain (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) {t : ℕ}
    (ht3 : 3 ≤ t) (ht9 : t < 9) :
    ∀ v u, u < v → D s inp t u → D s inp t v → ∃ j, j < s ∧ 9 + j ≤ v ∧ u ∈ inp j := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro u huv hu hv
    by_cases h9 : v < 9
    · have e1 := D_lt9 hv h9
      have e2 := D_lt9 hu (by omega)
      omega
    · obtain ⟨j0, rfl⟩ : ∃ j0, v = 9 + j0 := ⟨v - 9, by omega⟩
      have hj0 : j0 < s := by
        have := D_bound hv ht9
        omega
      obtain ⟨a, ha, hda⟩ := D_gate' hv ht9
      have halt := inp_lt hg hj0 ha
      rcases lt_trichotomy a u with h | h | h
      · obtain ⟨j1, hj1, hle, hmem⟩ := ih u huv a h hda hu
        have := htight a (D_ge3 hda ht3) j1 j0 hj1 hj0 hmem ha
        omega
      · subst h
        exact ⟨j0, hj0, le_refl _, ha⟩
      · obtain ⟨j1, hj1, hle, hmem⟩ := ih a halt u h hu hda
        exact ⟨j1, hj1, by omega, hmem⟩

theorem upper (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) {t t' : ℕ}
    (ht3 : 3 ≤ t) (ht9 : t < 9) {G : ℕ} (hG : D s inp t G) (hG' : D s inp t' G) :
    ∀ k, G ≤ k → D s inp t k → D s inp t' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hGk hk
    rcases Nat.eq_or_lt_of_le hGk with h | h
    · rw [← h]
      exact hG'
    · by_cases h9 : k < 9
      · have e1 := D_lt9 hk h9
        have e2 := D_lt9 hG (by omega)
        omega
      · obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
        have hj : j < s := by
          have := D_bound hk ht9
          omega
        obtain ⟨a, ha, hda⟩ := D_gate' hk ht9
        have halt := inp_lt hg hj ha
        by_cases hGa : G ≤ a
        · exact D_step hj ha (ih a halt hGa hda)
        · obtain ⟨j1, hj1, hle, hmem⟩ := chain hg htight ht3 ht9 G a (by omega) hda hG
          have := htight a (D_ge3 hda ht3) j1 j hj1 hj hmem ha
          omega

theorem uniq (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) {t : ℕ}
    (ht3 : 3 ≤ t) (ht9 : t < 9) {j a b : ℕ} (hj : j < s) (ha : a ∈ inp j) (hb : b ∈ inp j)
    (hab : a ≠ b) (hda : D s inp t a) : ¬ D s inp t b := by
  intro hdb
  have hla := inp_lt hg hj ha
  have hlb := inp_lt hg hj hb
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · obtain ⟨j1, hj1, hle, hmem⟩ := chain hg htight ht3 ht9 b a h hda hdb
    have := htight a (D_ge3 hda ht3) j1 j hj1 hj hmem ha
    omega
  · obtain ⟨j1, hj1, hle, hmem⟩ := chain hg htight ht3 ht9 a b h hdb hda
    have := htight b (D_ge3 hdb ht3) j1 j hj1 hj hmem hb
    omega

theorem pol (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) {t : Fin 9}
    (ht3 : 3 ≤ t.val) {G : ℕ} (hG : D s inp t.val G) :
    ∀ k, G ≤ k → D s inp t.val k → ∃ p : Bool, ∀ (z : Fin 9 → Bool) (t' : Fin 9),
      3 ≤ t'.val → D s inp t'.val G → W k z ≠ W k (flip t' z) → W k z = xor (W G z) p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hGk hk
    rcases Nat.eq_or_lt_of_le hGk with h | h
    · subst h
      exact ⟨false, fun z t' _ _ _ => by simp⟩
    · have h9 : ¬ k < 9 := by
        intro h9
        have e1 := D_lt9 hk h9
        have e2 := D_lt9 hG (by omega)
        omega
      obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
      have hj : j < s := by
        have := D_bound hk t.isLt
        omega
      obtain ⟨a, ha, hda⟩ := D_gate' hk t.isLt
      have halt := inp_lt hg hj ha
      have hGa : G ≤ a := by
        by_contra hGa
        obtain ⟨j1, hj1, hle, hmem⟩ := chain hg htight ht3 t.isLt G a (by omega) hda hG
        have := htight a (D_ge3 hda ht3) j1 j hj1 hj hmem ha
        omega
      obtain ⟨p, hp⟩ := ih a halt hGa hda
      have hother : ∀ c, c ∈ inp j → c ≠ a → ∀ (z : Fin 9 → Bool) (t' : Fin 9), 3 ≤ t'.val →
          D s inp t'.val G → W c z = W c (flip t' z) := by
        intro c hc hca z t' ht' hG'
        have hda' : D s inp t'.val a := upper hg htight ht3 t.isLt hG hG' a hGa hda
        have hnd : ¬ D s inp t'.val c :=
          uniq hg htight ht' t'.isLt hj ha hc (Ne.symm hca) hda'
        have hc9 := inp_lt hg hj hc
        exact indep hin hg t' c (by omega) hnd z
      rcases hg j hj with ⟨a0, h1, hi, hv⟩ | ⟨a0, b0, hab, hb, hi, hv⟩
      · have e : a = a0 := by
          rw [hi] at ha
          simpa using ha
        subst e
        refine ⟨!p, fun z t' ht' hG' hne => ?_⟩
        rw [hv z, hv (flip t' z)] at hne
        rw [hv z]
        exact p_not _ _ _ _ hne (hp z t' ht' hG')
      · have hb0 : b0 ∈ inp j := by rw [hi]; simp
        have ha0 : a0 ∈ inp j := by rw [hi]; simp
        have e : a = a0 ∨ a = b0 := by
          rw [hi] at ha
          simpa using ha
        refine ⟨p, fun z t' ht' hG' hne => ?_⟩
        rcases e with e | e
        · subst e
          have hc := hother b0 hb0 (by omega) z t' ht' hG'
          rcases hv with hv | hv
          · rw [hv z, hv (flip t' z), ← hc] at hne
            rw [hv z]
            exact p_and_l _ _ _ _ _ hne (hp z t' ht' hG')
          · rw [hv z, hv (flip t' z), ← hc] at hne
            rw [hv z]
            exact p_or_l _ _ _ _ _ hne (hp z t' ht' hG')
        · subst e
          have hc := hother a0 ha0 (by omega) z t' ht' hG'
          rcases hv with hv | hv
          · rw [hv z, hv (flip t' z), ← hc] at hne
            rw [hv z]
            exact p_and_r _ _ _ _ _ hne (hp z t' ht' hG')
          · rw [hv z, hv (flip t' z), ← hc] at hne
            rw [hv z]
            exact p_or_r _ _ _ _ _ hne (hp z t' ht' hG')

theorem meet_exists {u v o : ℕ} (hu : D s inp u o) (hv : D s inp v o) :
    ∃ G, Meet s inp u v G := by
  classical
  have h : ∃ k, D s inp u k ∧ D s inp v k := ⟨o, hu, hv⟩
  exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, fun k hk => Nat.find_min h hk⟩

theorem meet_symm {u v G : ℕ} (h : Meet s inp u v G) : Meet s inp v u G :=
  ⟨h.2.1, h.1, fun k hk hh => h.2.2 k hk ⟨hh.2, hh.1⟩⟩

theorem ultra (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) {u v w : ℕ}
    (hv3 : 3 ≤ v) (hv9 : v < 9) {G1 G2 G3 : ℕ} (h1 : Meet s inp u v G1)
    (h2 : Meet s inp v w G2) (h3 : Meet s inp u w G3) : G3 ≤ G1 ∨ G3 ≤ G2 := by
  rcases le_total G1 G2 with h | h
  · right
    have hu : D s inp u G2 := upper hg htight hv3 hv9 h1.2.1 h1.1 G2 h h2.1
    by_contra hc
    exact h3.2.2 G2 (by omega) ⟨hu, h2.2.1⟩
  · left
    have hw : D s inp w G1 := upper hg htight hv3 hv9 h2.1 h2.2.1 G1 h h1.2.1
    by_contra hc
    exact h3.2.2 G1 (by omega) ⟨h1.1, hw⟩

theorem meet_ge9 {u v G : ℕ} (huv : u ≠ v) (hm : Meet s inp u v G) : 9 ≤ G := by
  by_contra h
  have h1 := D_lt9 hm.1 (by omega)
  have h2 := D_lt9 hm.2.1 (by omega)
  omega

theorem meet_inputs {u v j : ℕ} (hu9 : u < 9) (hv9 : v < 9) (hm : Meet s inp u v (9 + j))
    (hlt : ∀ a, a ∈ inp j → a < 9 + j) :
    ∃ a b, a ∈ inp j ∧ b ∈ inp j ∧ D s inp u a ∧ ¬ D s inp v a ∧ D s inp v b ∧ ¬ D s inp u b := by
  obtain ⟨a, ha, hda⟩ := D_gate' hm.1 hu9
  obtain ⟨b, hb, hdb⟩ := D_gate' hm.2.1 hv9
  exact ⟨a, b, ha, hb, hda, fun h => hm.2.2 a (hlt a ha) ⟨hda, h⟩, hdb,
    fun h => hm.2.2 b (hlt b hb) ⟨h, hdb⟩⟩

theorem meet_not (hg : ∀ j, j < s → GateSpec W inp j) {u v : Fin 9} {j : ℕ} (hj : j < s)
    (hm : Meet s inp u.val v.val (9 + j)) {a0 : ℕ} (hi : inp j = [a0]) : False := by
  obtain ⟨a, b, ha, hb, hda, hnva, hdb, hnub⟩ :=
    meet_inputs u.isLt v.isLt hm (fun a ha => inp_lt hg hj ha)
  rw [hi] at ha hb
  simp at ha hb
  subst ha
  subst hb
  exact hnva hdb

theorem meet_val_and (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) {u v : Fin 9} {j : ℕ} (hj : j < s)
    (hm : Meet s inp u.val v.val (9 + j)) {a0 b0 : ℕ} (hi : inp j = [a0, b0])
    (hv : ∀ x, W (9 + j) x = (W a0 x && W b0 x)) (z : Fin 9 → Bool)
    (h1 : W (9 + j) z ≠ W (9 + j) (flip u z)) (h2 : W (9 + j) z ≠ W (9 + j) (flip v z)) :
    W (9 + j) z = true := by
  obtain ⟨a, b, ha, hb, hda, hnva, hdb, hnub⟩ :=
    meet_inputs u.isLt v.isLt hm (fun a ha => inp_lt hg hj ha)
  have hla := inp_lt hg hj ha
  have hlb := inp_lt hg hj hb
  have ea := indep hin hg v a (by omega) hnva z
  have eb := indep hin hg u b (by omega) hnub z
  rw [hi] at ha hb
  simp at ha hb
  rw [hv z, hv (flip u z)] at h1
  rw [hv z, hv (flip v z)] at h2
  rw [hv z]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · subst ha; subst hb; exact absurd hdb hnva
  · subst ha; subst hb
    rw [← eb] at h1
    rw [← ea] at h2
    rw [bh_and1 _ _ _ h1, bh_and2 _ _ _ h2]
    rfl
  · subst ha; subst hb
    rw [← eb] at h1
    rw [← ea] at h2
    rw [bh_and2 _ _ _ h1, bh_and1 _ _ _ h2]
    rfl
  · subst ha; subst hb; exact absurd hdb hnva

theorem meet_val_or (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) {u v : Fin 9} {j : ℕ} (hj : j < s)
    (hm : Meet s inp u.val v.val (9 + j)) {a0 b0 : ℕ} (hi : inp j = [a0, b0])
    (hv : ∀ x, W (9 + j) x = (W a0 x || W b0 x)) (z : Fin 9 → Bool)
    (h1 : W (9 + j) z ≠ W (9 + j) (flip u z)) (h2 : W (9 + j) z ≠ W (9 + j) (flip v z)) :
    W (9 + j) z = false := by
  obtain ⟨a, b, ha, hb, hda, hnva, hdb, hnub⟩ :=
    meet_inputs u.isLt v.isLt hm (fun a ha => inp_lt hg hj ha)
  have hla := inp_lt hg hj ha
  have hlb := inp_lt hg hj hb
  have ea := indep hin hg v a (by omega) hnva z
  have eb := indep hin hg u b (by omega) hnub z
  rw [hi] at ha hb
  simp at ha hb
  rw [hv z, hv (flip u z)] at h1
  rw [hv z, hv (flip v z)] at h2
  rw [hv z]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · subst ha; subst hb; exact absurd hdb hnva
  · subst ha; subst hb
    rw [← eb] at h1
    rw [← ea] at h2
    rw [bh_or1 _ _ _ h1, bh_or2 _ _ _ h2]
    rfl
  · subst ha; subst hb
    rw [← eb] at h1
    rw [← ea] at h2
    rw [bh_or2 _ _ _ h1, bh_or1 _ _ _ h2]
    rfl
  · subst ha; subst hb; exact absurd hdb hnva

theorem key (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) (hs : 1 ≤ s)
    {u v u' v' : Fin 9} (hu : 3 ≤ u.val) (hv : 3 ≤ v.val) (hu' : 3 ≤ u'.val) (hv' : 3 ≤ v'.val)
    (huv : u.val ≠ v.val) {G : ℕ}
    (hm : Meet s inp u.val v.val G) (hm' : Meet s inp u'.val v'.val G) {z z' : Fin 9 → Bool}
    (h1 : W (9 + s - 1) z ≠ W (9 + s - 1) (flip u z))
    (h2 : W (9 + s - 1) z ≠ W (9 + s - 1) (flip v z))
    (h1' : W (9 + s - 1) z' ≠ W (9 + s - 1) (flip u' z'))
    (h2' : W (9 + s - 1) z' ≠ W (9 + s - 1) (flip v' z')) :
    W (9 + s - 1) z = W (9 + s - 1) z' := by
  have ho : 9 + s - 1 < 9 + s := by omega
  have hDu : D s inp u.val (9 + s - 1) := dep_of_sens hin hg ho h1
  have hDv : D s inp v.val (9 + s - 1) := dep_of_sens hin hg ho h2
  have hGo : G ≤ 9 + s - 1 := by
    by_contra h
    exact hm.2.2 (9 + s - 1) (by omega) ⟨hDu, hDv⟩
  obtain ⟨p, hp⟩ := pol hin hg htight hu hm.1 (9 + s - 1) hGo hDu
  have sens : ∀ (t' : Fin 9), 3 ≤ t'.val → D s inp t'.val G → ∀ y : Fin 9 → Bool,
      W (9 + s - 1) y ≠ W (9 + s - 1) (flip t' y) →
      W (9 + s - 1) y = xor (W G y) p ∧ W G y ≠ W G (flip t' y) := by
    intro t' ht' hd y hne
    have e1 := hp y t' ht' hd hne
    have e2 := hp (flip t' y) t' ht' hd (by rw [flip_flip]; exact fun e => hne e.symm)
    refine ⟨e1, fun e => hne ?_⟩
    rw [e1, e2, e]
  have hG9 := meet_ge9 huv hm
  obtain ⟨j, rfl⟩ : ∃ j, G = 9 + j := ⟨G - 9, by omega⟩
  have hj : j < s := by
    have := D_bound hm.1 u.isLt
    omega
  have s1 := sens u hu hm.1 z h1
  have s2 := sens v hv hm.2.1 z h2
  have s1' := sens u' hu' hm'.1 z' h1'
  have s2' := sens v' hv' hm'.2.1 z' h2'
  rcases hg j hj with ⟨a0, _, hi, hv⟩ | ⟨a0, b0, _, _, hi, hv | hv⟩
  · exact (meet_not hg hj hm hi).elim
  · have e := meet_val_and hin hg hj hm hi hv z s1.2 s2.2
    have e' := meet_val_and hin hg hj hm' hi hv z' s1'.2 s2'.2
    rw [s1.1, s1'.1, e, e']
  · have e := meet_val_or hin hg hj hm hi hv z s1.2 s2.2
    have e' := meet_val_or hin hg hj hm' hi hv z' s1'.2 s2'.2
    rw [s1.1, s1'.1, e, e']

theorem edge_ne (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) (hs : 1 ≤ s)
    (hout : ∀ x, W (9 + s - 1) x = pm x)
    {u v u' v' : Fin 9} (hu : 3 ≤ u.val) (hv : 3 ≤ v.val) (hu' : 3 ≤ u'.val) (hv' : 3 ≤ v'.val)
    (huv : u.val ≠ v.val) {G G' : ℕ}
    (hm : Meet s inp u.val v.val G) (hm' : Meet s inp u'.val v'.val G') (z z' : Fin 9 → Bool)
    (e0 : pm z = true) (e1 : pm (flip u z) = false) (e2 : pm (flip v z) = false)
    (n0 : pm z' = false) (n1 : pm (flip u' z') = true) (n2 : pm (flip v' z') = true) :
    G ≠ G' := by
  intro h
  subst h
  have := key hin hg htight hs hu hv hu' hv' huv hm hm' (z := z) (z' := z')
    (by rw [hout, hout, e0, e1]; decide) (by rw [hout, hout, e0, e2]; decide)
    (by rw [hout, hout, n0, n1]; decide) (by rw [hout, hout, n0, n2]; decide)
  rw [hout, hout, e0, n0] at this
  exact absurd this (by decide)

theorem p4 (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (htight : Tight s inp) (hs : 1 ≤ s)
    (hout : ∀ x, W (9 + s - 1) x = pm x) : False := by
  have ho : 9 + s - 1 < 9 + s := by omega
  have dep : ∀ (t : Fin 9) (z : Fin 9 → Bool), pm z ≠ pm (flip t z) →
      D s inp t.val (9 + s - 1) := fun t z h =>
    dep_of_sens hin hg ho (z := z) (by rw [hout, hout]; exact h)
  have d3 := dep 3 (zw [1, 8]) (by decide)
  have d5 := dep 5 (zw [0, 7]) (by decide)
  have d7 := dep 7 (zw [0, 5]) (by decide)
  have d8 := dep 8 (zw [0, 4]) (by decide)
  obtain ⟨g57, m57⟩ := meet_exists d5 d7
  obtain ⟨g73, m73⟩ := meet_exists d7 d3
  obtain ⟨g38, m38⟩ := meet_exists d3 d8
  obtain ⟨g53, m53⟩ := meet_exists d5 d3
  obtain ⟨g58, m58⟩ := meet_exists d5 d8
  obtain ⟨g78, m78⟩ := meet_exists d7 d8
  have k1 : g57 ≠ g53 := edge_ne hin hg htight hs hout (by decide) (by decide) (by decide)
    (by decide) (by decide) m57 m53 (zw [0, 5, 7]) (zw [0, 2, 7]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have k2 : g73 ≠ g53 := edge_ne hin hg htight hs hout (by decide) (by decide) (by decide)
    (by decide) (by decide) m73 m53 (zw [2, 3, 7]) (zw [0, 2, 7]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have k3 : g73 ≠ g78 := edge_ne hin hg htight hs hout (by decide) (by decide) (by decide)
    (by decide) (by decide) m73 m78 (zw [2, 3, 7]) (zw [0, 4, 5]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have k4 : g38 ≠ g78 := edge_ne hin hg htight hs hout (by decide) (by decide) (by decide)
    (by decide) (by decide) m38 m78 (zw [1, 3, 8]) (zw [0, 4, 5]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have k5 : g38 ≠ g53 := edge_ne hin hg htight hs hout (by decide) (by decide) (by decide)
    (by decide) (by decide) m38 m53 (zw [1, 3, 8]) (zw [0, 2, 7]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have k6 : g38 ≠ g58 := edge_ne hin hg htight hs hout (by decide) (by decide) (by decide)
    (by decide) (by decide) m38 m58 (zw [1, 3, 8]) (zw [0, 4, 7]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have m37 := meet_symm m73
  have m75 := meet_symm m57
  have m83 := meet_symm m38
  have m35 := meet_symm m53
  have u1 := ultra hg htight (by decide) (by decide) m57 m73 m53
  have u2 := ultra hg htight (by decide) (by decide) m53 m37 m57
  have u3 := ultra hg htight (by decide) (by decide) m75 m53 m73
  have u4 := ultra hg htight (by decide) (by decide) m73 m38 m78
  have u5 := ultra hg htight (by decide) (by decide) m78 m83 m73
  have u6 := ultra hg htight (by decide) (by decide) m37 m78 m38
  have u7 := ultra hg htight (by decide) (by decide) m53 m38 m58
  have u8 := ultra hg htight (by decide) (by decide) m58 m83 m53
  have u9 := ultra hg htight (by decide) (by decide) m35 m58 m38
  omega

theorem agree (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (t : Fin 9) (z : Fin 9 → Bool)
    (hgate : ∀ j, j < s → t.val ∈ inp j → W (9 + j) z = W (9 + j) (flip t z)) :
    ∀ k, k < 9 + s → k ≠ t.val → W k z = W k (flip t z) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hne
    by_cases h9 : k < 9
    · rw [hin k h9, hin k h9, flip_ne]
      intro h
      apply hne
      rw [← h]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
      have hj : j < s := by omega
      by_cases hm : t.val ∈ inp j
      · exact hgate j hj hm
      · rcases hg j hj with ⟨a, ha, hi, hv⟩ | ⟨a, b, hab, hb, hi, hv⟩
        · have h1 : a ≠ t.val := fun e => hm (by rw [hi, e]; simp)
          rw [hv, hv, ih a (by omega) (by omega) h1]
        · have h1 : a ≠ t.val := fun e => hm (by rw [hi, e]; simp)
          have h2 : b ≠ t.val := fun e => hm (by rw [hi, e]; simp)
          have ea := ih a (by omega) (by omega) h1
          have eb := ih b (by omega) (by omega) h2
          rcases hv with hv | hv <;> rw [hv, hv, ea, eb]

theorem must_read (hs2 : 2 ≤ s) (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (hout : ∀ x, W (9 + s - 1) x = pm x)
    (t : Fin 9) (z : Fin 9 → Bool) (hne : pm z ≠ pm (flip t z))
    (hgate01 : ∀ j, j < 2 → t.val ∈ inp j → W (9 + j) z = W (9 + j) (flip t z)) :
    ∃ j, 2 ≤ j ∧ j < s ∧ t.val ∈ inp j := by
  by_contra hno
  have h := agree hin hg t z (fun j hj hm => by
    by_cases h2 : j < 2
    · exact hgate01 j h2 hm
    · exact absurd ⟨j, by omega, hj, hm⟩ hno) (9 + s - 1) (by omega) (by have := t.isLt; omega)
  rw [hout, hout] at h
  exact hne h

theorem antitone0 (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j) (h0 : ∀ x, W 9 x = !W 0 x)
    (hno : ∀ j, 1 ≤ j → j < s → 0 ∉ inp j ∧ (inp j).length = 2) (x : Fin 9 → Bool)
    (hx : x 0 = false) :
    ∀ k, k < 9 + s → k ≠ 0 → W k (flip 0 x) = true → W k x = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hne h
    by_cases h9 : k < 9
    · have e : flip 0 x ⟨k, h9⟩ = x ⟨k, h9⟩ :=
        flip_ne x (fun h => hne (by simpa using congrArg Fin.val h))
      rw [hin k h9, e] at h
      rw [hin k h9]
      exact h
    · obtain ⟨j, rfl⟩ : ∃ j, k = 9 + j := ⟨k - 9, by omega⟩
      have hj : j < s := by omega
      by_cases hj0 : j = 0
      · subst hj0
        exfalso
        have e1 : W 9 (flip 0 x) = true := h
        have e2 : W 0 (flip 0 x) = flip 0 x 0 := hin 0 (by omega) (flip 0 x)
        have e3 : flip 0 x 0 = true := by simp [flip, hx]
        rw [h0, e2, e3] at e1
        exact absurd e1 (by decide)
      · obtain ⟨hn0, hl⟩ := hno j (by omega) hj
        rcases hg j hj with ⟨a, ha, hi, hv⟩ | ⟨a, b, hab, hb, hi, hv⟩
        · rw [hi] at hl
          simp at hl
        · have ha0 : a ≠ 0 := fun e => hn0 (by rw [hi, e]; simp)
          have hb0 : b ≠ 0 := fun e => hn0 (by rw [hi, e]; simp)
          rcases hv with hv | hv
          · rw [hv] at h ⊢
            simp only [Bool.and_eq_true] at h ⊢
            exact ⟨ih a (by omega) (by omega) ha0 h.1, ih b (by omega) (by omega) hb0 h.2⟩
          · rw [hv] at h ⊢
            simp only [Bool.or_eq_true] at h ⊢
            rcases h with h | h
            · exact Or.inl (ih a (by omega) (by omega) ha0 h)
            · exact Or.inr (ih b (by omega) (by omega) hb0 h)

theorem tight_of (hs2 : 2 ≤ s) (hs : s ≤ 12)
    (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j)
    (h0i : inp 0 = [0]) (h0 : ∀ x, W 9 x = !W 0 x)
    (h1i : inp 1 = [1, 2]) (h1 : ∀ x, W 10 x = (W 1 x && W 2 x))
    (huse : ∀ j, j + 1 < s → ∃ k, j < k ∧ k < s ∧ 9 + j ∈ inp k)
    (hout : ∀ x, W (9 + s - 1) x = pm x) : Tight s inp := by
  have ho : 9 + s - 1 < 9 + s := by omega
  have hmem : ∀ w, w ∈ reads s inp ↔ ∃ j, 2 ≤ j ∧ j < s ∧ w ∈ inp j := by
    intro w
    unfold reads
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨j, hj, hw⟩
      rw [List.mem_range] at hj
      exact ⟨j + 2, by omega, by omega, hw⟩
    · rintro ⟨j, h2, hj, hw⟩
      refine ⟨j - 2, List.mem_range.mpr (by omega), ?_⟩
      have e : j - 2 + 2 = j := by omega
      rw [e]
      exact hw
  have hlen2 : ∀ j, j < s - 2 → (inp (j + 2)).length ≤ 2 := fun j hj => inp_len hg (by omega)
  have hlen : (reads s inp).length ≤ 2 * (s - 2) := len_le (fun j => inp (j + 2)) (s - 2) hlen2
  have g01 : ∀ (t : Fin 9), 3 ≤ t.val → ∀ (z : Fin 9 → Bool) j, j < 2 → t.val ∈ inp j →
      W (9 + j) z = W (9 + j) (flip t z) := by
    intro t ht z j hj hm
    exfalso
    interval_cases j
    · rw [h0i] at hm
      simp at hm
      omega
    · rw [h1i] at hm
      simp at hm
      omega
  have mr : ∀ (t : Fin 9) (z : Fin 9 → Bool), pm z ≠ pm (flip t z) →
      (∀ j, j < 2 → t.val ∈ inp j → W (9 + j) z = W (9 + j) (flip t z)) →
      t.val ∈ reads s inp := fun t z hne h01 =>
    (hmem t.val).2 (must_read hs2 hin hg hout t z hne h01)
  have r1 : (1 : Fin 9).val ∈ reads s inp := by
    refine mr 1 (zw [3, 8]) (by decide) ?_
    intro j hj hm
    interval_cases j
    · rw [h0i] at hm
      exact absurd hm (by decide)
    · show W 10 _ = W 10 _
      have a : zw [3, 8] 2 = false := by decide
      have b : flip 1 (zw [3, 8]) 2 = false := by decide
      have e1 : W 2 (zw [3, 8]) = zw [3, 8] 2 := hin 2 (by omega) _
      have e2 : W 2 (flip 1 (zw [3, 8])) = flip 1 (zw [3, 8]) 2 := hin 2 (by omega) _
      rw [h1, h1, e1, e2, a, b]
      simp
  have r2 : (2 : Fin 9).val ∈ reads s inp := by
    refine mr 2 (zw [3, 7]) (by decide) ?_
    intro j hj hm
    interval_cases j
    · rw [h0i] at hm
      exact absurd hm (by decide)
    · show W 10 _ = W 10 _
      have a : zw [3, 7] 1 = false := by decide
      have b : flip 2 (zw [3, 7]) 1 = false := by decide
      have e1 : W 1 (zw [3, 7]) = zw [3, 7] 1 := hin 1 (by omega) _
      have e2 : W 1 (flip 2 (zw [3, 7])) = flip 2 (zw [3, 7]) 1 := hin 1 (by omega) _
      rw [h1, h1, e1, e2, a, b]
      simp
  have r3 : (3 : Fin 9).val ∈ reads s inp :=
    mr 3 (zw [1, 8]) (by decide) (g01 3 (by decide) _)
  have r4 : (4 : Fin 9).val ∈ reads s inp :=
    mr 4 (zw [0, 8]) (by decide) (g01 4 (by decide) _)
  have r5 : (5 : Fin 9).val ∈ reads s inp :=
    mr 5 (zw [0, 7]) (by decide) (g01 5 (by decide) _)
  have r6 : (6 : Fin 9).val ∈ reads s inp :=
    mr 6 (zw [1, 5]) (by decide) (g01 6 (by decide) _)
  have r7 : (7 : Fin 9).val ∈ reads s inp :=
    mr 7 (zw [0, 5]) (by decide) (g01 7 (by decide) _)
  have r8 : (8 : Fin 9).val ∈ reads s inp :=
    mr 8 (zw [0, 4]) (by decide) (g01 8 (by decide) _)
  have hR : ∀ w, 1 ≤ w → w ≤ s + 7 → w ∈ reads s inp := by
    intro w h1w hw
    by_cases h8 : w ≤ 8
    · interval_cases w
      · exact r1
      · exact r2
      · exact r3
      · exact r4
      · exact r5
      · exact r6
      · exact r7
      · exact r8
    · obtain ⟨j, rfl⟩ : ∃ j, w = 9 + j := ⟨w - 9, by omega⟩
      obtain ⟨k, hjk, hk, hmk⟩ := huse j (by omega)
      refine (hmem _).2 ⟨k, ?_, hk, hmk⟩
      by_contra hk2
      have e : k = 1 := by omega
      subst e
      rw [h1i] at hmk
      simp at hmk
      omega
  have tight_from : (reads s inp).Nodup → Tight s inp := by
    intro hnd w hw j j' hj hj' hm hm'
    have hj2 : 2 ≤ j := by
      by_contra hc
      have hc' : j < 2 := by omega
      interval_cases j
      · rw [h0i] at hm
        simp at hm
        omega
      · rw [h1i] at hm
        simp at hm
        omega
    have hj2' : 2 ≤ j' := by
      by_contra hc
      have hc' : j' < 2 := by omega
      interval_cases j'
      · rw [h0i] at hm'
        simp at hm'
        omega
      · rw [h1i] at hm'
        simp at hm'
        omega
    have e := tight_range (fun j => inp (j + 2)) (s - 2) hnd (j - 2) (j' - 2) (by omega) (by omega) w
      (by rw [show j - 2 + 2 = j by omega]; exact hm) (by rw [show j' - 2 + 2 = j' by omega]; exact hm')
    omega
  by_cases hz : 0 ∈ reads s inp
  · have hsub : Finset.range (s + 8) ⊆ (reads s inp).toFinset := by
      intro w hw
      rw [List.mem_toFinset]
      rw [Finset.mem_range] at hw
      by_cases e : w = 0
      · subst e
        exact hz
      · exact hR w (by omega) (by omega)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    exact tight_from (nodup_of_card _ (by omega))
  · have hsub : Finset.Icc 1 (s + 7) ⊆ (reads s inp).toFinset := by
      intro w hw
      rw [List.mem_toFinset]
      rw [Finset.mem_Icc] at hw
      exact hR w hw.1 hw.2
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    by_cases hN : ∃ j, 2 ≤ j ∧ j < s ∧ (inp j).length ≤ 1
    · obtain ⟨j, h2, hj, h1l⟩ := hN
      have hl := len_lt (fun j => inp (j + 2)) (s - 2) hlen2 (j - 2) (by omega)
        (by rw [show j - 2 + 2 = j by omega]; exact h1l)
      have hl' : (reads s inp).length + 1 ≤ 2 * (s - 2) := hl
      exact tight_from (nodup_of_card _ (by omega))
    · exfalso
      have hno : ∀ j, 1 ≤ j → j < s → 0 ∉ inp j ∧ (inp j).length = 2 := by
        intro j h1j hj
        by_cases e : j = 1
        · subst e
          rw [h1i]
          simp
        · refine ⟨fun h => hz ((hmem 0).2 ⟨j, by omega, hj, h⟩), ?_⟩
          have := inp_len hg hj
          by_contra hc
          exact hN ⟨j, by omega, hj, by omega⟩
      have h := antitone0 hin hg h0 hno (zw [4, 8]) (by decide) (9 + s - 1) ho (by omega)
        (by rw [hout]; decide)
      rw [hout] at h
      exact absurd h (by decide)

theorem core (hs2 : 2 ≤ s) (hs : s ≤ 12)
    (hin : ∀ i (hi : i < 9) x, W i x = x ⟨i, hi⟩)
    (hg : ∀ j, j < s → GateSpec W inp j)
    (h0i : inp 0 = [0]) (h0 : ∀ x, W 9 x = !W 0 x)
    (h1i : inp 1 = [1, 2]) (h1 : ∀ x, W 10 x = (W 1 x && W 2 x))
    (huse : ∀ j, j + 1 < s → ∃ k, j < k ∧ k < s ∧ 9 + j ∈ inp k)
    (hout : ∀ x, W (9 + s - 1) x = pm x) : False :=
  p4 hin hg (tight_of hs2 hs hin hg h0i h0 h1i h1 huse hout) (by omega) hout

end core

def dflt : Gate := ⟨GateOp.and, []⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Wf (gs : List Gate) (k : ℕ) (x : Fin 9 → Bool) : Bool := (run gs (List.ofFn x)).getD k false

def inpf (gs : List Gate) (j : ℕ) : List ℕ := (gs.getD j dflt).inputs

theorem run_cons (g : Gate) (t : List Gate) (w : List Bool) :
    run (g :: t) w = run t (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_app (w : List Bool) (v : Bool) (k : ℕ) (hk : k < w.length) :
    (w ++ [v]).getD k false = w.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_app_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem run_lt : ∀ (gs : List Gate) (w : List Bool) (k : ℕ), k < w.length →
    (run gs w).getD k false = w.getD k false
  | [], w, k, _ => rfl
  | g :: t, w, k, hk => by
    rw [run_cons, run_lt t _ k (by simp; omega)]
    exact getD_app w _ k hk

theorem run_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ gs[j].inputs, i < w.length + j) →
    (run gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs w).getD i false)
  | g :: t, w, 0, _, h => by
    simp only [List.getElem_cons_zero, Nat.add_zero] at h ⊢
    rw [run_cons, run_lt t _ w.length (by simp), getD_app_last]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [run_lt t _ i (by simp; have := h i hi; omega), getD_app w _ i (h i hi)]
  | g :: t, w, j + 1, hj, h => by
    have ih := run_gate t (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) j
      (by simpa using hj)
      (by
        intro i hi
        have := h i (by simpa using hi)
        simp
        omega)
    rw [run_cons]
    simp only [List.length_append, List.length_singleton, List.getElem_cons_succ] at ih ⊢
    rw [show w.length + (j + 1) = w.length + 1 + j by omega]
    exact ih

theorem getD_dflt (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gs.getD j dflt = gs[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem head_facts (gs : List Gate) (hh : gs.head? = some ⟨GateOp.not, [0]⟩)
    (ht : gs.tail.head? = some ⟨GateOp.and, [1, 2]⟩) :
    2 ≤ gs.length ∧ gs.getD 0 dflt = ⟨GateOp.not, [0]⟩ ∧ gs.getD 1 dflt = ⟨GateOp.and, [1, 2]⟩ := by
  rcases gs with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp at hh
  · simp at ht
  · simp at hh ht
    subst hh
    subst ht
    simp

theorem Wf_gate (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin 9 → Bool)
    (hlt : ∀ i ∈ gs[j].inputs, i < 9 + j) :
    Wf gs (9 + j) x = gs[j].op.eval (gs[j].inputs.map fun i => Wf gs i x) := by
  have h := run_gate gs (List.ofFn x) j hj (by rw [List.length_ofFn]; exact hlt)
  rw [List.length_ofFn] at h
  exact h

theorem bridge (gs : List Gate) (o : ℕ) (hsz : gs.length ≤ 12)
    (hev : ∀ x : Fin 9 → Bool, (run gs (List.ofFn x)).getD o false = pm x)
    (ho : o + 1 = 9 + gs.length)
    (hshape : ∀ j : Fin gs.length,
      ((gs.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (gs.get j).inputs = [a]) ∨
      (((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (gs.get j).inputs = [a, b]))
    (huse : ∀ j : Fin gs.length, j.val + 1 < gs.length →
      ∃ k : Fin gs.length, j.val < k.val ∧ 9 + j.val ∈ (gs.get k).inputs)
    (hh : gs.head? = some ⟨GateOp.not, [0]⟩)
    (ht : gs.tail.head? = some ⟨GateOp.and, [1, 2]⟩) : False := by
  obtain ⟨hlen2, hg0, hg1⟩ := head_facts gs hh ht
  have hin : ∀ i (hi : i < 9) x, Wf gs i x = x ⟨i, hi⟩ := by
    intro i hi x
    show (run gs (List.ofFn x)).getD i false = _
    rw [run_lt _ _ _ (by rw [List.length_ofFn]; exact hi)]
    have e : (List.ofFn x)[i]? = some (x ⟨i, hi⟩) := by
      rw [List.getElem?_ofFn]
      simp [hi]
    rw [List.getD_eq_getElem?_getD, e]
    rfl
  have hg : ∀ j, j < gs.length → GateSpec (Wf gs) (inpf gs) j := by
    intro j hj
    have hinp : inpf gs j = gs[j].inputs := by
      show (gs.getD j dflt).inputs = _
      rw [getD_dflt gs j hj]
    rcases hshape ⟨j, hj⟩ with ⟨hop, a, ha, hia⟩ | ⟨hop, a, b, hab, hb, hiab⟩
    · simp only [List.get_eq_getElem] at hop hia
      have ha : a < 9 + j := ha
      left
      refine ⟨a, ha, by rw [hinp, hia], fun x => ?_⟩
      rw [Wf_gate gs j hj x (by rw [hia]; intro i hi; simp at hi; omega), hop, hia]
      rfl
    · simp only [List.get_eq_getElem] at hop hiab
      have hb : b < 9 + j := hb
      right
      refine ⟨a, b, hab, hb, by rw [hinp, hiab], ?_⟩
      rcases hop with hop | hop
      · left
        intro x
        rw [Wf_gate gs j hj x (by rw [hiab]; intro i hi; simp at hi; omega), hop, hiab]
        simp [GateOp.eval]
      · right
        intro x
        rw [Wf_gate gs j hj x (by rw [hiab]; intro i hi; simp at hi; omega), hop, hiab]
        simp [GateOp.eval]
  have h0i : inpf gs 0 = [0] := by
    show (gs.getD 0 dflt).inputs = _
    rw [hg0]
  have h1i : inpf gs 1 = [1, 2] := by
    show (gs.getD 1 dflt).inputs = _
    rw [hg1]
  have h0 : ∀ x, Wf gs 9 x = !Wf gs 0 x := by
    intro x
    have e : gs[0] = ⟨GateOp.not, [0]⟩ := by
      rw [← getD_dflt gs 0 (by omega)]
      exact hg0
    have h := Wf_gate gs 0 (by omega) x (by rw [e]; simp)
    rw [e] at h
    simpa [GateOp.eval] using h
  have h1 : ∀ x, Wf gs 10 x = (Wf gs 1 x && Wf gs 2 x) := by
    intro x
    have e : gs[1] = ⟨GateOp.and, [1, 2]⟩ := by
      rw [← getD_dflt gs 1 (by omega)]
      exact hg1
    have h := Wf_gate gs 1 (by omega) x (by rw [e]; simp)
    rw [e] at h
    simpa [GateOp.eval] using h
  have huse' : ∀ j, j + 1 < gs.length → ∃ k, j < k ∧ k < gs.length ∧ 9 + j ∈ inpf gs k := by
    intro j hj
    obtain ⟨k, hk, hm⟩ := huse ⟨j, by omega⟩ hj
    refine ⟨k.val, hk, k.isLt, ?_⟩
    show 9 + j ∈ (gs.getD k.val dflt).inputs
    rw [getD_dflt gs k.val k.isLt]
    simpa using hm
  have hout : ∀ x, Wf gs (9 + gs.length - 1) x = pm x := by
    intro x
    have e : 9 + gs.length - 1 = o := by omega
    rw [e]
    exact hev x
  exact core hlen2 hsz hin hg h0i h0 h1i h1 huse' hout

end PEqualNP.Outside.L_meta_27440

theorem PEqualNP.Outside.L_meta_27440 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩)) := by
  rintro ⟨C, _, hsize, hev, hout, hshape, _, huse, hhead, htail⟩
  exact PEqualNP.Outside.L_meta_27440.bridge C.gates C.output hsize hev hout hshape huse hhead htail
