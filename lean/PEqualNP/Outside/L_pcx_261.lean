import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_261_aux

open PEqualNP.ProofComplexity

private def BadIn {n : ℕ} (E : Fin n → Fin n → Bool → Prop) (m : ℕ) : Prop :=
  ∃ (v : ℕ → Fin n) (s : ℕ → Bool),
    v 0 = v m ∧ Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
    ∀ i < m, E (v i) (v (i + 1)) (s i)

private inductive Walk {n : ℕ} (E : Fin n → Fin n → Bool → Prop) : Fin n → Fin n → Bool → Prop
  | refl (u : Fin n) : Walk E u u false
  | step {u v w : Fin n} {p b : Bool} : Walk E u v p → E v w b → Walk E u w (p ^^ b)

private lemma Walk.trans {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    {u v w : Fin n} {p q : Bool} (h1 : Walk E u v p) (h2 : Walk E v w q) :
    Walk E u w (p ^^ q) := by
  induction h2 with
  | refl => simpa using h1
  | step _ he ih =>
    have := Walk.step ih he
    simpa [Bool.xor_assoc] using this

private lemma Walk.symm {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hEsym : ∀ u v b, E u v b → E v u b) {u v : Fin n} {p : Bool}
    (h : Walk E u v p) : Walk E v u p := by
  induction h with
  | refl => exact Walk.refl u
  | @step v0 w0 p0 b0 _ he ih =>
    have h1 : Walk E w0 v0 b0 := by
      have := Walk.step (Walk.refl w0) (hEsym v0 w0 b0 he)
      simpa using this
    have h2 := Walk.trans h1 ih
    simpa [Bool.xor_comm] using h2

private lemma walk_to_seq {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    {u v : Fin n} {p : Bool} (h : Walk E u v p) :
    ∃ (m : ℕ) (vs : ℕ → Fin n) (ss : ℕ → Bool),
      vs 0 = u ∧ vs m = v ∧
      (((Finset.range m).filter (fun i => ss i = true)).card % 2 == 1) = p ∧
      ∀ i < m, E (vs i) (vs (i + 1)) (ss i) := by
  induction h with
  | refl =>
    exact ⟨0, fun _ => u, fun _ => false, rfl, rfl, rfl, fun _ h => by omega⟩
  | @step v0 w0 p0 b0 _ he ih =>
    obtain ⟨m, vs, ss, h0, hm, hpar, hedge⟩ := ih
    refine ⟨m + 1, fun i => if i ≤ m then vs i else w0, fun i => if i < m then ss i else b0,
      by simp [h0], by simp, ?_, ?_⟩
    · have hfilt : (Finset.range (m + 1)).filter (fun i => (if i < m then ss i else b0) = true) =
          (Finset.range m).filter (fun i => ss i = true) ∪
            (if b0 = true then {m} else ∅) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
        by_cases him : i < m
        · simp [him, show i < m + 1 by omega]
          split_ifs <;> simp [show i ≠ m by omega]
        · by_cases heq : i = m
          · subst heq
            simp only [lt_irrefl, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one, true_and,
              false_and, false_or]
            cases b0 <;> simp
          · have hnot : ¬ (i < m + 1) := by omega
            simp only [hnot, false_and, false_iff, not_or, not_and]
            refine ⟨fun h => absurd h him, ?_⟩
            split_ifs <;> simp [heq]
      rw [hfilt, Finset.card_union_of_disjoint]
      · cases hb : b0
        · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_empty, Nat.add_zero,
            Bool.xor_false]
          exact hpar
        · simp only [↓reduceIte, Finset.card_singleton, Bool.xor_true]
          have hpar' : (((Finset.range m).filter (fun i => ss i = true)).card % 2 == 1) = p0 := hpar
          cases hp0 : p0
          · rw [hp0] at hpar'
            have h0 : ((Finset.range m).filter (fun i => ss i = true)).card % 2 = 0 := by
              have : ((Finset.range m).filter (fun i => ss i = true)).card % 2 ≠ 1 := by
                simpa using hpar'
              omega
            simp [Nat.add_mod, h0]
          · rw [hp0] at hpar'
            have h1 : ((Finset.range m).filter (fun i => ss i = true)).card % 2 = 1 := by
              simpa using hpar'
            simp [Nat.add_mod, h1]
      · split_ifs
        · simp
        · exact Finset.disjoint_empty_right _
    · intro i hi
      by_cases him : i < m
      · have h1 : i ≤ m := by omega
        have h2 : i + 1 ≤ m := by omega
        simp only [him, h1, h2, ↓reduceIte]
        exact hedge i him
      · have heq : i = m := by omega
        subst heq
        simp only [le_rfl, ↓reduceIte, show ¬(i + 1 ≤ i) by omega, lt_irrefl, hm]
        exact he

private lemma exists_bad_of_inconsistent {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hEsym : ∀ u v b, E u v b → E v u b)
    (hincon : ¬ ∃ f : Fin n → Bool, ∀ u v b, E u v b → (f u ^^ f v) = b) :
    ∃ m, BadIn E m := by
  classical
  by_contra hnobad
  have hno_odd : ∀ u : Fin n, ¬ Walk E u u true := by
    intro u hwalk
    obtain ⟨m, vs, ss, h0, hm, hpar, hedge⟩ := walk_to_seq hwalk
    have hodd : Odd (((Finset.range m).filter (fun i => ss i = true)).card) := by
      rw [Nat.odd_iff]
      simpa using hpar
    exact hnobad ⟨m, vs, ss, by rw [h0, hm], hodd, hedge⟩
  have huniq : ∀ u v p q, Walk E u v p → Walk E u v q → p = q := by
    intro u v p q hp hq
    have hloop := Walk.trans hp (Walk.symm hEsym hq)
    cases hpq : (p ^^ q)
    · cases p <;> cases q <;> simp_all
    · rw [hpq] at hloop
      exact absurd hloop (hno_odd u)
  let comp : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun v => ∃ p, Walk E u v p)
  have hcomp_ne : ∀ u, (comp u).Nonempty := fun u =>
    ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, false, Walk.refl u⟩⟩
  let rep : Fin n → Fin n := fun u => (comp u).min' (hcomp_ne u)
  have hrep_walk : ∀ u, ∃ p, Walk E (rep u) u p := by
    intro u
    have hmem : rep u ∈ comp u := Finset.min'_mem (comp u) (hcomp_ne u)
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hmem).2
    exact ⟨p, Walk.symm hEsym hp⟩
  have hrep_eq : ∀ u v b, E u v b → rep u = rep v := by
    intro u v b he
    have hcomp_eq : comp u = comp v := by
      ext w
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨b ^^ p, Walk.trans (Walk.symm hEsym (by simpa using Walk.step (Walk.refl u) he)) hp⟩
      · rintro ⟨p, hp⟩
        exact ⟨b ^^ p, Walk.trans (by simpa using Walk.step (Walk.refl u) he) hp⟩
    simp only [rep, hcomp_eq]
  let f : Fin n → Bool := fun u => decide (Walk E (rep u) u true)
  have hf_walk : ∀ u, Walk E (rep u) u (f u) := by
    intro u
    obtain ⟨p, hp⟩ := hrep_walk u
    cases p
    · have hnot : ¬ Walk E (rep u) u true := fun ht =>
        Bool.noConfusion (huniq (rep u) u false true hp ht)
      simp only [f, decide_eq_false hnot]
      exact hp
    · simp only [f, decide_eq_true hp]
      exact hp
  apply hincon
  refine ⟨f, fun u v b he => ?_⟩
  have h1 : Walk E (rep u) v (f u ^^ b) := Walk.step (hf_walk u) he
  have h2 : Walk E (rep u) v (f v) := by
    rw [hrep_eq u v b he]
    exact hf_walk v
  have heq : (f u ^^ b) = f v := huniq (rep u) v (f u ^^ b) (f v) h1 h2
  cases hfu : f u <;> cases hfv : f v <;> cases hb : b <;> simp_all

private lemma filter_range_split_same (m i j : ℕ) (hij : i < j) (hjm : j < m) (s : ℕ → Bool) :
    ((Finset.range m).filter (fun t => s t = true)).card =
      ((Finset.range (j - i)).filter (fun t => s (i + t) = true)).card +
      ((Finset.range (m - (j - i))).filter
        (fun t => (if t < i then s t else s (t + (j - i))) = true)).card := by
  have hbij :
      ((Finset.range (j - i)).filter (fun t => s (i + t) = true)).card =
      ((Finset.range m).filter (fun t => i ≤ t ∧ t < j ∧ s t = true)).card := by
    refine Finset.card_bij (fun t _ => i + t) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      exact ⟨by omega, by omega, by omega, ht.2⟩
    · intro t1 _ t2 _ h; omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      refine ⟨t - i, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show i + (t - i) = t by omega]
      exact ht.2.2.2
  have hbij2 :
      ((Finset.range (m - (j - i))).filter
        (fun t => (if t < i then s t else s (t + (j - i))) = true)).card =
      ((Finset.range m).filter (fun t => (t < i ∨ j ≤ t) ∧ s t = true)).card := by
    refine Finset.card_bij (fun t _ => if t < i then t else t + (j - i)) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      split_ifs with hti
      · exact ⟨by omega, Or.inl hti, by simpa [hti] using ht.2⟩
      · exact ⟨by omega, Or.inr (by omega), by simpa [hti] using ht.2⟩
    · intro t1 _ t2 _ h
      split_ifs at h <;> omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      rcases ht.2.1 with hti | hjt
      · refine ⟨t, ?_, by simp [hti]⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by simp [hti, ht.2.2]⟩
      · refine ⟨t - (j - i), ?_, by simp [show ¬(t - (j - i) < i) by omega]; omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        simp only [show ¬(t - (j - i) < i) by omega, ↓reduceIte]
        rw [show t - (j - i) + (j - i) = t by omega]
        exact ht.2.2
  rw [hbij, hbij2, ← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    constructor
    · intro ⟨htm, hst⟩
      by_cases h1 : t < i
      · exact Or.inr ⟨htm, Or.inl h1, hst⟩
      · by_cases h2 : t < j
        · exact Or.inl ⟨htm, by omega, h2, hst⟩
        · exact Or.inr ⟨htm, Or.inr (by omega), hst⟩
    · rintro (⟨htm, _, _, hst⟩ | ⟨htm, _, hst⟩) <;> exact ⟨htm, hst⟩
  · rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

private lemma filter_range_split_opp (m i j : ℕ) (hij : i < j) (hjm : j < m)
    (s : ℕ → Bool) (hsij : s i = s j) :
    ((Finset.range m).filter (fun t => s t = true)).card =
      ((Finset.range (j - i - 1)).filter (fun t => s (i + 1 + t) = true)).card +
      ((Finset.range (m - (j - i + 1))).filter
        (fun t => (if t < i then s t else s (t + (j - i + 1))) = true)).card +
      2 * (if s i = true then 1 else 0) := by
  have hbij1 :
      ((Finset.range (j - i - 1)).filter (fun t => s (i + 1 + t) = true)).card =
      ((Finset.range m).filter (fun t => i < t ∧ t < j ∧ s t = true)).card := by
    refine Finset.card_bij (fun t _ => i + 1 + t) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      exact ⟨by omega, by omega, by omega, ht.2⟩
    · intro t1 _ t2 _ h; omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      refine ⟨t - (i + 1), ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show i + 1 + (t - (i + 1)) = t by omega]
      exact ht.2.2.2
  have hbij2 :
      ((Finset.range (m - (j - i + 1))).filter
        (fun t => (if t < i then s t else s (t + (j - i + 1))) = true)).card =
      ((Finset.range m).filter (fun t => (t < i ∨ j < t) ∧ s t = true)).card := by
    refine Finset.card_bij (fun t _ => if t < i then t else t + (j - i + 1)) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      split_ifs with hti
      · exact ⟨by omega, Or.inl hti, by simpa [hti] using ht.2⟩
      · exact ⟨by omega, Or.inr (by omega), by simpa [hti] using ht.2⟩
    · intro t1 _ t2 _ h
      split_ifs at h <;> omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      rcases ht.2.1 with hti | hjt
      · refine ⟨t, ?_, by simp [hti]⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by simp [hti, ht.2.2]⟩
      · refine ⟨t - (j - i + 1), ?_, by simp [show ¬(t - (j - i + 1) < i) by omega]; omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        simp only [show ¬(t - (j - i + 1) < i) by omega, ↓reduceIte]
        rw [show t - (j - i + 1) + (j - i + 1) = t by omega]
        exact ht.2.2
  have hbij3 :
      2 * (if s i = true then 1 else 0) =
      ((Finset.range m).filter (fun t => (t = i ∨ t = j) ∧ s t = true)).card := by
    cases hsi : s i
    · have hsj : s j = false := by rw [← hsij, hsi]
      simp only [Bool.false_eq_true, ↓reduceIte, mul_zero]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _ h
      rcases h.1 with rfl | rfl
      · exact Bool.noConfusion (hsi.symm.trans h.2)
      · exact Bool.noConfusion (hsj.symm.trans h.2)
    · have hsj : s j = true := by rw [← hsij, hsi]
      simp only [↓reduceIte, mul_one]
      have heq : (Finset.range m).filter (fun t => (t = i ∨ t = j) ∧ s t = true) = {i, j} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro ⟨_, h1, _⟩; exact h1
        · rintro (rfl | rfl)
          · exact ⟨by omega, Or.inl rfl, hsi⟩
          · exact ⟨hjm, Or.inr rfl, hsj⟩
      rw [heq, Finset.card_pair (by omega)]
  rw [hbij1, hbij2, hbij3, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    constructor
    · intro ⟨htm, hst⟩
      by_cases h1 : t < i
      · exact Or.inl (Or.inr ⟨htm, Or.inl h1, hst⟩)
      · by_cases h2 : t = i
        · exact Or.inr ⟨htm, Or.inl h2, hst⟩
        · by_cases h3 : t < j
          · exact Or.inl (Or.inl ⟨htm, by omega, h3, hst⟩)
          · by_cases h4 : t = j
            · exact Or.inr ⟨htm, Or.inr h4, hst⟩
            · exact Or.inl (Or.inr ⟨htm, Or.inr (by omega), hst⟩)
    · rintro ((⟨htm, _, _, hst⟩ | ⟨htm, _, hst⟩) | ⟨htm, _, hst⟩) <;> exact ⟨htm, hst⟩
  · rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_union, Finset.mem_filter] at h1 h2
    omega
  · rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

private lemma bad_split_same {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    {m i j : ℕ} {v : ℕ → Fin n} {s : ℕ → Bool}
    (hv0 : v 0 = v m) (hodd : Odd (((Finset.range m).filter (fun t => s t = true)).card))
    (hedge : ∀ t < m, E (v t) (v (t + 1)) (s t))
    (hij : i < j) (hjm : j < m) (hvivj : v i = v j) :
    BadIn E (j - i) ∨ BadIn E (m - (j - i)) := by
  have hsum := filter_range_split_same m i j hij hjm s
  by_cases h1 : Odd (((Finset.range (j - i)).filter (fun t => s (i + t) = true)).card)
  · left
    refine ⟨fun t => v (i + t), fun t => s (i + t), ?_, h1, fun t ht => ?_⟩
    · simp [show i + (j - i) = j by omega, hvivj]
    · dsimp only
      rw [show i + (t + 1) = (i + t) + 1 by omega]
      exact hedge (i + t) (by omega)
  · right
    have h2 : Odd (((Finset.range (m - (j - i))).filter
        (fun t => (if t < i then s t else s (t + (j - i))) = true)).card) := by
      rw [Nat.odd_iff] at hodd h1 ⊢
      omega
    refine ⟨fun t => if t < i then v t else v (t + (j - i)),
      fun t => if t < i then s t else s (t + (j - i)), ?_, h2, fun t ht => ?_⟩
    · by_cases hi0 : i = 0
      · subst hi0
        simp only [Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, Nat.sub_zero]
        rw [show m - j + j = m by omega, ← hv0, hvivj]
      · simp only [show 0 < i by omega, ↓reduceIte, show ¬(m - (j - i) < i) by omega,
          show m - (j - i) + (j - i) = m by omega, hv0]
    · by_cases hti : t < i
      · by_cases ht1 : t + 1 < i
        · simp only [hti, ht1, ↓reduceIte]
          exact hedge t (by omega)
        · have heq : t + 1 = i := by omega
          simp only [hti, ht1, ↓reduceIte]
          rw [heq, show i + (j - i) = j by omega, ← hvivj, ← heq]
          exact hedge t (by omega)
      · have ht1 : ¬(t + 1 < i) := by omega
        simp only [hti, ht1, ↓reduceIte, show t + 1 + (j - i) = t + (j - i) + 1 by omega]
        exact hedge (t + (j - i)) (by omega)

private lemma bad_split_opp {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    {m i j : ℕ} {v : ℕ → Fin n} {s : ℕ → Bool}
    (hv0 : v 0 = v m) (hodd : Odd (((Finset.range m).filter (fun t => s t = true)).card))
    (hedge : ∀ t < m, E (v t) (v (t + 1)) (s t))
    (hij : i < j) (hjm : j < m) (h1 : v i = v (j + 1)) (h2 : v (i + 1) = v j) (hsij : s i = s j) :
    BadIn E (j - i - 1) ∨ BadIn E (m - (j - i + 1)) := by
  have hsum := filter_range_split_opp m i j hij hjm s hsij
  by_cases ha : Odd (((Finset.range (j - i - 1)).filter (fun t => s (i + 1 + t) = true)).card)
  · left
    refine ⟨fun t => v (i + 1 + t), fun t => s (i + 1 + t), ?_, ha, fun t ht => ?_⟩
    · simp only [Nat.add_zero]
      rw [show i + 1 + (j - i - 1) = j by omega, h2]
    · dsimp only
      rw [show i + 1 + (t + 1) = i + 1 + t + 1 by omega]
      exact hedge (i + 1 + t) (by omega)
  · right
    have hb : Odd (((Finset.range (m - (j - i + 1))).filter
        (fun t => (if t < i then s t else s (t + (j - i + 1))) = true)).card) := by
      rw [Nat.odd_iff] at hodd ha ⊢
      omega
    refine ⟨fun t => if t < i then v t else v (t + (j - i + 1)),
      fun t => if t < i then s t else s (t + (j - i + 1)), ?_, hb, fun t ht => ?_⟩
    · by_cases hi0 : i = 0
      · subst hi0
        simp only [Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, Nat.sub_zero]
        rw [show m - (j + 1) + (j + 1) = m by omega, ← hv0, h1]
      · simp only [show 0 < i by omega, ↓reduceIte, show ¬(m - (j - i + 1) < i) by omega,
          show m - (j - i + 1) + (j - i + 1) = m by omega, hv0]
    · by_cases hti : t < i
      · by_cases ht1 : t + 1 < i
        · simp only [hti, ht1, ↓reduceIte]
          exact hedge t (by omega)
        · have heq : t + 1 = i := by omega
          simp only [hti, ht1, ↓reduceIte]
          rw [heq, show i + (j - i + 1) = j + 1 by omega, ← h1, ← heq]
          exact hedge t (by omega)
      · have ht1 : ¬(t + 1 < i) := by omega
        simp only [hti, ht1, ↓reduceIte, show t + 1 + (j - i + 1) = t + (j - i + 1) + 1 by omega]
        exact hedge (t + (j - i + 1)) (by omega)

private lemma shortest_bad_vertices_distinct {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    {g : ℕ} {v : ℕ → Fin n} {s : ℕ → Bool}
    (hv0 : v 0 = v g) (hodd : Odd (((Finset.range g).filter (fun t => s t = true)).card))
    (hedge : ∀ t < g, E (v t) (v (t + 1)) (s t))
    (hmin : ∀ j < g, ¬ BadIn E j) :
    ∀ i j, i < j → j < g → v i ≠ v j := by
  intro i j hij hjg heq
  rcases bad_split_same hv0 hodd hedge hij hjg heq with h1 | h2
  · exact hmin (j - i) (by omega) h1
  · exact hmin (g - (j - i)) (by omega) h2

private lemma shortest_bad_le_edges {n : ℕ} {α : Type*} [DecidableEq α]
    (L : Finset α) (uOf vOf : α → Fin n) (bOf : α → Bool)
    (E_L : Fin n → Fin n → Bool → Prop)
    (hEL : ∀ x y s, E_L x y s ↔ ∃ p ∈ L, ((uOf p = x ∧ vOf p = y) ∨ (uOf p = y ∧ vOf p = x)) ∧ bOf p = s)
    (m : ℕ) (hbad : BadIn E_L m) (hmin : ∀ k < m, ¬ BadIn E_L k) :
    m ≤ L.card := by
  classical
  obtain ⟨v, s, hv0, hodd, hedge⟩ := hbad
  have hex : ∀ i : Fin m, ∃ p ∈ L,
      ((uOf p = v i.val ∧ vOf p = v (i.val + 1)) ∨ (uOf p = v (i.val + 1) ∧ vOf p = v i.val)) ∧
      bOf p = s i.val := fun i => (hEL _ _ _).mp (hedge i.val i.isLt)
  let pick : Fin m → α := fun i => Classical.choose (hex i)
  have hpick_mem : ∀ i : Fin m, pick i ∈ L := fun i => (Classical.choose_spec (hex i)).1
  have hpick_ed : ∀ i : Fin m,
      ((uOf (pick i) = v i.val ∧ vOf (pick i) = v (i.val + 1)) ∨
       (uOf (pick i) = v (i.val + 1) ∧ vOf (pick i) = v i.val)) ∧
      bOf (pick i) = s i.val := fun i => (Classical.choose_spec (hex i)).2
  have hinj_lt : ∀ i j : Fin m, i.val < j.val → pick i ≠ pick j := by
    intro i j hlt hij
    have hi := hpick_ed i
    have hj := hpick_ed j
    rw [hij] at hi
    have hsij : s i.val = s j.val := by rw [← hi.2, hj.2]
    rcases hi.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj.1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rcases bad_split_same hv0 hodd hedge hlt j.isLt (h1.symm.trans h3) with ha | hb
      · exact hmin _ (by omega) ha
      · exact hmin _ (by omega) hb
    · rcases bad_split_opp hv0 hodd hedge hlt j.isLt (h1.symm.trans h3) (h2.symm.trans h4) hsij with ha | hb
      · exact hmin _ (by omega) ha
      · exact hmin _ (by omega) hb
    · rcases bad_split_opp hv0 hodd hedge hlt j.isLt (h2.symm.trans h4) (h1.symm.trans h3) hsij with ha | hb
      · exact hmin _ (by omega) ha
      · exact hmin _ (by omega) hb
    · rcases bad_split_same hv0 hodd hedge hlt j.isLt (h2.symm.trans h4) with ha | hb
      · exact hmin _ (by omega) ha
      · exact hmin _ (by omega) hb
  have hinj : Function.Injective pick := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
    · exact hinj_lt i j hlt hij
    · exact hinj_lt j i hgt hij.symm
  have hcard : (Finset.univ.image pick).card ≤ L.card :=
    Finset.card_le_card (fun x hx => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hpick_mem i)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

private lemma resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool} {C D R : Clause V}
    (hres : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) :
    ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  cases hv : a v
  · obtain ⟨l, hlC, hsat⟩ := hC
    have hne : l ≠ (v, true) := by
      intro heq
      rw [heq] at hsat
      exact Bool.noConfusion (hv.symm.trans hsat)
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlC⟩), hsat⟩
  · obtain ⟨l, hlD, hsat⟩ := hD
    have hne : l ≠ (v, false) := by
      intro heq
      rw [heq] at hsat
      exact Bool.noConfusion (hv.symm.trans hsat)
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlD⟩), hsat⟩

private lemma tree_sat_sound {n h : ℕ}
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause (Fin n))
    (hlen : ∀ p ∈ nodes, p.length ≤ h)
    (hstep : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p))
    (a : Fin n → Bool) (r : List Bool) (hr : r ∈ nodes)
    (hleaves : ∀ p ∈ nodes \ inner, r <+: p → ClauseSat a (line p)) :
    ClauseSat a (line r) := by
  have hgen : ∀ (d : ℕ) (p : List Bool), p ∈ nodes → h - p.length ≤ d →
      (∀ q ∈ nodes \ inner, p <+: q → ClauseSat a (line q)) →
      ClauseSat a (line p) := by
    intro d
    induction d with
    | zero =>
      intro p hp hd hl
      by_cases hpin : p ∈ inner
      · have hch := (hstep p hpin).1
        have hl1 := hlen p hp
        have hl2 := hlen (p ++ [false]) hch
        simp only [List.length_append, List.length_singleton] at hl2
        omega
      · exact hl p (Finset.mem_sdiff.mpr ⟨hp, hpin⟩) (List.prefix_refl p)
    | succ d ih =>
      intro p hp hd hl
      by_cases hpin : p ∈ inner
      · obtain ⟨hf, ht, hres⟩ := hstep p hpin
        have hlenp := hlen p hp
        have hsat_f := ih (p ++ [false]) hf (by simp; omega)
          (fun q hq hpq => hl q hq (List.IsPrefix.trans (List.prefix_append p [false]) hpq))
        have hsat_t := ih (p ++ [true]) ht (by simp; omega)
          (fun q hq hpq => hl q hq (List.IsPrefix.trans (List.prefix_append p [true]) hpq))
        exact resolvent_sound hres hsat_f hsat_t
      · exact hl p (Finset.mem_sdiff.mpr ⟨hp, hpin⟩) (List.prefix_refl p)
  exact hgen (h - r.length) r hr le_rfl hleaves

private lemma tree_upward {nodes inner : Finset (List Bool)}
    (hsub : inner ⊆ nodes)
    (hup : ∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) :
    ∀ (p q : List Bool), q ∈ nodes → p <+: q → p ≠ q → p ∈ inner := by
  intro p q hq hpq hne
  obtain ⟨t, rfl⟩ := hpq
  cases t with
  | nil => exact absurd (by simp) hne
  | cons b rest =>
    have hgen : ∀ (r : List Bool), p ++ b :: r ∈ nodes → p ++ [b] ∈ nodes := by
      intro r
      induction r using List.reverseRecOn with
      | nil => intro h; exact h
      | append_singleton r c ih =>
        intro h
        have h1 : (p ++ b :: r) ++ [c] ∈ nodes := by
          simpa [List.append_assoc] using h
        exact ih (hsub (hup (p ++ b :: r) c h1))
    exact hup p b (hgen rest hq)

private lemma tree_leaves_le_two_pow {h : ℕ} (nodes inner : Finset (List Bool))
    (hsub : inner ⊆ nodes)
    (hlen : ∀ p ∈ nodes, p.length ≤ h)
    (hup : ∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) :
    (nodes \ inner).card ≤ 2 ^ h := by
  let pad : List Bool → (Fin h → Bool) := fun p k => p.getD k.val false
  have hinj : Set.InjOn pad ↑(nodes \ inner) := by
    intro p hp q hq heq
    rw [Finset.mem_coe] at hp hq
    have hpn : p ∈ nodes := (Finset.mem_sdiff.mp hp).1
    have hpi : p ∉ inner := (Finset.mem_sdiff.mp hp).2
    have hqn : q ∈ nodes := (Finset.mem_sdiff.mp hq).1
    have hqi : q ∉ inner := (Finset.mem_sdiff.mp hq).2
    have hplen := hlen p hpn
    have hqlen := hlen q hqn
    have hsame : ∀ (k : ℕ) (hkp : k < p.length) (hkq : k < q.length), p[k]'hkp = q[k]'hkq := by
      intro k hkp hkq
      have h1 := congrFun heq ⟨k, by omega⟩
      simp only [pad, List.getD_eq_getElem _ _ hkp, List.getD_eq_getElem _ _ hkq] at h1
      exact h1
    by_cases hle : p.length ≤ q.length
    · have hpref : p <+: q := by
        refine ⟨q.drop p.length, ?_⟩
        apply List.ext_getElem
        · simp; omega
        · intro k hk1 hk2
          by_cases hkp : k < p.length
          · rw [List.getElem_append_left hkp]
            exact hsame k hkp (by omega)
          · rw [List.getElem_append_right (by omega), List.getElem_drop]
            congr 1
            omega
      by_cases hne : p = q
      · exact hne
      · exact absurd (tree_upward hsub hup p q hqn hpref hne) hpi
    · have hpref : q <+: p := by
        refine ⟨p.drop q.length, ?_⟩
        apply List.ext_getElem
        · simp; omega
        · intro k hk1 hk2
          by_cases hkq : k < q.length
          · rw [List.getElem_append_left hkq]
            exact (hsame k (by omega) hkq).symm
          · rw [List.getElem_append_right (by omega), List.getElem_drop]
            congr 1
            omega
      by_cases hne : q = p
      · exact hne.symm
      · exact absurd (tree_upward hsub hup q p hpn hpref hne) hqi
  have h1 := Finset.card_image_of_injOn hinj
  have h2 : ((nodes \ inner).image pad).card ≤ Fintype.card (Fin h → Bool) :=
    Finset.card_le_univ _
  rw [h1, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h2
  exact h2

private lemma clause_sat_of_xor {n : ℕ} {f : Fin n → Bool} {u v : Fin n} {b a : Bool}
    (h : (f u ^^ f v) = b) :
    ClauseSat f ({(u, !a), (v, a ^^ b)} : Clause (Fin n)) := by
  by_cases hfu : f u = !a
  · exact ⟨(u, !a), by simp, hfu⟩
  · refine ⟨(v, a ^^ b), by simp, ?_⟩
    cases h1 : f u <;> cases h2 : f v <;> cases a <;> cases b <;> simp_all

private lemma lower_bound {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hEsym : ∀ u v b, E u v b → E v u b)
    (g : ℕ) (hbadg : BadIn E g) (hming : ∀ j < g, ¬ BadIn E j)
    (L h w : ℕ)
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause (Fin n))
    (hroot : [] ∈ nodes) (hsub : inner ⊆ nodes) (hempty : line [] = ∅)
    (hbw : ∀ p ∈ nodes, p.length ≤ h ∧ (line p).card ≤ w)
    (hL : (nodes \ inner).card ≤ L)
    (hax : ∀ p ∈ nodes, p ∉ inner →
      ∃ (u v : Fin n) (b a : Bool), E u v b ∧ line p = {(u, !a), (v, a ^^ b)})
    (hup : ∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner)
    (hstep : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    2 * g ≤ L ∧ 2 * g ≤ 2 ^ h ∧ (if g = 1 then 1 else 2) ≤ w := by
  classical
  have hgpos : 1 ≤ g := by
    by_contra h0
    have hg0 : g = 0 := by omega
    subst hg0
    obtain ⟨_, _, _, hodd, _⟩ := hbadg
    simp at hodd
  have hroot_in : [] ∈ inner := by
    by_contra hni
    obtain ⟨u, v, b, a, _, hcl⟩ := hax [] hroot hni
    rw [hempty] at hcl
    have : (u, !a) ∈ (∅ : Clause (Fin n)) := by rw [hcl]; simp
    simp at this
  obtain ⟨hf_mem, ht_mem, hres0⟩ := hstep [] hroot_in
  obtain ⟨x, hx_f, hx_t, hx_emp⟩ := hres0
  rw [hempty] at hx_emp
  have hlf : line [false] = {(x, true)} := by
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ (∅ : Clause (Fin n)) := by
        rw [hx_emp]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hl⟩)
      simp at this
    · rintro rfl; exact hx_f
  have hlt : line [true] = {(x, false)} := by
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ (∅ : Clause (Fin n)) := by
        rw [hx_emp]
        exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hl⟩)
      simp at this
    · rintro rfl; exact hx_t
  have hsub_ge : ∀ (r : List Bool) (c : Bool), r ∈ nodes → line r = {(x, c)} →
      g ≤ ((nodes \ inner).filter (fun p => r <+: p)).card := by
    intro r c hr hlr
    set Lr := (nodes \ inner).filter (fun p => r <+: p)
    have hax_r : ∀ p ∈ Lr, ∃ (u v : Fin n) (b a : Bool),
        E u v b ∧ line p = {(u, !a), (v, a ^^ b)} := fun p hp =>
      hax p (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).2
    let pickQuad : ∀ p : List Bool, Fin n × Fin n × Bool × Bool := fun p =>
      if hp : p ∈ Lr then
        let u := Classical.choose (hax_r p hp)
        let h1 := Classical.choose_spec (hax_r p hp)
        let v := Classical.choose h1
        let h2 := Classical.choose_spec h1
        let b := Classical.choose h2
        let h3 := Classical.choose_spec h2
        let a := Classical.choose h3
        (u, v, b, a)
      else (x, x, false, false)
    let uOf : List Bool → Fin n := fun p => (pickQuad p).1
    let vOf : List Bool → Fin n := fun p => (pickQuad p).2.1
    let bOf : List Bool → Bool := fun p => (pickQuad p).2.2.1
    let aOf : List Bool → Bool := fun p => (pickQuad p).2.2.2
    have hpick_spec : ∀ p ∈ Lr, E (uOf p) (vOf p) (bOf p) ∧
        line p = {(uOf p, !(aOf p)), (vOf p, aOf p ^^ bOf p)} := by
      intro p hp
      simp only [uOf, vOf, bOf, aOf, pickQuad, dif_pos hp]
      exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hax_r p hp))))
    let Er : Fin n → Fin n → Bool → Prop := fun u v b =>
      ∃ p ∈ Lr, ((uOf p = u ∧ vOf p = v) ∨ (uOf p = v ∧ vOf p = u)) ∧ bOf p = b
    have hEr_sym : ∀ u v b, Er u v b → Er v u b := by
      rintro u v b ⟨p, hp, h1 | h2, hb⟩
      · exact ⟨p, hp, Or.inr ⟨h1.1, h1.2⟩, hb⟩
      · exact ⟨p, hp, Or.inl ⟨h2.1, h2.2⟩, hb⟩
    have hEr_sub : ∀ u v b, Er u v b → E u v b := by
      rintro u v b ⟨p, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl⟩
      · exact (hpick_spec p hp).1
      · exact hEsym _ _ _ (hpick_spec p hp).1
    have hincon : ¬ ∃ f : Fin n → Bool, ∀ u v b, Er u v b → (f u ^^ f v) = b := by
      rintro ⟨f, hf⟩
      let f' : Fin n → Bool := if f x = c then (fun z => !(f z)) else f
      have hf'_xor : ∀ u v b, Er u v b → (f' u ^^ f' v) = b := by
        intro u v b he
        have h0 := hf u v b he
        dsimp only [f']
        split_ifs
        · dsimp only; rw [← h0]; cases f u <;> cases f v <;> rfl
        · exact h0
      have hf'_x : f' x = !c := by
        dsimp only [f']
        split_ifs with hfx
        · dsimp only
          rw [hfx]
        · cases h1 : f x <;> cases hc : c <;> rw [h1, hc] at hfx <;> simp at hfx ⊢
      have hsat_r := tree_sat_sound nodes inner line (fun p hp => (hbw p hp).1) hstep f' r hr
        (fun p hp hpr => by
          have hpLr : p ∈ Lr := Finset.mem_filter.mpr ⟨hp, hpr⟩
          rw [(hpick_spec p hpLr).2]
          exact clause_sat_of_xor (hf'_xor (uOf p) (vOf p) (bOf p)
            ⟨p, hpLr, Or.inl ⟨rfl, rfl⟩, rfl⟩))
      rw [hlr] at hsat_r
      obtain ⟨l, hl, hsat⟩ := hsat_r
      rw [Finset.mem_singleton] at hl
      rw [hl] at hsat
      rw [hf'_x] at hsat
      cases c <;> simp at hsat
    have hex_bad : ∃ m, BadIn Er m := exists_bad_of_inconsistent Er hEr_sym hincon
    let m := Nat.find hex_bad
    have hm_bad : BadIn Er m := Nat.find_spec hex_bad
    have hm_min : ∀ k < m, ¬ BadIn Er k := fun k hk => Nat.find_min hex_bad hk
    have hm_le : m ≤ Lr.card := shortest_bad_le_edges Lr uOf vOf bOf Er (fun _ _ _ => Iff.rfl) m hm_bad hm_min
    have hbadE : BadIn E m := by
      obtain ⟨v, s, hv0, hodd, hedge⟩ := hm_bad
      exact ⟨v, s, hv0, hodd, fun i hi => hEr_sub _ _ _ (hedge i hi)⟩
    have hgm : g ≤ m := by
      by_contra hlt
      exact hming m (by omega) hbadE
    exact le_trans hgm hm_le
  have hf_ge := hsub_ge [false] true hf_mem hlf
  have ht_ge := hsub_ge [true] false ht_mem hlt
  have hdisj : Disjoint ((nodes \ inner).filter (fun p => [false] <+: p))
      ((nodes \ inner).filter (fun p => [true] <+: p)) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    obtain ⟨t1, ht1⟩ := (Finset.mem_filter.mp h1).2
    obtain ⟨t2, ht2⟩ := (Finset.mem_filter.mp h2).2
    rw [← ht1] at ht2
    simp at ht2
  have hunion_sub : ((nodes \ inner).filter (fun p => [false] <+: p)) ∪
      ((nodes \ inner).filter (fun p => [true] <+: p)) ⊆ nodes \ inner :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hleaves_ge : 2 * g ≤ (nodes \ inner).card := by
    have h1 := Finset.card_le_card hunion_sub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    omega
  have h2g_L : 2 * g ≤ L := le_trans hleaves_ge hL
  have h2g_h : 2 * g ≤ 2 ^ h :=
    le_trans hleaves_ge (tree_leaves_le_two_pow nodes inner hsub (fun p hp => (hbw p hp).1) hup)
  have hw_ge : (if g = 1 then 1 else 2) ≤ w := by
    have hne : (nodes \ inner).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp⟩ := hne
    have hpn : p ∈ nodes := (Finset.mem_sdiff.mp hp).1
    have hpi : p ∉ inner := (Finset.mem_sdiff.mp hp).2
    have hpw : (line p).card ≤ w := (hbw p hpn).2
    obtain ⟨u, v, b, a, he, hcl⟩ := hax p hpn hpi
    rw [hcl] at hpw
    split_ifs with hg1
    · have h1 : 1 ≤ ({(u, !a), (v, a ^^ b)} : Clause (Fin n)).card :=
        Finset.card_pos.mpr ⟨(u, !a), by simp⟩
      omega
    · have hneq : (u, !a) ≠ (v, a ^^ b) := by
        intro heq
        have huv : u = v := congrArg Prod.fst heq
        have hab : (!a) = (a ^^ b) := congrArg Prod.snd heq
        have hb : b = true := by cases ha : a <;> cases hb' : b <;> rw [ha, hb'] at hab <;> simp at hab ⊢
        subst huv; subst hb
        have hbad1 : BadIn E 1 := by
          refine ⟨fun _ => u, fun _ => true, rfl, by simp, fun i hi => ?_⟩
          exact he
        exact hming 1 (by omega) hbad1
      rw [Finset.card_pair hneq] at hpw
      exact hpw
  exact ⟨h2g_L, h2g_h, hw_ge⟩

private lemma pref_succ (s : ℕ → Bool) (k : ℕ) :
    (((Finset.range (k + 1)).filter (fun i => s i = true)).card % 2 == 1) =
      ((((Finset.range k).filter (fun i => s i = true)).card % 2 == 1) ^^ s k) := by
  have hfilt : (Finset.range (k + 1)).filter (fun i => s i = true) =
      (Finset.range k).filter (fun i => s i = true) ∪ (if s k = true then {k} else ∅) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    by_cases hik : i < k
    · simp [hik, show i < k + 1 by omega]
      split_ifs <;> simp [show i ≠ k by omega]
    · by_cases heq : i = k
      · subst heq
        simp only [lt_irrefl, lt_add_iff_pos_right, zero_lt_one, true_and,
          false_and, false_or]
        cases s i <;> simp
      · simp only [show ¬(i < k + 1) by omega, false_and, false_iff, not_or, not_and]
        refine ⟨fun h => absurd h hik, ?_⟩
        split_ifs <;> simp [heq]
  rw [hfilt, Finset.card_union_of_disjoint]
  · cases hsk : s k
    · simp
    · simp only [↓reduceIte, Finset.card_singleton, Bool.xor_true]
      set c := ((Finset.range k).filter (fun i => s i = true)).card
      have hmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
      rcases hmod with h0 | h1
      · simp [Nat.add_mod, h0]
      · simp [Nat.add_mod, h1]
  · split_ifs
    · simp
    · exact Finset.disjoint_empty_right _

private def buildChain {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (g : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool)
    (hv0 : v 0 = v g) (hodd : Odd (((Finset.range g).filter (fun i => s i = true)).card))
    (hedge : ∀ i < g, E (v i) (v (i + 1)) (s i))
    (hming : ∀ j < g, ¬ BadIn E j)
    (c : Bool) :
    ∀ (d l len : ℕ), 1 ≤ len → len ≤ 2 ^ d → l + len ≤ g →
      { T : Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Fin n)) //
        let nodes := T.1
        let inner := T.2.1
        let line := T.2.2
        let pref := fun k => (((Finset.range k).filter (fun i => s i = true)).card % 2 == 1)
        [] ∈ nodes ∧ inner ⊆ nodes ∧
        line [] = {(v l, !(c ^^ pref l)), (v (l + len), c ^^ pref (l + len))} ∧
        (∀ p ∈ nodes, p.length ≤ d ∧ (line p).card ≤ (if g = 1 then 1 else 2)) ∧
        (nodes \ inner).card = len ∧
        (∀ p ∈ nodes, p ∉ inner →
          ∃ (u w : Fin n) (b a : Bool), E u w b ∧ line p = {(u, !a), (w, a ^^ b)}) ∧
        (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) ∧
        (∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
          IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) } := by
  classical
  intro d
  induction d with
  | zero =>
    intro l len hlen1 hlen2 hlg
    have hlen_eq : len = 1 := by simp at hlen2; omega
    subst hlen_eq
    let pref := fun k => (((Finset.range k).filter (fun i => s i = true)).card % 2 == 1)
    let cl : Clause (Fin n) := {(v l, !(c ^^ pref l)), (v (l + 1), c ^^ pref (l + 1))}
    refine ⟨({[]}, ∅, fun _ => cl), by simp, Finset.empty_subset _, rfl, ?_, by simp, ?_, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      refine ⟨le_rfl, ?_⟩
      split_ifs with hg1
      · subst hg1
        have hl0 : l = 0 := by omega
        subst hl0
        have hs0 : s 0 = true := by
          cases h : s 0
          · simp [Finset.range_one, Finset.filter_singleton, h] at hodd
          · rfl
        have hpref0 : pref 0 = false := rfl
        have hpref1 : pref 1 = true := by simp [pref, Finset.range_one, Finset.filter_singleton, hs0]
        simp only [cl, hv0, hpref0, hpref1, Bool.xor_false, Bool.xor_true, Finset.pair_eq_singleton]
        simp
      · exact Finset.card_le_two
    · intro p _ _
      refine ⟨v l, v (l + 1), s l, c ^^ pref l, hedge l (by omega), ?_⟩
      simp only [cl, pref]
      rw [pref_succ s l, Bool.xor_assoc]
    · intro p bit hp
      rw [Finset.mem_singleton] at hp
      have := congrArg List.length hp
      simp at this
    · intro p hp
      simp at hp
  | succ d ih =>
    intro l len hlen1 hlen2 hlg
    let pref := fun k => (((Finset.range k).filter (fun i => s i = true)).card % 2 == 1)
    by_cases hlen_one : len = 1
    · subst hlen_one
      let cl : Clause (Fin n) := {(v l, !(c ^^ pref l)), (v (l + 1), c ^^ pref (l + 1))}
      refine ⟨({[]}, ∅, fun _ => cl), by simp, Finset.empty_subset _, rfl, ?_, by simp, ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        refine ⟨Nat.zero_le _, ?_⟩
        split_ifs with hg1
        · subst hg1
          have hl0 : l = 0 := by omega
          subst hl0
          have hs0 : s 0 = true := by
            cases h : s 0
            · simp [Finset.range_one, Finset.filter_singleton, h] at hodd
            · rfl
          have hpref0 : pref 0 = false := rfl
          have hpref1 : pref 1 = true := by simp [pref, Finset.range_one, Finset.filter_singleton, hs0]
          simp only [cl, hv0, hpref0, hpref1, Bool.xor_false, Bool.xor_true, Finset.pair_eq_singleton]
          simp
        · exact Finset.card_le_two
      · intro p _ _
        refine ⟨v l, v (l + 1), s l, c ^^ pref l, hedge l (by omega), ?_⟩
        simp only [cl, pref]
        rw [pref_succ s l, Bool.xor_assoc]
      · intro p bit hp
        rw [Finset.mem_singleton] at hp
        have := congrArg List.length hp
        simp at this
      · intro p hp
        simp at hp
    · have hlen2' : 2 ≤ len := by omega
      let len1 := len / 2
      let len2 := len - len1
      have hlen1_ge : 1 ≤ len1 := by omega
      have hlen2_ge : 1 ≤ len2 := by omega
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      have hlen1_le : len1 ≤ 2 ^ d := by omega
      have hlen2_le : len2 ≤ 2 ^ d := by omega
      let T1 := ih l len1 hlen1_ge hlen1_le (by omega)
      let T2 := ih (l + len1) len2 hlen2_ge hlen2_le (by omega)
      let m := l + len1
      let pm : Bool := c ^^ pref m
      let Tl := if pm = true then T1.val else T2.val
      let Tr := if pm = true then T2.val else T1.val
      let nodes : Finset (List Bool) :=
        insert [] (Tl.1.image (fun p => false :: p) ∪ Tr.1.image (fun p => true :: p))
      let inner : Finset (List Bool) :=
        insert [] (Tl.2.1.image (fun p => false :: p) ∪ Tr.2.1.image (fun p => true :: p))
      let rootCl : Clause (Fin n) := {(v l, !(c ^^ pref l)), (v (l + len), c ^^ pref (l + len))}
      let line : List Bool → Clause (Fin n) := fun p =>
        match p with
        | [] => rootCl
        | false :: rest => Tl.2.2 rest
        | true :: rest => Tr.2.2 rest
      have hTl_prop :
          [] ∈ Tl.1 ∧ Tl.2.1 ⊆ Tl.1 ∧
          (∀ p ∈ Tl.1, p.length ≤ d ∧ (Tl.2.2 p).card ≤ (if g = 1 then 1 else 2)) ∧
          (∀ p ∈ Tl.1, p ∉ Tl.2.1 →
            ∃ (u w : Fin n) (b a : Bool), E u w b ∧ Tl.2.2 p = {(u, !a), (w, a ^^ b)}) ∧
          (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ Tl.1 → p ∈ Tl.2.1) ∧
          (∀ p ∈ Tl.2.1, p ++ [false] ∈ Tl.1 ∧ p ++ [true] ∈ Tl.1 ∧
            IsResolvent (Tl.2.2 (p ++ [false])) (Tl.2.2 (p ++ [true])) (Tl.2.2 p)) := by
        by_cases hpm : pm = true
        · simp only [Tl, hpm, ↓reduceIte]
          exact ⟨T1.property.1, T1.property.2.1, T1.property.2.2.2.1, T1.property.2.2.2.2.2.1,
            T1.property.2.2.2.2.2.2.1, T1.property.2.2.2.2.2.2.2⟩
        · simp only [Tl, hpm, ↓reduceIte]
          exact ⟨T2.property.1, T2.property.2.1, T2.property.2.2.2.1, T2.property.2.2.2.2.2.1,
            T2.property.2.2.2.2.2.2.1, T2.property.2.2.2.2.2.2.2⟩
      have hTr_prop :
          [] ∈ Tr.1 ∧ Tr.2.1 ⊆ Tr.1 ∧
          (∀ p ∈ Tr.1, p.length ≤ d ∧ (Tr.2.2 p).card ≤ (if g = 1 then 1 else 2)) ∧
          (∀ p ∈ Tr.1, p ∉ Tr.2.1 →
            ∃ (u w : Fin n) (b a : Bool), E u w b ∧ Tr.2.2 p = {(u, !a), (w, a ^^ b)}) ∧
          (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ Tr.1 → p ∈ Tr.2.1) ∧
          (∀ p ∈ Tr.2.1, p ++ [false] ∈ Tr.1 ∧ p ++ [true] ∈ Tr.1 ∧
            IsResolvent (Tr.2.2 (p ++ [false])) (Tr.2.2 (p ++ [true])) (Tr.2.2 p)) := by
        by_cases hpm : pm = true
        · simp only [Tr, hpm, ↓reduceIte]
          exact ⟨T2.property.1, T2.property.2.1, T2.property.2.2.2.1, T2.property.2.2.2.2.2.1,
            T2.property.2.2.2.2.2.2.1, T2.property.2.2.2.2.2.2.2⟩
        · simp only [Tr, hpm, ↓reduceIte]
          exact ⟨T1.property.1, T1.property.2.1, T1.property.2.2.2.1, T1.property.2.2.2.2.2.1,
            T1.property.2.2.2.2.2.2.1, T1.property.2.2.2.2.2.2.2⟩
      have hsdiff : nodes \ inner =
          (Tl.1 \ Tl.2.1).image (fun p => false :: p) ∪
          (Tr.1 \ Tr.2.1).image (fun p => true :: p) := by
        ext p
        cases p with
        | nil => simp [nodes, inner]
        | cons b rest =>
          cases b
          · simp [nodes, inner]
          · simp [nodes, inner]
      have hcard_sdiff : (nodes \ inner).card = len := by
        rw [hsdiff, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
            Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2)]
          by_cases hpm : pm = true
          · simp only [Tl, Tr, hpm, ↓reduceIte]
            rw [T1.property.2.2.2.2.1, T2.property.2.2.2.2.1]; omega
          · simp only [Tl, Tr, hpm, Bool.false_eq_true, ↓reduceIte]
            rw [T2.property.2.2.2.2.1, T1.property.2.2.2.2.1]; omega
        · rw [Finset.disjoint_left]
          intro p h1 h2
          obtain ⟨q1, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨q2, _, hq2⟩ := Finset.mem_image.mp h2
          simp at hq2
      refine ⟨(nodes, inner, line), by simp [nodes], ?_, rfl, ?_, hcard_sdiff, ?_, ?_, ?_⟩
      · intro p hp
        simp only [inner, nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨q, hTl_prop.2.1 hq, rfl⟩)
        · exact Or.inr (Or.inr ⟨q, hTr_prop.2.1 hq, rfl⟩)
      · intro p hp
        simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · refine ⟨Nat.zero_le _, ?_⟩
          have hgne1 : g ≠ 1 := by omega
          simp only [hgne1, ↓reduceIte, line, rootCl]
          exact Finset.card_le_two
        · have := hTl_prop.2.2.1 q hq
          exact ⟨by simp; omega, this.2⟩
        · have := hTr_prop.2.2.1 q hq
          exact ⟨by simp; omega, this.2⟩
      · intro p hp hpi
        have hmem : p ∈ nodes \ inner := Finset.mem_sdiff.mpr ⟨hp, hpi⟩
        rw [hsdiff, Finset.mem_union] at hmem
        rcases hmem with h1 | h2
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
          exact hTl_prop.2.2.2.1 q (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hq).2
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h2
          exact hTr_prop.2.2.2.1 q (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hq).2
      · intro p bit hp
        cases p with
        | nil => simp [inner]
        | cons b rest =>
          cases b
          · have h1 : rest ++ [bit] ∈ Tl.1 := by
              simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union,
                Finset.mem_image] at hp
              rcases hp with h | ⟨q, hq, heq⟩ | ⟨q, _, heq⟩
              · simp at h
              · cases heq; exact hq
              · simp at heq
            have h2 := hTl_prop.2.2.2.2.1 rest bit h1
            simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨rest, h2, rfl⟩)
          · have h1 : rest ++ [bit] ∈ Tr.1 := by
              simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union,
                Finset.mem_image] at hp
              rcases hp with h | ⟨q, _, heq⟩ | ⟨q, hq, heq⟩
              · simp at h
              · simp at heq
              · cases heq; exact hq
            have h2 := hTr_prop.2.2.2.2.1 rest bit h1
            simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨rest, h2, rfl⟩)
      · intro p hp
        simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · refine ⟨?_, ?_, ?_⟩
          · simp only [nodes, List.nil_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨[], hTl_prop.1, rfl⟩)
          · simp only [nodes, List.nil_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨[], hTr_prop.1, rfl⟩)
          · have hdist := shortest_bad_vertices_distinct hv0 hodd hedge hming
            have hml : v m ≠ v l := (hdist l m (by omega) (by omega)).symm
            have hmr : v m ≠ v (l + len) := by
              by_cases hfull : l + len = g
              · rw [hfull, ← hv0]
                exact (hdist 0 m (by omega) (by omega)).symm
              · exact hdist m (l + len) (by omega) (by omega)
            have hT1_root : T1.val.2.2 [] = {(v l, !(c ^^ pref l)), (v m, pm)} := T1.property.2.2.1
            have hT2_root : T2.val.2.2 [] = {(v m, !pm), (v (l + len), c ^^ pref (l + len))} := by
              have h := T2.property.2.2.1
              have hsum : l + len1 + len2 = l + len := by omega
              exact h.trans (by rw [hsum])
            refine ⟨v m, ?_, ?_, ?_⟩
            · simp only [line, List.nil_append, Tl]
              cases hpm : pm
              · simp only [Bool.false_eq_true, ↓reduceIte, hT2_root, hpm, Bool.not_false]
                simp
              · simp only [↓reduceIte, hT1_root, hpm]
                simp
            · simp only [line, List.nil_append, Tr]
              cases hpm : pm
              · simp only [Bool.false_eq_true, ↓reduceIte, hT1_root, hpm]
                simp
              · simp only [↓reduceIte, hT2_root, hpm, Bool.not_true]
                simp
            · simp only [line, List.nil_append, rootCl, Tl, Tr]
              have hne1 : (v l, !(c ^^ pref l)) ≠ (v m, true) := fun h => hml (congrArg Prod.fst h).symm
              have hne2 : (v l, !(c ^^ pref l)) ≠ (v m, false) := fun h => hml (congrArg Prod.fst h).symm
              have hne3 : (v (l + len), c ^^ pref (l + len)) ≠ (v m, true) := fun h => hmr (congrArg Prod.fst h).symm
              have hne4 : (v (l + len), c ^^ pref (l + len)) ≠ (v m, false) := fun h => hmr (congrArg Prod.fst h).symm
              cases hpm : pm
              · simp only [Bool.false_eq_true, ↓reduceIte, hT1_root, hT2_root, hpm, Bool.not_false]
                ext z
                simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
                constructor
                · rintro (rfl | rfl)
                  · exact Or.inr ⟨hne2, Or.inl rfl⟩
                  · exact Or.inl ⟨hne3, Or.inr rfl⟩
                · rintro (⟨h1, rfl | rfl⟩ | ⟨h1, rfl | rfl⟩)
                  · exact absurd rfl h1
                  · exact Or.inr rfl
                  · exact Or.inl rfl
                  · exact absurd rfl h1
              · simp only [↓reduceIte, hT1_root, hT2_root, hpm, Bool.not_true]
                ext z
                simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
                constructor
                · rintro (rfl | rfl)
                  · exact Or.inl ⟨hne1, Or.inl rfl⟩
                  · exact Or.inr ⟨hne4, Or.inr rfl⟩
                · rintro (⟨h1, rfl | rfl⟩ | ⟨h1, rfl | rfl⟩)
                  · exact Or.inl rfl
                  · exact absurd rfl h1
                  · exact absurd rfl h1
                  · exact Or.inr rfl
        · obtain ⟨hf, ht, hres⟩ := hTl_prop.2.2.2.2.2 q hq
          refine ⟨?_, ?_, hres⟩
          · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨q ++ [false], hf, rfl⟩)
          · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨q ++ [true], ht, rfl⟩)
        · obtain ⟨hf, ht, hres⟩ := hTr_prop.2.2.2.2.2 q hq
          refine ⟨?_, ?_, hres⟩
          · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨q ++ [false], hf, rfl⟩)
          · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨q ++ [true], ht, rfl⟩)

private theorem main_aux : ∀ (n : ℕ) (E : Fin n → Fin n → Bool → Prop),
    (∀ u v b, E u v b → E v u b) →
    let bad := fun m : ℕ => ∃ (v : ℕ → Fin n) (s : ℕ → Bool),
      v 0 = v m ∧ Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
      ∀ i < m, E (v i) (v (i + 1)) (s i)
    let ax := fun C : Clause (Fin n) =>
      ∃ (u v : Fin n) (b a : Bool), E u v b ∧ C = {(u, !a), (v, a ^^ b)}
    ∀ g : ℕ, bad g → (∀ j < g, ¬ bad j) →
      ∀ L h w : ℕ,
        (∃ (nodes inner : Finset (List Bool)) (line : List Bool → Clause (Fin n)),
          [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
          (∀ p ∈ nodes, p.length ≤ h ∧ (line p).card ≤ w) ∧
          (nodes \ inner).card ≤ L ∧ (∀ p ∈ nodes, p ∉ inner → ax (line p)) ∧
          (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) ∧
          ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
            IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) ↔
        2 * g ≤ L ∧ 2 * g ≤ 2 ^ h ∧ (if g = 1 then 1 else 2) ≤ w := by
  intro n E hEsym
  dsimp only
  intro g hbadg hming L h w
  constructor
  · rintro ⟨nodes, inner, line, hroot, hsub, hempty, hbw, hL, hax, hup, hstep⟩
    exact lower_bound E hEsym g hbadg hming L h w nodes inner line hroot hsub hempty hbw hL hax hup hstep
  · rintro ⟨hL, hh, hw⟩
    obtain ⟨v, s, hv0, hodd, hedge⟩ := hbadg
    have hgpos : 1 ≤ g := by
      by_contra h0
      have hg0 : g = 0 := by omega
      subst hg0
      simp at hodd
    have hhpos : 1 ≤ h := by
      by_contra h0
      have hh0 : h = 0 := by omega
      subst hh0
      simp at hh
      omega
    have hgle : g ≤ 2 ^ (h - 1) := by
      have : 2 ^ h = 2 * 2 ^ (h - 1) := by
        conv_lhs => rw [show h = (h - 1) + 1 by omega, Nat.pow_succ]
        omega
      omega
    let T1 := buildChain E g v s hv0 hodd hedge hming false (h - 1) 0 g hgpos hgle (by omega)
    let T2 := buildChain E g v s hv0 hodd hedge hming true (h - 1) 0 g hgpos hgle (by omega)
    let nodes : Finset (List Bool) :=
      insert [] (T1.val.1.image (fun p => false :: p) ∪ T2.val.1.image (fun p => true :: p))
    let inner : Finset (List Bool) :=
      insert [] (T1.val.2.1.image (fun p => false :: p) ∪ T2.val.2.1.image (fun p => true :: p))
    let line : List Bool → Clause (Fin n) := fun p =>
      match p with
      | [] => ∅
      | false :: rest => T1.val.2.2 rest
      | true :: rest => T2.val.2.2 rest
    have hsdiff : nodes \ inner =
        (T1.val.1 \ T1.val.2.1).image (fun p => false :: p) ∪
        (T2.val.1 \ T2.val.2.1).image (fun p => true :: p) := by
      ext p
      cases p with
      | nil => simp [nodes, inner]
      | cons b rest =>
        cases b
        · simp [nodes, inner]
        · simp [nodes, inner]
    have hcard_sdiff : (nodes \ inner).card = 2 * g := by
      rw [hsdiff, Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
          Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
          T1.property.2.2.2.2.1, T2.property.2.2.2.2.1]
        omega
      · rw [Finset.disjoint_left]
        intro p h1 h2
        obtain ⟨q1, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨q2, _, hq2⟩ := Finset.mem_image.mp h2
        simp at hq2
    refine ⟨nodes, inner, line, by simp [nodes], ?_, rfl, ?_, by omega, ?_, ?_, ?_⟩
    · intro p hp
      simp only [inner, nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨q, T1.property.2.1 hq, rfl⟩)
      · exact Or.inr (Or.inr ⟨q, T2.property.2.1 hq, rfl⟩)
    · intro p hp
      simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact ⟨Nat.zero_le _, by simp [line]⟩
      · have := T1.property.2.2.2.1 q hq
        exact ⟨by simp; omega, le_trans this.2 hw⟩
      · have := T2.property.2.2.2.1 q hq
        exact ⟨by simp; omega, le_trans this.2 hw⟩
    · intro p hp hpi
      have hmem : p ∈ nodes \ inner := Finset.mem_sdiff.mpr ⟨hp, hpi⟩
      rw [hsdiff, Finset.mem_union] at hmem
      rcases hmem with h1 | h2
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
        exact T1.property.2.2.2.2.2.1 q (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hq).2
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h2
        exact T2.property.2.2.2.2.2.1 q (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hq).2
    · intro p bit hp
      cases p with
      | nil => simp [inner]
      | cons b rest =>
        cases b
        · have h1 : rest ++ [bit] ∈ T1.val.1 := by
            simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union,
              Finset.mem_image] at hp
            rcases hp with h | ⟨q, hq, heq⟩ | ⟨q, _, heq⟩
            · simp at h
            · cases heq; exact hq
            · simp at heq
          have h2 := T1.property.2.2.2.2.2.2.1 rest bit h1
          simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inl ⟨rest, h2, rfl⟩)
        · have h1 : rest ++ [bit] ∈ T2.val.1 := by
            simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union,
              Finset.mem_image] at hp
            rcases hp with h | ⟨q, _, heq⟩ | ⟨q, hq, heq⟩
            · simp at h
            · simp at heq
            · cases heq; exact hq
          have h2 := T2.property.2.2.2.2.2.2.1 rest bit h1
          simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inr ⟨rest, h2, rfl⟩)
    · intro p hp
      simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · refine ⟨?_, ?_, ?_⟩
        · simp only [nodes, List.nil_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inl ⟨[], T1.property.1, rfl⟩)
        · simp only [nodes, List.nil_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inr ⟨[], T2.property.1, rfl⟩)
        · have hprefg : (((Finset.range g).filter (fun i => s i = true)).card % 2 == 1) = true := by
            rw [Nat.odd_iff] at hodd
            simp [hodd]
          have hT1_root : T1.val.2.2 [] = {(v 0, true)} := by
            have h := T1.property.2.2.1
            simp only [Nat.zero_add, ← hv0, hprefg, Finset.range_zero, Finset.filter_empty,
              Finset.card_empty, Nat.zero_mod, beq_iff_eq, zero_ne_one, decide_false] at h
            simpa using h
          have hT2_root : T2.val.2.2 [] = {(v 0, false)} := by
            have h := T2.property.2.2.1
            simp only [Nat.zero_add, ← hv0, hprefg, Finset.range_zero, Finset.filter_empty,
              Finset.card_empty, Nat.zero_mod, beq_iff_eq, zero_ne_one, decide_false] at h
            simpa using h
          refine ⟨v 0, ?_, ?_, ?_⟩
          · simp [line, hT1_root]
          · simp [line, hT2_root]
          · simp [line, hT1_root, hT2_root]
      · obtain ⟨hf, ht, hres⟩ := T1.property.2.2.2.2.2.2.2 q hq
        refine ⟨?_, ?_, hres⟩
        · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inl ⟨q ++ [false], hf, rfl⟩)
        · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inl ⟨q ++ [true], ht, rfl⟩)
      · obtain ⟨hf, ht, hres⟩ := T2.property.2.2.2.2.2.2.2 q hq
        refine ⟨?_, ?_, hres⟩
        · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inr ⟨q ++ [false], hf, rfl⟩)
        · simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
          exact Or.inr (Or.inr ⟨q ++ [true], ht, rfl⟩)

end PEqualNP.Outside.L_pcx_261_aux

theorem PEqualNP.Outside.L_pcx_261 : (∀ (n : ℕ) (E : Fin n → Fin n → Bool → Prop),
  (∀ u v b, E u v b → E v u b) →
  let bad := fun m : ℕ => ∃ (v : ℕ → Fin n) (s : ℕ → Bool),
    v 0 = v m ∧ Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
    ∀ i < m, E (v i) (v (i+1)) (s i)
  let ax := fun C : PEqualNP.ProofComplexity.Clause (Fin n) =>
    ∃ (u v : Fin n) (b a : Bool), E u v b ∧ C = {(u,!a),(v,a ^^ b)}
  ∀ g : ℕ, bad g → (∀ j < g, ¬ bad j) →
    ∀ L h w : ℕ,
      (∃ (nodes inner : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause (Fin n)),
        [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
        (∀ p ∈ nodes, p.length ≤ h ∧ (line p).card ≤ w) ∧
        (nodes \ inner).card ≤ L ∧ (∀ p ∈ nodes, p ∉ inner → ax (line p)) ∧
        (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) ∧
        ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
          PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) ↔
      2*g ≤ L ∧ 2*g ≤ 2^h ∧ (if g = 1 then 1 else 2) ≤ w) :=
  PEqualNP.Outside.L_pcx_261_aux.main_aux
