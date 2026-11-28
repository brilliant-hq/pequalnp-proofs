import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51640_aux

variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure XW where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat

structure Inst where
  NN : Nat
  AA : Nat
  HX : Nat
  HY : Nat
  segsX : List (ℕ × ℕ)
  segsY : List (ℕ × ℕ)
  rawP : List ℕ
  TG : ℕ

def segOk (AA : ℕ) (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)

structure InstOk (I : Inst) : Prop where
  segX_ok : I.segsX.all (segOk I.AA) = true
  segY_ok : I.segsY.all (segOk I.AA) = true
  HX_eq : I.HX = bitsOf I.segsX
  HY_eq : I.HY = bitsOf I.segsY
  AA_TG : I.AA &&& I.TG = I.AA
  TG_lt : I.TG < 2 ^ I.NN
  AA_lt : I.AA < 2 ^ I.NN
  raw_good : I.rawP.all (fun w => I.segsX.all (segGood w 0) && I.segsY.all (segGood w I.NN)) = true
  rawP_len : I.rawP.length = 8

noncomputable section coreC
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def spC (NN : Nat) (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def covC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (spC NN d l w.s) ih) v
def twiceC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (spC NN d l w.s) (covC NN d l t)) ih) v
def hitC (HX HY : Nat) (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hitsC (HX HY : Nat) (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hitC HX HY f e))) (m))
def flagC (NN AA : Nat) (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (spC NN d l w.s) o) AA
def rectC (NN AA HX HY : Nat) (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flagC NN AA d l o w :: m)) (true) (hitsC HX HY (flagC NN AA d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def joinC (HX HY : Nat) (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hitsC HX HY f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hitsC HX HY f c.b)) (hitsC HX HY f c.a)) cs
def bipC (NN AA HX HY : Nat) (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => joinC HX HY ih f cs [f] [] []) (flagC NN AA false l o w)) v
def anyEC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hitsC HX HY f t)) m
def rmFC (HX HY : Nat) (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hitC HX HY f e)) m
def starC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyEC HX HY (rmFC HX HY f t))) false (hitsC HX HY f (rmFC HX HY f t))) (anyEC HX HY t)) (hitsC HX HY f t)) m
def flkC (NN AA : Nat) (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flagC NN AA false l o w)) v
def mkXC (NN : Nat) (d : Bool) (l o : Nat) (v : List W) : List XW :=
  List.rec (motive := fun _ => List XW) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (spC NN d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) fun remaining =>
    Bool.rec (motive := fun _ => Bool) false
      (kids (child f g) e n remaining a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v))
      (Nat.beq (Nat.land remaining g) g)
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Bool.rec (motive := fun _ => Bool) (Nat.beq dc 0) true (Nat.beq da 0)))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : XW → Bool) (xs : List XW) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : XW → XW → Bool) (xs : List XW) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : XW → XW → Bool) (xs : List XW) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : XW → XW → Bool) (xs : List XW) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wstC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twiceC NN d l v)
def nodeC (NN : Nat) (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cvC (NN : Nat) (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)
def tstC (NN AA HX HY : Nat) (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flkC NN AA l (wstC NN d l v) v (starC HX HY))) false (bipC NN AA HX HY l (wstC NN d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rectC NN AA HX HY d l (wstC NN d l v) v [])) (Nat.beq n e)) v.length
def mvC (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def lookC (NN AA HX HY : Nat) (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => cvC NN (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1))) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => cvC NN (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1))) fuel
end coreC

def bigNat_0 : Nat := 0xffffeffffefbffff7dffffbdf77fffefbdffffddffffbdf7bffff7bdbffff7beefbbbffeb56b6ab7ffaabffd55ffeadffedffedad5b56afff6d56bffdbffdab5adb56fff6fff6b56d7ffbffdb6fff0000000000000000
def bigNat_1 : Nat := 0x14a94954800554002aa001520012001252a4a9500092a94002400254a524a9000900094a928004002490000000000000000000
def bigNat_2 : Nat := 0x100001000010400008200004208800010420000220000420840000842400008411044400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0x1ffffc000000000000000000000003ffff8000000000000000007fffe07c1f070000000040642201211009089190919090000020008440021212121300010028c888c8880020a44422312488c000000000000000004046d544600012304005184110024608504f4c000858410801070848459703e0f8380460000603000008000040008c000c0000010300000001508001bffc0818034600060000850d0003ffdb6ffffb1b26c7ec74e930
def bigNat_4 : Nat := 0x3ffff03e000000000000000000000007fffe0787fffef001f7000000202000086000432202294023082380081020420cc22c08630860000410a0218421c4224210e08630c2280000000000000000082180061808120c090ec601f002098108080704081a0821094ba03c054ba7800fb80218010300000000000110000a0000dffe00c18102000611600018000204218500006fff631617ff800186000289adfbe3e7ad990
def bigNat_5 : Nat := 0x3ffff03e07fffef007fffef7dc0000000000000000e4400b2800694807800700000081002c482500f000e1020480a403c0038d02d802c0163600680000000000000000104a0018a01024501010a8082204520210111808956c01f00a6d2780066d27bee00004a0000800000022000140000adffe0000020404080006c16bffc00018302c056fff00006816c0000001b00003a33cd08dd25e728
def bigNat_6 : Nat := 0x7fffe03ffff7800ffffc078000003ffff78007fffef7b000000000000000102401101cc500ea2a077000760076185a00ac06a8da801ac01ac35005b4007300730d68003a81d424877000000000000000002080206002224f010126c0bc00491c203c202040a44cbc000c4937bd8800300200808802816008800028000155ffe000000000c2d005600006d4000000001a802db0000000006b4000000001b6fff7c284fed028b254b
def bigNat_7 : Nat := 0xffffdf00000003ffff7bef00000000000000000000000000001400485402c000140001400140900008500b000000280028356a000001200120948900b005800014000000000000000004110c1810c4088862043031044519ccf80424180c64f3df79081c0081081c0840109110c04000a00002abffc00000000000000d800056afff000000000001ab58000000000006b56d7ffbffc0000051ff4ca4c6a68795
def bigNat_8 : Nat := 0x7fffef800000000ffffdf7bffffb8000000000000000000000000000000012000152170000b0000580005800581b52a60004c000001300130254b126085c085c0000002c016000058000000000000000008203060030830f187c840c0080611f0fbd847e1d00700040200e0110200e010822102030b0000ab7ff80000000000000000000dad5b000000000000000001ab5adb56fff6fff0000000000000000084bd5419e9fb170e
def bigNat_9 : Nat := 0x1ffffc0000007fffefbffff7bee00000000000000000000000000000000000000000000016ad6800980004c000260002600260125ab428570092885c025c0000000001600160000000b005800016000000000000000000fc1c0801c0020fe07d07f03df701e004000780000780108200f0020000f00210440201c0b56b60000000000000000000000000dad5b56afff6d56bffdbffc00000000000000000000000000000000a4cfbb63b53967a1
def bigNat_10 : Nat := 0x1ffffdffffdf00000000000000000000000000000000000000000000000000000000000004894c04e000170000b8001380138000000000180000006000600000000001800180000000c006000018000000000000000000ffe00ffe00fbf00041f80021007e000821f80011f80021043f0004213f00042088203e00b56b6ab7ffaabffd55ffeadffedffe000000000000000000000000000000000000000000000000000000026863f8391937ac7
def bigNat_11 : Nat := 0xffffeffffefbffff7dffffbdf77fffefbdffffddffffbdf7bffff7bdbffff7beefbbbffeb56b6ab7ffaabffd55ffeadffedffedad5b56afff6d56bffdbffdab5adb56fff6fff6b56d7ffbffdb6fffffffffffffffffff
def NN0 : Nat := 693
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 76), (76, 79), (79, 82), (82, 85), (85, 98), (98, 111), (111, 113), (113, 116), (116, 119), (119, 121), (121, 123), (123, 126), (126, 128), (128, 131), (131, 144), (144, 147), (147, 160), (160, 163), (163, 165), (165, 167), (167, 170), (170, 173), (173, 176), (176, 178), (178, 181), (181, 183), (183, 186), (186, 188), (188, 190), (190, 193), (193, 206), (206, 209), (209, 222), (222, 224), (224, 227), (227, 229), (229, 231), (231, 233), (233, 236), (236, 239), (239, 252), (252, 254), (254, 256), (256, 259), (259, 261), (261, 263), (263, 266), (266, 269), (269, 271), (271, 273), (273, 276), (276, 278), (278, 281), (281, 284), (284, 297), (297, 300), (300, 313), (313, 316), (316, 318), (318, 320), (320, 333), (333, 335), (335, 337), (337, 339), (339, 341), (341, 354), (354, 356), (356, 358), (358, 360), (360, 362), (362, 375), (375, 378), (378, 380), (380, 382), (382, 384), (384, 387), (387, 390), (390, 392), (392, 395), (395, 397), (397, 399), (399, 402), (402, 404)]
def segsY0 : List (ℕ × ℕ) := [(404, 418), (418, 422), (422, 426), (426, 432), (432, 436), (436, 442), (442, 447), (447, 466), (466, 469), (469, 474), (474, 479), (479, 498), (498, 503), (503, 509), (509, 514), (514, 533), (533, 537), (537, 557), (557, 562), (562, 568), (568, 587), (587, 591), (591, 597), (597, 602), (602, 621), (621, 627), (627, 646), (646, 652), (652, 672), (672, 692)]
def rawP0 : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8, bigNat_9, bigNat_10]
def TG0 : ℕ := bigNat_11
def I : Inst := ⟨NN0, AA0, HX0, HY0, segsX0, segsY0, rawP0, TG0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok0 : segsX0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok0 : segsY0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq0 : HX0 = bitsOf segsX0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq0 : HY0 = bitsOf segsY0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG0 : AA0 &&& TG0 = AA0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt0 : TG0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt0 : AA0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good0 : rawP0.all (fun w => segsX0.all (segGood w 0) && segsY0.all (segGood w NN0)) = true := by decide +kernel
lemma IOk : InstOk I := ⟨segX_ok0, segY_ok0, HX_eq0, HY_eq0, AA_TG0, TG_lt0, AA_lt0, raw_good0, rfl⟩

section engine

noncomputable section core
abbrev sp := spC I.NN
abbrev cov := covC I.NN
abbrev twice := twiceC I.NN
abbrev hit := hitC I.HX I.HY
abbrev hits := hitsC I.HX I.HY
abbrev flag := flagC I.NN I.AA
abbrev rect := rectC I.NN I.AA I.HX I.HY
abbrev join := joinC I.HX I.HY
abbrev bip := bipC I.NN I.AA I.HX I.HY
abbrev anyE := anyEC I.HX I.HY
abbrev rmF := rmFC I.HX I.HY
abbrev star := starC I.HX I.HY
abbrev flk := flkC I.NN I.AA
abbrev mkX := mkXC I.NN
abbrev wst := wstC I.NN
abbrev node := nodeC I.NN
abbrev cv := cvC I.NN
abbrev tst := tstC I.NN I.AA I.HX I.HY
abbrev mv := mvC I.NN I.AA I.HX I.HY
abbrev look := lookC I.NN I.AA I.HX I.HY
abbrev look1 := look1C I.NN I.AA I.HX I.HY
end core

lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb I.NN d s i) := by
  cases d <;> simp [sp, spC, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (I.NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov, covC]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq I.NN d S w.s i := by
  simp only [nl, wst, wstC, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this

section engine_ok
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same I.segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same I.segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (I.NN + i) = s.testBit (I.NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all (segOk I.AA) = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → I.AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + I.AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ I.segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ I.segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, hitC, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) I.HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) I.HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [IOk.HX_eq] at a3; rw [IOk.HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg I.NN m T i ∧ I.AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (I.NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb I.NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (I.NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (I.NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : XW := ⟨w, w.s, Nat.shiftRight w.s I.NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Bool.rec (motive := fun _ => Bool) (Nat.beq dc 0) true (Nat.beq da 0) = true := by
        rcases this with h | h
        · simp [h]
        · cases Nat.beq da 0 <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s I.NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → I.AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (I.NN + j1) = w.testBit (I.NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht I.NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → I.AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq I.NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb I.NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht I.NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := I.NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simpa only [cv, cvC, hcov] using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (I.NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (I.NN + i) = (a.s ^^^ m).testBit (I.NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : XW → Bool} {xs : List XW} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : XW → XW → Bool} {xs : List XW} {q : ℕ} {a c : XW} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : XW → XW → Bool} {xs : List XW} {q q' : ℕ} {a c : XW} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : XW => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : XW → XW → Bool} {xs : List XW} (hp : pairsN h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg XW.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look, lookC] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pos_eq] at h
    have h := cv_ok X hs hm.1 h
    rw [bR] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (XW → XW → Bool) → List XW → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1, look1C] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pos_eq] at h
    have h := cv_ok X hs hl h
    rw [bR] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e))
end sound

end engine_ok
def xw (e : ℕ × ℕ) : ℕ := I.rawP.getD e.1 0 ||| I.rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := I.rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ I.NN - 1
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i bad =>
  let a := I.rawP.getD i 0
  let b := Nat.shiftRight a I.NN
  let bad0 := bif Z.testBit i then (a ||| b) &&& FULL else 0
  let bad1 := bif Z.testBit (8+i) then (a &&& b &&& FULL) ^^^ FULL else 0
  bad ||| bad0 ||| bad1) 0
def lz (Z : ℕ) : ℕ := Nat.land I.AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) I.NN)
def tz (Z : ℕ) : ℕ := Nat.land I.TG (mz Z)

section engine_ok2
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg I.NN (mz Z) (tz Z) i ∧ I.AA.testBit i = true := by
  have hA : I.AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : I.TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) IOk.AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (I.NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< I.NN).testBit (I.NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le IOk.TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 IOk.raw_good w (by simpa [rawG, rawL, six] using hw)
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySubC (NN : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (covC NN d l t)) l)) true
    (st (Nat.lor c (spC NN d l w.s)) fun c => ih c fun r => h (w :: r))) v
abbrev anySub := anySubC I.NN
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topCC (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
abbrev topC := topCC I.NN I.AA I.HX I.HY
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startvC (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topCC NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
abbrev startv := startvC I.NN I.AA I.HX I.HY
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : XW → XW → Bool} {xs : List XW} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : XW => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startvC nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
theorem imp_of_live {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
theorem imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 (L - 1) t p.1 p.2 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr h)
lemma one {E Q : List (ℕ × ℕ)} {K t : ℕ} (h : chk E Q 0 K t FF 1 = false) : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩

end engine_ok2

end engine
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
theorem fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

def UniqueNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j

lemma UniqueNot.tail {g : Gate} {gs : List Gate} (h : UniqueNot (g :: gs)) : UniqueNot gs := by
  intro i j hi hj
  let i' : Fin (g :: gs).length := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let j' : Fin (g :: gs).length := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  have he := congrArg Fin.val (h i' j' hi hj)
  apply Fin.ext
  dsimp [i', j'] at he
  omega

lemma UniqueNot.tail_of_head {g : Gate} {gs : List Gate} (h : UniqueNot (g :: gs)) (hg : g.op = .not) :
    ∀ a ∈ gs, a.op ≠ .not := by
  intro a ha hnot
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  let j : Fin (g :: gs).length := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let z : Fin (g :: gs).length := ⟨0, by simp⟩
  have hj : ((g :: gs).get j).op = .not := by
    change (gs.get i).op = .not
    rw [hi, hnot]
  have he := congrArg Fin.val (h z j hg hj)
  dsimp [z, j] at he
  omega

lemma Live.add_binary {m T k t : ℕ} {S : Set ℕ} {S1 : Finset ℕ} {d : Bool} {a b : ℕ}
    (hl : Live Z0 m T k t S1) (hs : (S1 : Set ℕ) ⊆ insert (op d a b) S) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ k' ≤ k + 1, ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ S ∧ Live Z0 m T k' t S' := by
  by_cases hg : op d a b ∈ S1
  · by_cases hab : a = b
    · subst hab
      rw [op_self] at hs
      exact ⟨k, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
    · refine ⟨k + 1, le_rfl, insert a (insert b (S1.erase (op d a b))), ?_,
        .bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

lemma ex_mono_live {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k ≤ gs.length, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k 0 S0 := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact ⟨0, by simp, _, by simpa [ex] using getD_mem hw h0 i, .stop⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → ∃ k ≤ (g :: gs).length, ∃ S0 : Finset ℕ,
        (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k 0 S0 := by
      intro h
      obtain ⟨k, hk, S0, hS0, hl⟩ := ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT
      exact ⟨k, by simp; omega, S0, hS0, hl⟩
    have go := ih (w ++ [gv m w g]) (insert (gv m w g) S) (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    have hop := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    rcases hop with rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        obtain ⟨k, hk, S0, hS0, hl⟩ := go
        obtain ⟨k', hk', S', hS', hl'⟩ := Live.add_binary (d := false) hl hS0 (rd i) (rd j)
        exact ⟨k', by simp; omega, S', hS', hl'⟩
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        obtain ⟨k, hk, S0, hS0, hl⟩ := go
        obtain ⟨k', hk', S', hS', hl'⟩ := Live.add_binary (d := true) hl hS0 (rd i) (rd j)
        exact ⟨k', by simp; omega, S', hS', hl'⟩

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    UniqueNot gs → (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length 1 S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg huniq hnot hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have hwm_stay : gv m w g ∈ S → ∀ x ∈ w ++ [gv m w g], x ∈ S := fun h x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hw x hx; exact h
    have hwm_ins : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact Or.inr (hw x hx); exact Or.inl rfl
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs huniq.tail hnot' hT with hs | ⟨S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs huniq.tail hnot' hT with hs | ⟨S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have hgsMono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
          intro g hg
          have hne := huniq.tail_of_head (by rfl) g hg
          have ho := (hgs g hg).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
          rcases ho with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hne h).elim
        obtain ⟨k, hk, S1, hS1, hl1⟩ := ex_mono_live m gs
          (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S)
          hwm_ins (Or.inr h0) (Or.inr hm) hgsMono hT
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) 1 (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨_, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))

lemma scan_eq_any (p : XW → Bool) (xs : List XW) : scan p xs = xs.any p := by
  induction xs with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (motive := fun _ => Bool) (scan p ws) true (p w) = _
    rw [ih, bR]
    cases h : p w <;> simp [List.any_cons, h]

lemma pairsC_eq (H : ℕ) (f : XW → XW → Bool) (a : XW) (xs : List XW) :
    pairsC H f (a :: xs) =
      (xs.any (fun x => hb H (a.s + x.s) && f a x) || pairsC H f xs) := by
  have he : (fun x : XW => bif hb H (a.s + x.s) then f a x else false) =
      (fun x : XW => hb H (a.s + x.s) && f a x) := by
    funext x
    cases hb H (a.s + x.s) <;> rfl
  change Bool.rec (motive := fun _ => Bool) (pairsC H f xs) true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (f a x) (hb H (a.s + x.s))) xs) = _
  rw [bR, scan_eq_any]
  simp only [bR, he]
  cases xs.any (fun x => hb H (a.s + x.s) && f a x) <;> rfl

def possibleInputPair (H : ℕ) (v : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a rest later =>
      Bool.rec (motive := fun _ => Bool) later true (rest.any fun b => hb H (a.s + b.s))) v

lemma possibleInputPair_cons (H : ℕ) (a : W) (v : List W) :
    possibleInputPair H (a :: v) = ((v.any fun b => hb H (a.s + b.s)) || possibleInputPair H v) := by
  change Bool.rec (motive := fun _ => Bool) (possibleInputPair H v) true
    (v.any fun b => hb H (a.s + b.s)) = _
  cases v.any (fun b => hb H (a.s + b.s)) <;> rfl

lemma mkXC_map (nn : ℕ) (d : Bool) (l o : ℕ) (v : List W) :
    mkXC nn d l o v = v.map (fun w => ⟨w, w.s, Nat.shiftRight w.s nn, Nat.land (spC nn d l w.s) o⟩) := by
  induction v with
  | nil => rfl
  | cons w v ih =>
    change _ :: mkXC nn d l o v = _ :: _
    rw [ih]

lemma fs_eq_filter (xs : List XW) : fs xs = xs.filter (fun x => !Nat.beq x.w.r 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0) = _
    rw [ih]
    cases h : Nat.beq x.w.r 0 <;> simp [h]

lemma fr_eq_filter (xs : List XW) : fr xs = xs.filter (fun x => Nat.beq x.w.r 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0) = _
    rw [ih]
    cases h : Nat.beq x.w.r 0 <;> simp [h]

lemma pairImpossible {H nn l o : ℕ} {d : Bool} {v : List W} (f : XW → XW → Bool)
    (h : possibleInputPair H v = false) :
    pairsC H f (fs (mkXC nn d l o v)) = false := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [possibleInputPair_cons, Bool.or_eq_false_iff] at h
    let a' : XW := ⟨a, a.s, Nat.shiftRight a.s nn, Nat.land (spC nn d l a.s) o⟩
    change pairsC H f (Bool.rec (motive := fun _ => List XW)
      (a' :: fs (mkXC nn d l o v)) (fs (mkXC nn d l o v)) (Nat.beq a.r 0)) = _
    cases ha : Nat.beq a.r 0
    · change pairsC H f (a' :: fs (mkXC nn d l o v)) = false
      rw [pairsC_eq, ih h.2, Bool.or_false]
      apply List.any_eq_false.mpr
      intro x hx
      rw [fs_eq_filter, List.mem_filter, mkXC_map, List.mem_map] at hx
      obtain ⟨⟨w, hw, rfl⟩, _⟩ := hx
      intro hit
      simp only [Bool.and_eq_true] at hit
      exact List.any_eq_false.mp h.1 w hw hit.1
    · exact ih h.2

lemma noGenerated {nn l o : ℕ} {d : Bool} {v : List W}
    (h : v.any (fun w => Nat.beq w.r 0) = false) : fr (mkXC nn d l o v) = [] := by
  rw [fr_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  rw [mkXC_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact List.any_eq_false.mp h w hw

lemma noMoves {v : List W} (h : v.any (fun w => Nat.beq w.r 0) = false)
    (nn aa hx hy l m g k z y : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool) :
    mvC nn aa hx hy F l m g k 0 z v y = false := by
  have hp (f : XW → XW → Bool) : pairsN f (mkXC nn false l (wstC nn false l v) v) = false := by
    rw [pairsN, noGenerated h]; rfl
  have hnode : nodeC nn (F (Nat.sub k 1) 0) false l m g
      (Nat.sub (Nat.sub k 0) y) v.length z v pairsN = false := by
    simp only [nodeC, hp, bR, Bool.cond_self]
  simp only [mvC, show pos 0 = false from rfl, hnode, show ∀ f, prd 0 f = false by intro; rfl, bR]

lemma noNode {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodeC nn f d l m g e n z v (fun h xs => pairsC H h (fs xs)) = false := by
  simp only [nodeC, pairImpossible _ h, bR, Bool.cond_self]

lemma tst_const_false (nn aa hx hy : ℕ) (d : Bool) (l e : ℕ) (v : List W) :
    tstC nn aa hx hy d l e v (fun _ => false) = false := by
  simp only [tstC, bR, Bool.cond_self]

def relevantStart (t H ph : ℕ) (v : List W) : Bool :=
  (Nat.ble v.length 1 || (Nat.beq ph 1 && (pos t || v.any fun w => Nat.beq w.r 0))) ||
    possibleInputPair H v

lemma relevantStart_facts {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false) :
    Nat.ble v.length 1 = false ∧
      (Nat.beq ph 1 = false ∨ (t = 0 ∧ v.any (fun w => Nat.beq w.r 0) = false)) ∧
      possibleInputPair H v = false := by
  simp only [relevantStart, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
  refine ⟨h.1.1, h.1.2.imp_right ?_, h.2⟩
  rintro ⟨ht, hv⟩
  exact ⟨by cases t <;> simp [pos] at ht ⊢, hv⟩

lemma inactiveTop {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) :
    topCC nn aa hx hy l m g K H ph k t z v = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topCC, hl, noNode hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMoves hv, Bool.cond_self, tst_const_false]

def guardStart (t H ph : ℕ) (test : List W → Bool) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (test v) (relevantStart t H ph v)

lemma guardStart_eq {t H ph : ℕ} {test : List W → Bool}
    (h : ∀ v, relevantStart t H ph v = false → test v = false) :
    guardStart t H ph test = test := by
  funext v
  unfold guardStart
  cases hv : relevantStart t H ph v
  · exact (h v hv).symm
  · rfl

lemma inactiveStart {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) :
    startvC nn aa hx hy l m g B K t p H ph v = false := by
  simp only [startvC, child, st_eq, inactiveTop h, bR, Bool.cond_self]

noncomputable def searchInputs (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (guardStart t H ph (test nn aa hx hy l m g B p))))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma searchInputs_eq {E Q : List (ℕ × ℕ)} {Z K t H ph : ℕ}
    {test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool}
    (h : ∀ nn aa hx hy l m g B p v, relevantStart t H ph v = false →
      test nn aa hx hy l m g B p v = false) :
    searchInputs E Q Z K t H ph test =
      (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
        frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
          st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
          anySubC nn (pos t) l v 0 (test nn aa hx hy l m g B p)))
        (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z) := by
  simp only [searchInputs, guardStart_eq (h _ _ _ _ _ _ _ _ _)]

noncomputable def chkFast (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p =>
    startvC nn aa hx hy l m g B K t p H ph)

lemma chkFast_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkFast E Q Z K t H ph = chk E Q Z K t H ph := by
  unfold chkFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStart h nn aa hx hy l m g B K p)]
  rfl
set_option maxHeartbeats 0 in
noncomputable def notCandidate (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v : List W) (a : W) : Bool :=
  nots f m g e n z q v [a]

set_option maxHeartbeats 0 in
lemma nots_cons (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v : List W) (a : W) (r : List W) :
    nots f m g e n z q v (a :: r) =
      (notCandidate f m g e n z q v a || nots f m g e n z q v r) := by
  unfold notCandidate
  unfold nots
  dsimp only
  simp only [bR]
  have fact (d x : Bool) : (bif d then true else x) = ((bif d then true else false) || x) := by
    cases d <;> rfl
  exact fact _ _

set_option maxHeartbeats 0 in
lemma nots_true_iff (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) :
    nots f m g e n z q v r = true ↔
      ∃ a ∈ r, notCandidate f m g e n z q v a = true := by
  induction r with
  | nil => simp [nots]
  | cons a r ih =>
    rw [nots_cons, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨b,hb,ht⟩)
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp [hb], ht⟩
    · rintro ⟨b,hb,ht⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl ht
      · exact Or.inr ⟨b,hb,ht⟩

set_option maxHeartbeats 0 in
lemma nots_some_bin (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W)
    (h : nots f m g e n z q v r = true) :
    ∃ b : Fin 8, nots f m g e n z q v (r.filter fun a => a.s % 8 == b.val) = true := by
  obtain ⟨a,ha,hit⟩ := (nots_true_iff _ _ _ _ _ _ _ _ _).mp h
  refine ⟨⟨a.s % 8, Nat.mod_lt _ (by decide)⟩,
    (nots_true_iff _ _ _ _ _ _ _ _ _).mpr ⟨a, ?_, hit⟩⟩
  simp [ha]

set_option maxHeartbeats 0 in
def picked {X : Type} (F : X → Bool) (G : Fin 8 → X → Bool) : Prop :=
  ∀ x, F x = true → ∃ b, G b x = true

set_option maxHeartbeats 0 in
lemma Bool_pick (base : Bool) (F : Bool) (G : Fin 8 → Bool)
    (h : F = true → ∃ b, G b = true) :
    base || F = true → ∃ b, base || G b = true := by
  cases base
  · simpa using h
  · intro _
    exact ⟨0, rfl⟩

set_option maxHeartbeats 0 in
lemma tst_picked (nn aa hx hy : ℕ) (d : Bool) (l e : ℕ) (v : List W)
    (F : ℕ → Bool) (G : Fin 8 → ℕ → Bool) (hp : picked F G) :
    tstC nn aa hx hy d l e v F = true →
      ∃ b : Fin 8, tstC nn aa hx hy d l e v (G b) = true := by
  simp only [tstC, bR]
  cases h : Nat.beq v.length e
  · simp only [h, Bool.cond_false]
    cases hnext : Nat.beq v.length.succ e
    · simp only [hnext, Bool.cond_false]
      exact hp 0
    · simp only [hnext, Bool.cond_true]
      cases hb : bipC nn aa hx hy l (wstC nn d l v) v []
      · simp only [hb, Bool.cond_false]
        cases hs : flkC nn aa l (wstC nn d l v) v (starC hx hy)
        · simp only [hs, Bool.cond_false]
          exact hp 1
        · simp only [hs, Bool.cond_true]
          exact hp 0
      · simp [hb]
  · simp only [h, Bool.cond_true]
    cases hr : rectC nn aa hx hy d l (wstC nn d l v) v []
    · simp only [hr, Bool.cond_false]
      exact hp 0
    · simp [hr]

set_option maxHeartbeats 0 in
noncomputable def mvPicked (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) (y : Nat) (b : Fin 8) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (v.filter fun a => a.s % 8 == b.val))) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length

set_option maxHeartbeats 0 in
lemma mv_picked (nn aa hx hy : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) :
    mvC nn aa hx hy F l m g k t z v y = true →
      ∃ b : Fin 8, mvPicked nn aa hx hy F l m g k t z v y b = true := by
  simp only [mvC, mvPicked, bR]
  cases hnode : nodeC nn (F (k-1) t) (pos t) l m g (k-t-y) v.length z v pairsN
  · simp only [hnode, Bool.cond_false]
    cases t with
    | zero => simp [prd]
    | succ t =>
      simp only [prd, Nat.rec]
      exact nots_some_bin _ _ _ _ _ _ _ _ _
  · simp only [hnode, Bool.cond_true]
    intro _
    exact ⟨0,by simp⟩

set_option maxHeartbeats 0 in
noncomputable def topPicked (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) (b : Fin 8) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvPicked NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y b) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)

set_option maxHeartbeats 0 in
lemma top_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topCC nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPicked nn aa hx hy l m g K H ph k t z v b = true := by
  simp only [topCC, topPicked, bR]
  cases h : Nat.ble v.length 1
  · simp only [h, Bool.cond_false]
    apply tst_picked
    intro y
    cases hm : nodeC nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hm, Bool.cond_false]
      cases hc : Nat.beq ph 1
      · simp [hc]
      · simp only [hc, Bool.cond_true]
        exact mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _
    · simp only [hm, Bool.cond_true]
      intro _
      exact ⟨0,by simp⟩
  · simp only [h, Bool.cond_true]
    intro _
    exact ⟨0,by simp⟩

set_option maxHeartbeats 0 in
noncomputable def startPicked (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (b : Fin 8) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPicked NN AA HX HY l m g K H ph K t z r b) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

set_option maxHeartbeats 0 in
lemma start_picked (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startvC nn aa hx hy l m g B K t p H ph)
      (fun b v => startPicked nn aa hx hy l m g B K t p H ph v b) := by
  intro v
  simp only [startvC, startPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact top_picked _ _ _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 0 in
lemma anySub_picked (nn : ℕ) (d : Bool) (l : ℕ) (v : List W)
    (F : List W → Bool) (G : Fin 8 → List W → Bool) (hp : picked F G) (bits : ℕ) :
    anySubC nn d l v bits F = true → ∃ b : Fin 8, anySubC nn d l v bits (G b) = true := by
  induction v generalizing F G bits with
  | nil => exact hp []
  | cons a v ih =>
    let inc := Nat.lor bits (spC nn d l a.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l v)) l
    have hu (J : List W → Bool) : anySubC nn d l (a :: v) bits J =
        (bif anySubC nn d l v inc (fun r => J (a :: r)) then true else
          (bif skip then anySubC nn d l v bits J else false)) := by
      change Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l v bits J) skip)
        true (st inc fun c => anySubC nn d l v c (fun r => J (a :: r))) = _
      simp only [st_eq, bR]
    simp only [hu]
    have hs := ih (fun as => F (a :: as)) (fun b as => G b (a :: as))
      (fun as => hp (a :: as)) inc
    cases ht : anySubC nn d l v inc (fun as => F (a :: as))
    · simp only [ht, Bool.cond_false]
      cases hc : skip
      · simp [hc]
      · simp only [hc, Bool.cond_true]
        intro h
        obtain ⟨b,hb⟩ := ih F G hp bits h
        refine ⟨b, ?_⟩
        rw [hb]
        cases anySubC nn d l v inc (fun as => G b (a :: as)) <;> rfl
    · simp only [ht, Bool.cond_true]
      intro _
      obtain ⟨b,hb⟩ := hs ht
      exact ⟨b, by rw [hb]; rfl⟩

set_option maxHeartbeats 0 in
noncomputable def chkPicked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (b : Fin 8) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPicked nn aa hx hy l m g B K t p H ph r b)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

set_option maxHeartbeats 0 in
lemma chk_picked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Fin 8, chkPicked E Q Z K t H ph b = false) : chk E Q Z K t H ph = false := by
  suffices chk E Q Z K t H ph = true → False by
    cases he : chk E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chk, chkPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (start_picked _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h b).symm.trans hb)

section BinaryPartition

noncomputable def pairOne (d : Bool) (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool)
    (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' =>
    bif d then h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)
    else h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s')
      (Nat.lor a.a c.a) (Nat.land a.b c.b)) c) a

def cvOp (b : Fin 8) : Bool := b.val % 2 == 1

lemma pair_picked (h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a c : XW) :
    pair h a c = true → ∃ b : Fin 8, pairOne (cvOp b) h a c = true := by
  have h0 : cvOp 0 = false := rfl
  have h1 : cvOp 1 = true := rfl
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,pairOne,bR]
  intro h'
  cases hon : h w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · rw [hon, Bool.cond_false] at h'
    exact ⟨1, by simpa only [h1, Bool.cond_true] using h'⟩
  · exact ⟨0, by simpa only [h0, Bool.cond_false] using hon⟩

lemma scan_picked (f : XW → Bool) (q : Fin 8 → XW → Bool) (v : List XW)
    (hp : picked f q) :
    scan f v = true → ∃ b, scan (q b) v = true := by
  induction v with
  | nil => simp [scan]
  | cons a v ih =>
    have hu (F : XW → Bool) :
        scan F (a :: v) = (bif F a then true else scan F v) := by
      change Bool.rec (motive := fun _ => Bool) (scan F v) true (F a) = _
      rw [bR]
    simp only [hu]
    cases h : f a
    · simp only [h, Bool.cond_false]
      intro hr
      obtain ⟨b,hb⟩ := ih hr
      exact ⟨b,by rw [hb]; cases q b a <;> rfl⟩
    · intro _
      obtain ⟨b,hb⟩ := hp a h
      exact ⟨b,by rw [hb]; rfl⟩

lemma pairsC_picked (H : ℕ) (a : XW → XW → Bool) (q : Fin 8 → XW → XW → Bool)
    (hp : ∀ x, picked (a x) (fun b => q b x)) (xs : List XW) :
    pairsC H a xs = true → ∃ b, pairsC H (q b) xs = true := by
  induction xs with
  | nil => simp [pairsC]
  | cons x xs ih =>
    have hu (F : XW → XW → Bool) : pairsC H F (x :: xs) =
        (bif scan (fun e => bif hb H (x.s + e.s) then F x e else false) xs
          then true else pairsC H F xs) := by
      change Bool.rec (motive := fun _ => Bool) (pairsC H F xs) true
        (scan (fun e => Bool.rec (motive := fun _ => Bool) false (F x e) (hb H (x.s + e.s))) xs) = _
      simp only [bR]
    have hp' : picked (fun e => bif hb H (x.s + e.s) then a x e else false)
        (fun b e => bif hb H (x.s + e.s) then q b x e else false) := by
      intro e
      cases hc : hb H (x.s + e.s)
      · simp [hc]
      · simpa [hc] using hp x e
    simp only [hu]
    cases hc : scan (fun e => bif hb H (x.s + e.s) then a x e else false) xs
    · simp only [hc, Bool.cond_false]
      intro h
      obtain ⟨b,hb⟩ := ih h
      refine ⟨b, ?_⟩
      rw [hb]
      cases scan (fun e => bif PEqualNP.Outside.L_meta_51640_aux.hb H (x.s + e.s) then q b x e else false) xs <;> rfl
    · intro _
      obtain ⟨b,hb⟩ := scan_picked _ _ xs hp' hc
      exact ⟨b, by rw [hb]; rfl⟩

noncomputable def nodePicked (NN : Nat) (f : Nat → List W → Bool) (d : Bool)
    (l m g e n z : Nat) (v : List W) (H : Nat) (kind : Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool)
    (pairsC H (pairOne kind (f0 h)) (fs xs))
    (Bool.rec (motive := fun _ => Bool) (pairsC H (pairOne kind (f1 h)) (fs xs))
      (pairsC H (pairOne kind (f2 h)) (fs xs)) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v)) (mid f m g e (Nat.pred n) z v)

lemma node_picked (nn : ℕ) (f : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) (H : ℕ) :
    nodeC nn f d l m g e n z v (fun h xs => pairsC H h (fs xs)) = true →
      ∃ b : Fin 8, nodePicked nn f d l m g e n z v H (cvOp b) = true := by
  simp only [nodeC, nodePicked, bR]
  cases hn : Nat.ble n e
  · simp only [hn, Bool.cond_false]
    exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _
  · simp only [hn, Bool.cond_true]
    cases hs : Nat.ble n.succ e
    · simp only [hs, Bool.cond_false]
      exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _
    · simp only [hs, Bool.cond_true]
      exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _

noncomputable def topPairPicked (NN AA HX HY l m g K H ph k t z : ℕ)
    (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodePicked NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v H kind))) true (Nat.ble v.length 1)

lemma topPair_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topCC nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPairPicked nn aa hx hy l m g K H ph k t z v (cvOp b) = true := by
  simp only [topCC, topPairPicked, bR]
  cases ht : Nat.ble v.length 1
  · simp only [ht, Bool.cond_false]
    apply tst_picked
    intro y h
    dsimp only at h ⊢
    cases hx' : nodeC nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hx', Bool.cond_false] at h
      refine ⟨0, ?_⟩
      rw [h]
      cases nodePicked nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v H (cvOp 0) <;> rfl
    · obtain ⟨b,hb⟩ := node_picked _ _ _ _ _ _ _ _ _ _ _ hx'
      exact ⟨b, by simp only [hb, Bool.cond_true]⟩
  · simp only [ht, Bool.cond_true]
    exact fun _ => ⟨0,by simp⟩

noncomputable def startPairPicked (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPairPicked NN AA HX HY l m g K H ph K t z r kind) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

lemma startPair_picked (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startvC nn aa hx hy l m g B K t p H ph)
      (fun b v => startPairPicked nn aa hx hy l m g B K t p H ph v (cvOp b)) := by
  intro v
  simp only [startvC, startPairPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact topPair_picked _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def chkPairPicked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPairPicked nn aa hx hy l m g B K t p H ph r kind)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma noNodePicked {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d kind : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodePicked nn f d l m g e n z v H kind = false := by
  simp only [nodePicked, pairImpossible _ h, bR, Bool.cond_self]

lemma inactiveTopPicked {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) (kind : Bool) :
    topPairPicked nn aa hx hy l m g K H ph k t z v kind = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topPairPicked, hl, noNodePicked hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMoves hv, Bool.cond_self, tst_const_false]

lemma inactiveStartPicked {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) (kind : Bool) :
    startPairPicked nn aa hx hy l m g B K t p H ph v kind = false := by
  simp only [startPairPicked, child, st_eq, inactiveTopPicked h, bR, Bool.cond_self]

noncomputable def chkPairFast (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p v =>
    startPairPicked nn aa hx hy l m g B K t p H ph v kind)

lemma chkPairFast_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) :
    chkPairFast E Q Z K t H ph kind = chkPairPicked E Q Z K t H ph kind := by
  unfold chkPairFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStartPicked h nn aa hx hy l m g B K p kind)]
  rfl

lemma chkPair_picked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Bool, chkPairPicked E Q Z K t H ph b = false) : chk E Q Z K t H ph = false := by
  suffices chk E Q Z K t H ph = true → False by
    cases he : chk E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chk, chkPairPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (startPair_picked _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h (cvOp b)).symm.trans hb)

end BinaryPartition

lemma ins_distribute (o : W) (v : List W) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (h : picked f g) : ins o v f = true → ∃ b, ins o v (g b) = true := by
  induction v generalizing f g with
  | nil => exact h [o]
  | cons a r ih =>
    have step (u : List W → Bool) : ins o (a :: r) u =
        (bif Nat.ble a.s o.s then (bif Nat.beq o.s a.s then false else u (o :: a :: r))
          else ins o r (fun ws => u (a :: ws))) := by
      change Bool.rec (motive := fun _ => Bool) (ins o r (fun ws => u (a :: ws)))
        (Bool.rec (motive := fun _ => Bool) (u (o :: a :: r)) false (Nat.beq o.s a.s))
        (Nat.ble a.s o.s) = _
      rw [bR,bR]
    simp only [step]
    cases hle : Nat.ble a.s o.s
    · simp only [hle,Bool.cond_false]
      exact ih (f := fun ws => f (a :: ws)) (g := fun b ws => g b (a :: ws)) (fun ws => h (a :: ws))
    · cases he : Nat.beq o.s a.s
      · simpa only [he,hle,Bool.cond_true,Bool.cond_false] using h (o :: a :: r)
      · simp [he,hle]

lemma put_distribute (m s x y : ℕ) (v : List W) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (h : picked f g) : put m s x y v f = true → ∃ b, put m s x y v (g b) = true := by
  simp only [put,st_eq,bR]
  cases h0 : Nat.beq s 0 <;> cases h1 : Nat.beq s m <;> simp only [h0,h1,Bool.cond_true,Bool.cond_false,Bool.false_eq_true,false_implies]
  exact ins_distribute _ _ h

lemma child_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (free z : ℕ) (mk : (List W → Bool) → Bool) (mk_distribute : ∀ p q, picked p q → mk p = true → ∃ b, mk (q b) = true)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    child f free mk z = true → ∃ b, child (g b) free mk z = true := by
  simp only [child,st_eq,bR]
  cases hb : Nat.beq (z &&& free) free
  · simp [hb]
  · simpa only [hb,Bool.cond_true] using mk_distribute (f z) (fun b => g b z) (h z)

lemma kids_unfold (ch : ((List W → Bool) → Bool) → ℕ → Bool) (e n z x y a c : ℕ)
    (oa oc : Bool) (mk : (List W → Bool) → Bool) :
    kids ch e n z x y a c oa oc mk =
      ((oa && oc && ch (fun f => mk (fun r => rm a c r f)) z) ||
      ((oc && Nat.ble (n+1) e && ch (fun f => mk (fun r => rm c c r f)) (z-x)) ||
      ((oa && Nat.ble (n+1) e && ch (fun f => mk (fun r => rm a a r f)) (z-y)) ||
       (Nat.ble (n+2) e && ch mk (z-x-y))))) := by
  simp only [kids,bR]
  cases oa <;> cases oc <;> cases Nat.ble (n+1) e <;> cases Nat.ble (n+2) e <;> simp <;>
    (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> (try simp only [← Bool.not_eq_true]) <;> tauto

lemma kids_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (free e n z x y a c : ℕ) (oa oc : Bool) (mk : (List W → Bool) → Bool)
    (hm : ∀ p q, picked p q → mk p = true → ∃ b, mk (q b) = true)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    kids (child f free) e n z x y a c oa oc mk = true →
    ∃ b, kids (child (g b) free) e n z x y a c oa oc mk = true := by
  have cm (p q k : ℕ) : child f free (fun f => mk fun r => rm p q r f) k = true →
      ∃ b, child (g b) free (fun f => mk fun r => rm p q r f) k = true := by
    refine child_distribute free k _ ?_ h
    intro u v huv
    simp only [rm_eq]
    exact hm (fun r => u (r.filter _)) (fun b r => v b (r.filter _)) (fun r => huv (r.filter _))
  rw [kids_unfold]
  simp only [Bool.or_eq_true,Bool.and_eq_true]
  rintro (⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩)
  · obtain ⟨b,hb⟩ := cm a c z h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inl ⟨h1,hb⟩
  · obtain ⟨b,hb⟩ := cm c c (z-x) h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inl ⟨h1,hb⟩)
  · obtain ⟨b,hb⟩ := cm a a (z-y) h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inr (Or.inl ⟨h1,hb⟩))
  · obtain ⟨b,hb⟩ := child_distribute free (z-x-y) mk hm h h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inr (Or.inr ⟨h1,hb⟩))

lemma mid_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (m free e n z : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    mid f m free e n z v a c da dc s x y = true →
      ∃ b, mid (g b) m free e n z v a c da dc s x y = true := by
  simp only [mid,st_eq,bR]
  cases hb : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) free) free
  · simp [hb]
  · simpa only [hb,Bool.cond_true] using
      kids_distribute free e n (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) a.c c.c a.s c.s
        (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)
        (fun _ _ => put_distribute m s x y v) h

lemma pairs_distribute (f : XW → XW → Bool) (g : Fin 8 → XW → XW → Bool)
    (h : ∀ x, picked (f x) (fun b => g b x)) (v : List XW) :
    pairs f v = true → ∃ b, pairs (g b) v = true := by
  induction v with
  | nil => simp [pairs]
  | cons a r ih =>
    have he (u : XW → XW → Bool) : pairs u (a::r) = bif scan (u a) r then true else pairs u r := by
      change Bool.rec (motive := fun _ => Bool) (pairs u r) true (scan (u a) r) = _
      rw [bR]
    simp only [he]
    cases hb : scan (f a) r
    · simp only [hb,Bool.cond_false]
      intro ht
      obtain ⟨b,hb⟩ := ih ht
      exact ⟨b, by rw [hb]; cases scan (g b a) r <;> rfl⟩
    · simp only [hb,Bool.cond_true]
      intro _
      obtain ⟨b,hb⟩ := scan_picked _ _ r (h a) hb
      exact ⟨b,by rw [hb]; rfl⟩

lemma mode_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (m free e n z : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    modeF n e (mid f m free e n.pred z v) a c da dc s x y = true →
      ∃ b, modeF n e (mid (g b) m free e n.pred z v) a c da dc s x y = true := by
  have mid' := mid_distribute m free e n.pred z v a c da dc s x y h
  unfold modeF
  cases hn : Nat.ble n e
  · simp only [hn,Bool.cond_false,f0,bR]
    cases ha : Nat.beq (Nat.lor da dc) 0
    · simp [ha]
    · simpa only [ha,Bool.cond_true] using mid'
  · simp only [hn,Bool.cond_true]
    cases hs : Nat.ble n.succ e
    · simp only [hs,Bool.cond_false,f1,bR]
      cases ha : (bif Nat.beq da 0 then true else Nat.beq dc 0)
      · simp [ha]
      · simpa only [ha,Bool.cond_true] using mid'
    · simpa only [hs,Bool.cond_true,f2] using mid'

lemma pairOne_distribute (d : Bool) {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pairOne d f a c = true → ∃ b, pairOne d (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  cases d <;> simp only [pairOne,Bool.cond_false,Bool.cond_true] <;> exact h _ _ _ _ _ _ _

lemma nodeC_as_mode (NN : ℕ) (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    nodeC NN f d l m g e n z v go = go (pair (modeF n e (mid f m g e n.pred z v))) (mkXC NN d l (wstC NN d l v) v) := by
  unfold nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma pickedNode_as_mode (NN : ℕ) (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (H : ℕ) (kind : Bool) :
    nodePicked NN f d l m g e n z v H kind =
      pairsC H (pairOne kind (modeF n e (mid f m g e n.pred z v))) (fs (mkXC NN d l (wstC NN d l v) v)) := by
  unfold nodePicked modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma nodePicked_distribute {f : ℕ → List W → Bool} {branches : Fin 8 → ℕ → List W → Bool}
    (NN : ℕ) (d : Bool) (l m g e n z : ℕ) (v : List W) (H : ℕ) (kind : Bool)
    (h : ∀ j, picked (f j) (fun b => branches b j)) :
    nodePicked NN f d l m g e n z v H kind = true →
      ∃ b, nodePicked NN (branches b) d l m g e n z v H kind = true := by
  simp only [pickedNode_as_mode]
  exact pairsC_picked H _ _ (fun x y => pairOne_distribute kind
    (fun _ _ _ _ _ _ _ => mode_distribute m g e n z v _ _ _ _ _ _ _ h) x y) _

lemma look1C_step (nn aa hx hy l m g K fuel k t z : ℕ) (v : List W) :
    look1C nn aa hx hy l m g K fuel.succ k t z v =
      cvC nn (pos t) l v (bif Nat.ble v.length 1 then true else
        tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y)) := by
  change cvC nn (pos t) l v (Bool.rec (motive := fun _ => Bool)
      (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y) true
          (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) = _
  simp only [bR]

def nextPairPred (b : ℕ) (p : XW → XW → Bool) (a c : XW) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (p a c) (Nat.beq (((a.s + c.s) % MM) % 8) b)

lemma nextPairPred_picked (p : XW → XW → Bool) (a : XW) :
    picked (p a) (fun b => nextPairPred b p a) := by
  intro c h
  refine ⟨⟨((a.s + c.s) % MM) % 8, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simpa only [nextPairPred, bR, Nat.beq_refl, Bool.cond_true] using h

def nextPairS (b : ℕ) (p : XW → XW → Bool) (xs : List XW) : Bool :=
  pairsS (nextPairPred b p) xs

def nextPairN (b : ℕ) (p : XW → XW → Bool) (xs : List XW) : Bool :=
  pairsN (nextPairPred b p) xs

lemma nextPairS_picked (p : XW → XW → Bool) (xs : List XW) :
    pairsS p xs = true → ∃ b : Fin 8, nextPairS b p xs = true :=
  pairs_distribute _ _ (nextPairPred_picked p) _

lemma nextPairN_picked (p : XW → XW → Bool) (xs : List XW) :
    pairsN p xs = true → ∃ b : Fin 8, nextPairN b p xs = true := by
  simp only [nextPairN, pairsN, bR]
  cases hs : pairs p (fr xs)
  · simp only [Bool.cond_false]
    intro h
    obtain ⟨b, hb⟩ := scan_picked _ _ _
      (fun a => scan_picked _ _ _ (nextPairPred_picked p a)) h
    refine ⟨b, ?_⟩
    simp only [hb, Bool.cond_self]
  · intro _
    obtain ⟨b, hb⟩ := pairs_distribute _ _ (nextPairPred_picked p) _ hs
    exact ⟨b, by simp only [hb, Bool.cond_true]⟩

noncomputable def mvNext (NN AA HX HY bin : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (v.filter fun a => a.s % 8 == bin))) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v (nextPairN bin))) v.length
lemma prdNots_picked (t : ℕ) (f : ℕ → ℕ → ℕ → List W → Bool)
    (m g n z q : ℕ) (e : ℕ → ℕ) (v : List W) :
    prd t (fun s => nots (f s) m g (e s) n z q v v) = true →
    ∃ b : Fin 8, prd t (fun s => nots (f s) m g (e s) n z q v
      (v.filter fun a => a.s % 8 == (b : ℕ))) = true := by
  cases t with
  | zero => simp [prd]
  | succ t => exact nots_some_bin (f t) m g (e t) n z q v v

lemma mvNext_picked (nn aa hx hy l m g k t z : ℕ)
    (F : ℕ → ℕ → ℕ → List W → Bool) (v : List W) (y : ℕ) :
    mvC nn aa hx hy F l m g k t z v y = true →
    ∃ b : Fin 8, mvNext nn aa hx hy b F l m g k t z v y = true := by
  simp only [mvC, mvNext, bR]
  cases hd : nodeC nn (F (Nat.sub k 1) t) (pos t) l m g
      (Nat.sub (Nat.sub k t) y) v.length z v pairsN
  · simp only [Bool.cond_false]
    intro h
    obtain ⟨b, hb⟩ := prdNots_picked t _ m g v.length z 0 _ v h
    exact ⟨b, by simp only [hb, Bool.cond_self]⟩
  · intro _
    rw [nodeC_as_mode] at hd
    obtain ⟨b, hb⟩ := nextPairN_picked _ _ hd
    exact ⟨b, by simp only [nodeC_as_mode, hb, Bool.cond_true]⟩

noncomputable def look1Next (nn aa hx hy l m g K : ℕ) (bin : ℕ) :
    ℕ → ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, _, _ => Nat.beq bin 0
  | fuel + 1, k, t, z, v =>
    cvC nn (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool)
        (mvNext nn aa hx hy bin (lookC nn aa hx hy l m g K) l m g k t z v y) true
        (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t)
          (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (nextPairS bin))))
        (Nat.beq bin 0) (Nat.ble v.length 1))

lemma look1Next_picked (nn aa hx hy l m g K fuel k t : ℕ) :
    ∀ z, picked (look1C nn aa hx hy l m g K fuel k t z)
      (fun b => look1Next nn aa hx hy l m g K b fuel k t z) := by
  intro z v
  cases fuel with
  | zero =>
    intro _
    exact ⟨0, rfl⟩
  | succ fuel =>
    rw [look1C_step]
    simp only [look1Next, cvC, bR]
    cases hc : Nat.beq (covC nn (pos t) l v) l
    · simp [hc]
    · simp only [hc, Bool.cond_true]
      cases hv : Nat.ble v.length 1
      · simp only [Bool.cond_false]
        apply tst_picked
        intro y h
        let f := look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t
        let e := Nat.sub (Nat.sub k t) y
        cases hd : nodeC nn f (pos t) l m g e v.length z v pairsS
        · have hm : mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y = true := by
            simpa only [f, e, hd, Bool.cond_false, Bool.or_false] using h
          obtain ⟨b, hb⟩ := mvNext_picked nn aa hx hy l m g k t z _ v y hm
          exact ⟨b, by simp only [hb, Bool.cond_self]⟩
        · rw [nodeC_as_mode] at hd
          obtain ⟨b, hb⟩ := nextPairS_picked _ _ hd
          refine ⟨b, ?_⟩
          simp only [nodeC_as_mode, hb, Bool.cond_true, f, e]
      · exact fun _ => ⟨0, rfl⟩

noncomputable def topPairNext (NN AA HX HY l m g K H ph k t z : ℕ)
    (v : List W) (kind : Bool) (bin : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodePicked NN (look1Next NN AA HX HY l m g K bin K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v H kind))) true (Nat.ble v.length 1)

lemma topPairNext_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) (kind : Bool) :
    topPairPicked nn aa hx hy l m g K H ph k t z v kind = true →
      ∃ b : Fin 8, topPairNext nn aa hx hy l m g K H ph k t z v kind b = true := by
  simp only [topPairPicked, topPairNext, bR]
  cases ht : Nat.ble v.length 1
  · simp only [ht, Bool.cond_false]
    apply tst_picked
    intro y h
    dsimp only at h ⊢
    cases hx' : nodePicked nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v H kind
    · simp only [hx', Bool.cond_false] at h
      refine ⟨0, ?_⟩
      simp only [h, Bool.cond_self]
    · obtain ⟨b,hb⟩ := nodePicked_distribute nn (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v H kind
        (look1Next_picked nn aa hx hy l m g K K (Nat.sub k 1) t) hx'
      exact ⟨b, by simp only [hb, Bool.cond_true]⟩
  · simp only [ht, Bool.cond_true]
    exact fun _ => ⟨0,by simp⟩

noncomputable def startPairNext (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (kind : Bool) (bin : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPairNext NN AA HX HY l m g K H ph K t z r kind bin) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

lemma startPairNext_picked (nn aa hx hy l m g B K t p H ph : ℕ) (kind : Bool) :
    picked (fun v => startPairPicked nn aa hx hy l m g B K t p H ph v kind)
      (fun b v => startPairNext nn aa hx hy l m g B K t p H ph v kind b) := by
  intro v
  simp only [startPairPicked, startPairNext, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact topPairNext_picked _ _ _ _ _ _ _ _ _ _ _ _ _ v kind

noncomputable def chkPairNext (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) (bin : ℕ) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p v =>
    startPairNext nn aa hx hy l m g B K t p H ph v kind bin)

lemma guardStart_picked (t H ph : ℕ) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (pickedTest : picked f g) :
    picked (guardStart t H ph f) (fun b => guardStart t H ph (g b)) := by
  intro v
  unfold guardStart
  cases h : relevantStart t H ph v
  · simp
  · simpa [h] using pickedTest v

lemma chkPair_next (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool)
    (checked : ∀ b : Fin 8, chkPairNext E Q Z K t H ph kind b = false) :
    chkPairPicked E Q Z K t H ph kind = false := by
  rw [← chkPairFast_eq]
  refine Bool.eq_false_iff.mpr fun h => ?_
  simp only [chkPairFast, chkPairNext, searchInputs, frc_eq, st_eq] at h checked
  obtain ⟨b, hb⟩ := anySub_picked _ _ _ _ _ _
    (guardStart_picked t H ph (startPairNext_picked _ _ _ _ _ _ _ _ _ _ _ _ _ kind)) _ h
  exact Bool.noConfusion ((checked b).symm.trans hb)

section inst_data
def r5 : List (ℕ × ℕ) := [(31, 1), (47, 2), (55, 1), (59, 2), (61, 1), (62, 1), (79, 2), (87, 2), (91, 4), (93, 4), (94, 1), (103, 2), (107, 2), (109, 4), (110, 2), (115, 2), (117, 2), (118, 2), (121, 2), (122, 1), (124, 1), (143, 1), (155, 2), (157, 1), (158, 1), (167, 1), (171, 2), (173, 2), (174, 4), (179, 1), (182, 2), (185, 1), (186, 2), (188, 1), (203, 1), (205, 2), (206, 1), (211, 1), (213, 1), (214, 1), (217, 2), (218, 1), (220, 1), (229, 1), (230, 2), (233, 1), (234, 1), (236, 2), (242, 1), (244, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk5 : r5.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma i5 : ∀ e ∈ r5, Imp [] e.1 e.2 := okAll (T := []) chk5 (by simp)
def rs5 : List (ℕ × ℕ) := r5
lemma is5 : ∀ e ∈ rs5, Imp [] e.1 e.2 := i5
def r4 : List (ℕ × ℕ) := [(15, 4), (23, 2), (27, 5), (29, 4), (30, 3), (39, 4), (43, 3), (45, 5), (46, 5), (51, 4), (53, 2), (54, 4), (57, 4), (58, 4), (60, 3), (71, 3), (75, 5), (77, 5), (78, 4), (83, 5), (85, 5), (86, 4), (89, 5), (90, 4), (92, 4), (99, 3), (101, 5), (102, 3), (105, 5), (106, 4), (108, 5), (113, 3), (114, 4), (116, 4), (120, 2), (135, 1), (139, 4), (141, 4), (142, 4), (147, 2), (149, 1), (150, 2), (153, 4), (154, 4), (156, 3), (163, 2), (165, 2), (166, 5), (169, 4), (170, 5), (172, 5), (177, 1), (178, 4), (180, 2), (184, 2), (195, 1), (197, 2), (198, 2), (201, 4), (202, 3), (204, 4), (209, 2), (210, 3), (212, 3), (216, 2), (225, 1), (226, 2), (228, 4), (232, 2), (240, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk4 : r4.all (fun e => okE [] (pr rs5 e.1) e) = true := by decide +kernel
lemma i4 : ∀ e ∈ r4, Imp [] e.1 e.2 := okAll (T := rs5) chk4 is5
def rs4 : List (ℕ × ℕ) := r4 ++ rs5
lemma is4 : ∀ e ∈ rs4, Imp [] e.1 e.2 := apI i4 is5
def r3 : List (ℕ × ℕ) := [(7, 5), (11, 6), (13, 7), (14, 7), (19, 6), (21, 5), (22, 5), (25, 7), (26, 7), (28, 6), (35, 5), (37, 6), (38, 6), (41, 6), (42, 6), (44, 8), (49, 5), (50, 7), (52, 5), (56, 5), (67, 6), (69, 6), (70, 5), (73, 7), (74, 7), (76, 7), (81, 6), (82, 7), (84, 7), (88, 5), (97, 6), (98, 5), (100, 6), (104, 6), (112, 5), (131, 4), (133, 4), (134, 5), (137, 7), (138, 7), (140, 7), (145, 4), (146, 5), (148, 4), (152, 5), (161, 4), (162, 6), (164, 6), (168, 6), (176, 4), (193, 4), (194, 4), (196, 5), (200, 5), (208, 4), (224, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk3 : r3.all (fun e => okE [] (pr rs4 e.1) e) = true := by decide +kernel
lemma i3 : ∀ e ∈ r3, Imp [] e.1 e.2 := okAll (T := rs4) chk3 is4
def rs3 : List (ℕ × ℕ) := r3 ++ rs4
lemma is3 : ∀ e ∈ rs3, Imp [] e.1 e.2 := apI i3 is4
def r2 : List (ℕ × ℕ) := [(3, 8), (5, 8), (6, 8), (9, 10), (10, 9), (12, 10), (17, 8), (18, 9), (20, 8), (24, 8), (33, 8), (34, 9), (36, 9), (40, 9), (48, 8), (65, 9), (66, 8), (68, 9), (72, 9), (80, 8), (96, 8), (129, 7), (130, 8), (132, 8), (136, 9), (144, 7), (160, 8), (192, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk2 : r2.all (fun e => okE [] (pr rs3 e.1) e) = true := by decide +kernel
lemma i2 : ∀ e ∈ r2, Imp [] e.1 e.2 := okAll (T := rs3) chk2 is3
def rs2 : List (ℕ × ℕ) := r2 ++ rs3
lemma is2 : ∀ e ∈ rs2, Imp [] e.1 e.2 := apI i2 is3
def r1 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk1 : r1.all (fun e => okE [] (pr rs2 e.1) e) = true := by decide +kernel
lemma i1 : ∀ e ∈ r1, Imp [] e.1 e.2 := okAll (T := rs2) chk1 is2
def rs1 : List (ℕ × ℕ) := r1 ++ rs2
lemma is1 : ∀ e ∈ rs1, Imp [] e.1 e.2 := apI i1 is2
def pin4 : List (ℕ × ℕ) := [(270, 3), (278, 3), (282, 5), (284, 5), (294, 2), (298, 3), (300, 3), (306, 3), (308, 3), (312, 3), (326, 3), (330, 5), (332, 5), (338, 5), (340, 5), (344, 5), (354, 3), (356, 3), (360, 3), (368, 3), (390, 2), (394, 3), (396, 3), (402, 3), (404, 3), (408, 3), (418, 2), (420, 2), (424, 1), (432, 1), (450, 3), (452, 3), (456, 3), (464, 3), (480, 1), (525, 2), (533, 1), (537, 3), (540, 3), (549, 1), (553, 3), (556, 3), (561, 2), (564, 3), (568, 3), (581, 2), (585, 2), (588, 2), (593, 1), (596, 3), (600, 1), (609, 1), (612, 3), (616, 1), (624, 2), (645, 1), (649, 3), (652, 3), (657, 2), (660, 3), (664, 3), (673, 2), (676, 3), (680, 3), (688, 4), (705, 1), (708, 3), (712, 1), (720, 2), (736, 2), (1035, 2), (1043, 2), (1049, 2), (1050, 2), (1059, 1), (1065, 3), (1066, 3), (1073, 1), (1074, 3), (1080, 1), (1091, 1), (1097, 3), (1098, 3), (1105, 1), (1106, 3), (1112, 1), (1121, 2), (1122, 3), (1128, 3), (1136, 2), (1155, 1), (1161, 3), (1162, 3), (1169, 1), (1170, 3), (1176, 1), (1185, 2), (1186, 3), (1192, 3), (1200, 2), (1217, 2), (1218, 3), (1224, 3), (1232, 2), (1248, 4), (2055, 2), (2067, 3), (2069, 2), (2070, 1), (2083, 3), (2085, 3), (2086, 3), (2097, 2), (2098, 3), (2100, 1), (2115, 2), (2117, 3), (2118, 1), (2129, 3), (2130, 3), (2132, 3), (2145, 2), (2146, 1), (2148, 3), (2160, 1), (2179, 4), (2181, 4), (2182, 2), (2193, 4), (2194, 3), (2196, 2), (2209, 4), (2210, 3), (2212, 3), (2224, 2), (2241, 4), (2242, 2), (2244, 3), (2256, 3), (2272, 2), (4103, 1), (4107, 3), (4109, 2), (4110, 2), (4131, 1), (4133, 2), (4134, 2), (4137, 2), (4138, 2), (4140, 3), (4163, 2), (4165, 1), (4166, 1), (4169, 3), (4170, 3), (4172, 2), (4193, 1), (4194, 1), (4196, 2), (4200, 2), (4227, 2), (4229, 1), (4230, 1), (4233, 3), (4234, 3), (4236, 2), (4257, 1), (4258, 1), (4260, 2), (4264, 2), (4289, 2), (4290, 2), (4292, 1), (4296, 3), (4320, 1), (8199, 2), (8203, 3), (8205, 3), (8206, 5), (8211, 1), (8213, 1), (8214, 3), (8217, 2), (8218, 3), (8220, 3), (8259, 1), (8261, 1), (8262, 3), (8265, 2), (8266, 3), (8268, 3), (8273, 2), (8274, 3), (8276, 3), (8280, 2), (8323, 2), (8325, 2), (8326, 5), (8329, 3), (8330, 5), (8332, 5), (8337, 1), (8338, 3), (8340, 3), (8344, 3), (8385, 1), (8386, 3), (8388, 3), (8392, 3), (8400, 3), (16391, 3), (16395, 3), (16397, 5), (16398, 3), (16403, 3), (16405, 5), (16406, 3), (16409, 5), (16410, 3), (16412, 5), (16419, 3), (16421, 3), (16422, 3), (16425, 3), (16426, 2), (16428, 3), (16433, 3), (16434, 3), (16436, 3), (16440, 3), (16515, 1), (16517, 2), (16518, 1), (16521, 3), (16522, 2), (16524, 3), (16529, 2), (16530, 1), (16532, 2), (16536, 3), (16545, 1), (16546, 2), (16548, 1), (16552, 2), (16560, 1), (32775, 2), (32779, 2), (32781, 2), (32782, 3), (32787, 2), (32789, 2), (32790, 3), (32793, 2), (32794, 3), (32796, 3), (32803, 2), (32805, 2), (32806, 3), (32809, 2), (32810, 3), (32812, 3), (32817, 2), (32818, 3), (32820, 3), (32824, 3), (32835, 3), (32837, 3), (32838, 2), (32841, 3), (32842, 2), (32844, 2), (32849, 3), (32850, 2), (32852, 2), (32856, 2), (32865, 3), (32866, 2), (32868, 2), (32872, 2), (32880, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4 : pin4.all (fun e => okE [] (pr rs1 e.1) e) = true := by decide +kernel
lemma h4 : ∀ e ∈ pin4, Imp [] e.1 e.2 := okAll (T := rs1) v4 is1
def pv4 : List (ℕ × ℕ) := rs1 ++ pin4
lemma hv4 : ∀ e ∈ pv4, Imp [] e.1 e.2 := apI is1 h4
def pin3 : List (ℕ × ℕ) := [(262, 4), (266, 6), (268, 6), (274, 6), (276, 6), (280, 6), (290, 4), (292, 4), (296, 4), (304, 4), (322, 6), (324, 6), (328, 6), (336, 6), (352, 4), (386, 4), (388, 4), (392, 4), (400, 4), (416, 2), (448, 4), (517, 2), (521, 4), (524, 4), (529, 3), (532, 4), (536, 4), (545, 3), (548, 4), (552, 4), (560, 5), (577, 2), (580, 4), (584, 2), (592, 3), (608, 3), (641, 3), (644, 4), (648, 4), (656, 5), (672, 5), (704, 3), (1027, 2), (1033, 4), (1034, 4), (1041, 2), (1042, 4), (1048, 2), (1057, 3), (1058, 4), (1064, 4), (1072, 3), (1089, 3), (1090, 4), (1096, 4), (1104, 3), (1120, 5), (1153, 3), (1154, 4), (1160, 4), (1168, 3), (1184, 5), (1216, 5), (2051, 5), (2053, 5), (2054, 3), (2065, 5), (2066, 4), (2068, 3), (2081, 5), (2082, 4), (2084, 4), (2096, 3), (2113, 5), (2114, 3), (2116, 4), (2128, 4), (2144, 3), (2177, 7), (2178, 5), (2180, 5), (2192, 5), (2208, 5), (2240, 5), (4099, 3), (4101, 2), (4102, 2), (4105, 4), (4106, 4), (4108, 3), (4129, 2), (4130, 2), (4132, 3), (4136, 3), (4161, 3), (4162, 3), (4164, 2), (4168, 4), (4192, 2), (4225, 3), (4226, 3), (4228, 2), (4232, 4), (4256, 2), (4288, 3), (8195, 3), (8197, 3), (8198, 6), (8201, 4), (8202, 6), (8204, 6), (8209, 2), (8210, 4), (8212, 4), (8216, 4), (8257, 2), (8258, 4), (8260, 4), (8264, 4), (8272, 4), (8321, 3), (8322, 6), (8324, 6), (8328, 6), (8336, 4), (8384, 4), (16387, 4), (16389, 6), (16390, 4), (16393, 6), (16394, 4), (16396, 6), (16401, 6), (16402, 4), (16404, 6), (16408, 6), (16417, 4), (16418, 4), (16420, 4), (16424, 4), (16432, 4), (16513, 3), (16514, 2), (16516, 3), (16520, 4), (16528, 3), (16544, 2), (32771, 3), (32773, 3), (32774, 4), (32777, 3), (32778, 4), (32780, 4), (32785, 3), (32786, 4), (32788, 4), (32792, 4), (32801, 3), (32802, 4), (32804, 4), (32808, 4), (32816, 4), (32833, 4), (32834, 3), (32836, 3), (32840, 3), (32848, 3), (32864, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v3 : pin3.all (fun e => okE [] (pr pv4 e.1) e) = true := by decide +kernel
lemma h3 : ∀ e ∈ pin3, Imp [] e.1 e.2 := okAll (T := pv4) v3 hv4
def pv3 : List (ℕ × ℕ) := pv4 ++ pin3
lemma hv3 : ∀ e ∈ pv3, Imp [] e.1 e.2 := apI hv4 h3
def pin2 : List (ℕ × ℕ) := [(258, 7), (260, 7), (264, 7), (272, 7), (288, 5), (320, 7), (384, 5), (513, 4), (516, 5), (520, 5), (528, 6), (544, 6), (576, 4), (640, 6), (1025, 4), (1026, 5), (1032, 5), (1040, 4), (1056, 6), (1088, 6), (1152, 6), (2049, 8), (2050, 6), (2052, 6), (2064, 6), (2080, 6), (2112, 6), (2176, 8), (4097, 4), (4098, 4), (4100, 3), (4104, 5), (4128, 3), (4160, 4), (4224, 4), (8193, 4), (8194, 7), (8196, 7), (8200, 7), (8208, 5), (8256, 5), (8320, 7), (16385, 7), (16386, 5), (16388, 7), (16392, 7), (16400, 7), (16416, 5), (16512, 4), (32769, 4), (32770, 5), (32772, 5), (32776, 5), (32784, 5), (32800, 5), (32832, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2 : pin2.all (fun e => okE [] (pr pv3 e.1) e) = true := by decide +kernel
lemma h2 : ∀ e ∈ pin2, Imp [] e.1 e.2 := okAll (T := pv3) v2 hv3
def pv2 : List (ℕ × ℕ) := pv3 ++ pin2
lemma hv2 : ∀ e ∈ pv2, Imp [] e.1 e.2 := apI hv3 h2
def pin1 : List (ℕ × ℕ) := [(256, 8), (512, 7), (1024, 7), (2048, 9), (4096, 5), (8192, 8), (16384, 8), (32768, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1 : pin1.all (fun e => okE [] (pr pv2 e.1) e) = true := by decide +kernel
lemma h1 : ∀ e ∈ pin1, Imp [] e.1 e.2 := okAll (T := pv2) v1 hv2
def pv1 : List (ℕ × ℕ) := pv2 ++ pin1
lemma hv1 : ∀ e ∈ pv1, Imp [] e.1 e.2 := apI hv2 h1
def rStrong : List (ℕ × ℕ) := [(1, 12), (2, 12), (4, 12), (8, 13), (16, 11), (32, 11), (64, 11), (128, 11)]
def e8Q : List (ℕ × ℕ) := (pr pv1 8).filter (fun e => e.2 ≥ 4)


def allInputsNeeded (nn : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun w ws rest bits =>
      !Nat.beq (Nat.lor bits (covC nn d l ws)) l &&
        rest (Nat.lor bits (spC nn d l w.s))) v

lemma anySub_allInputs {nn : ℕ} {d : Bool} {l : ℕ} {v : List W} {bits : ℕ}
    (needed : allInputsNeeded nn d l v bits = true) (test : List W → Bool) :
    anySubC nn d l v bits test = test v := by
  induction v generalizing bits test with
  | nil => rfl
  | cons w ws ih =>
    let included := Nat.lor bits (spC nn d l w.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l ws)) l
    change (!skip && allInputsNeeded nn d l ws included) = true at needed
    simp only [Bool.and_eq_true] at needed
    have mustKeep : skip = false := Bool.eq_false_iff.mpr (fun h => by rw [h] at needed; simp at needed)
    change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l ws bits test) skip)
      true (st included (fun c => anySubC nn d l ws c (fun r => test (w :: r)))) = _
    rw [st_eq, ih needed.2, mustKeep]
    cases test (w :: ws) <;> rfl

def e8Words : List W := [
  ⟨0x1beff9f3ff9b00000000000000000000000000000000000000000000000000000000000004814c04e00017000000001380138000000000180000006000600000000001800180000000c006000000000000000000000000df600f9e00d80000400000010000000801d8001000000104000000003700042088203600340b62371982b8ac00000adc4edc4e00000000000000000000000000000000000000000000000000000000286300291105a84, 0x100000004000000100001000000800000400000000002100000000200002108421084210000000000000000000008421084000000000000000000040000000, 0x8000000010842000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x8000000010842100000004000000100001000000800000400000000002100000000200002108421084210000000000000000000008421084000000000000000000040000000, 3⟩,
  ⟨0x1beff800000000000f8000003ee0000000000000000000000000000000000000000000000681680080000400000000020002000200b4005100000844024400000000010001000000008004000000000000000000000000dc1c0801c00000007c000001f700000400078000000000820000000000f00210440201c0340b600000000000000000000000001805b00acab0016b29db29c0000000000000000000000000000000080c7b002b53042a0, 0x200000008000080000000000020000000000000421000010842100000000000842108421080000000008000000210842000000000000002000000, 0x400000000000108421080000000000000000000000000000000010840000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000000108421080200000008000080000000000020000010840000421000010842100000000000842108421080000000008000000210842000000000000002000000, 3⟩,
  ⟨0x1f3ff8000000000000000000000003bfbf0000000000000000006fff80781e060000000040642201211000001190919090000020008440021212121300010008c888c8880020a444223000000000000000000000004044d144400000004000000110000008104d48000000010800000000459403c0f0300440000603000008000000008c000c0000000300000000108001b29c0018004600060000010d000315c0000083132002ec74c830, 0x80000002000020000010000008000000000840000000000010840100020080210002000401080200842100000004000002000020004010800000001, 0x200000000000000000000000000000000000000421084200000000421084000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000000080000002000020000010000008421084200840000421084010840100020080210002000401080200842100000004000002000020004010800000001, 3⟩,
  ⟨0xf80000000000001f03bfbf3800000000000000000000000000000000200004203000010000000000800080300a600004000000100010004b000080c080c000000040020000000000000000000000082030600308000007c0000008000000f81845e1c0000004000000000200e0108221020303000023719800000000000000000001805b00000000000000000003580056c676c670000000000000000080951010e9701204, 0x10000008000000000000000000004000040000001000000000000000000210000008420000000842000000004210800000400000200000108420000000000100000, 0x20000000000000000004210842000000000000000000000000000002108000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000010000008000004210842000000004000040000001000000002108000000210000008420000000842000000004210800000400000200000108420000000000100000, 3⟩,
  ⟨0x3e00000000000000000000000000000006fff8f001e70000000020000020000100000140010801800010004004002c00230020000000a0008400c002420060020000000000000000000000082180061808000008000001f0000001000807040000002100000000054b87800f380218000300000000000000000a0000dc4e00018002000001600018000004000500006c670016162b800000000009290123c70d890, 0x2000001000000040000400000200000000000000200000108001004200040000401004010040008020084010002100000080000040000400080200800000020, 0x4000000000000000000000000000000000842108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4000002000001000000040000400000200842108000000200000108001004200040000401004010040008020084010002100000080000040000400080200800000020, 3⟩,
  ⟨0x1f00000000000003ef0000000000000000000000000000040000040040000000000000001000001001000000000000006a0000000000000009001000800000000000000000000004110c1810c400000200000004400000f80424180000001f7800000001081c0840109110c040002000002b8ac000000000000001800000acab0000000000000358000000000000016d62bb15c0000001d70000c4248294, 0x800000400000010000000000000000002000000080010800000400084000840000001080000000108400004200042000020000010000100001084000000008000, 0x1000000000000000000000000108420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000800000400000010000108420000000002000000080010800000400084000840000001080000000108400004200042000020000010000100001084000000008000, 3⟩,
  ⟨0x3e0000000006fff8f79c000000000000000020400100000148018001000000010004002500300020020000a400c0008002d80040020000000000000000000000104a0018a0100000100000002200000200111808000001f000000000066d07bce00004a0000800000002000000000adc4e0000000400080000016b29c000003000056c6700000016c00000000000002138000dd24c220, 0x40000020000000800000000000000000100000004010042008020080210802008000004200800100021000010840100001000000800008001000210000000400, 0x80000000000000000000000000001084210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x80000040000020000000800000001084210000100000004010042008020080210802008000004200800100021000010840100001000000800008001000210000000400, 3⟩]

def e8M : ℕ := 0x1beff9f3ff9b00000f8000003ee00001f03bfbf38000003ef000000006fff8f79de766ff86816c46e33057158000015b89db89c300b6015956002d653b653806b000ad8ced8ce002dac5762b8000000000000000000000df7fcf9ffcd800007c000001f700000f81dfdf9c000001f78000000037ffc7bcef3b37fc340b62371982b8ac00000adc4edc4e1805b00acab0016b29db29c03580056c676c670016d62bb15c0000083d7b012fd74dab4

def e8G : ℕ := 0x84210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210

def e8B : ℕ := 0xbd6b7bdeb8c6318c5ad8b5b18b5b18c6318c6318c6318c62d8b5ad7bdef7bdef7bdf18c6318bdf18c6318be2f8c5f17be317be2f8bdaf5ad6d7ad6b7a5ad6ad6b5b4e73a4a72

def e8L : ℕ := 0xdf7fcf9ffcd800007c000001f700000f81dfdf9c000001f78000000037ffc7bcef3b37fc340b62371982b8ac00000adc4edc4e1805b00acab0016b29db29c03580056c676c670016d62bb15c000000000000000000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8Words_eq : avl (PZ e8Q) (mz 8) (rawL []) = e8Words := Eq.refl e8Words

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8M_eq : mz 8 = e8M := Eq.refl e8M

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8G_eq : pL (e8Q.map fun _ => 16) = e8G := Eq.refl e8G

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8B_eq : pL (e8Q.map fun e => 16 + (12 - e.2)) = e8B := Eq.refl e8B

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8L_eq : lz 8 = e8L := Eq.refl e8L

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allE8Inputs (d : Bool) :
    allInputsNeeded I.NN d e8L e8Words 0 = true := by
  cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma searchInputs_e8 (t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    searchInputs [] e8Q 8 12 t H ph test =
      guardStart t H ph (test I.NN I.AA I.HX I.HY e8L e8M e8G e8B 0) e8Words := by
  simp only [searchInputs, frc_eq, st_eq, e8Words_eq, e8M_eq, e8G_eq, e8B_eq, e8L_eq]
  change anySubC I.NN (pos t) e8L e8Words 0 _ = _
  rw [anySub_allInputs (allE8Inputs (pos t))]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8Ok : pOk 8 e8Q = true := by decide +kernel

def e8Cases : List (ℕ × ℕ) := [(0x400, 0), (0x1000000000000, 0), (0x400000000000000000, 0), (0x1000000000000000000000, 0), (0x10000000000000000000000, 0), (0x40000000000000000000000000, 0), (0x100000000000000000000000000000, 0), (0x1000000000000000000000000000000, 0), (0x4000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000, 0), (0x10000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000, 0), (0x10000000000000000000000000000000000000000, 0), (0x10000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000, 0), (0x1000000000000000000000000000000000000000000000000, 0), (0x1000000000000000000000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000000, 0), (0x3baffebbffeffefeefefbffeefffbffeefffbffffefffffffffbff, 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8Full : mFull e8Cases = true := by decide +kernel

namespace CofactorEight

abbrev rootPreparedMask : ℕ := e8M
abbrev rootPreparedSlots : ℕ := e8G
abbrev rootPreparedBudget : ℕ := e8B
abbrev rootPreparedWords : List W := e8Words



lemma pair_distribute {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pair f a c = true → ∃ b, pair (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,bR]
  cases hb : f w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · simp only [hb,Bool.cond_false]
    intro hor
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hor
    refine ⟨b, ?_⟩
    rw [hb]
    simp
  · intro _
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hb
    exact ⟨b,by rw [hb]; rfl⟩



noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f false e8L rootPreparedMask rootPreparedSlots 12 7
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootStart_eq (H : ℕ) (kind : Bool) :
    startPairPicked I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots rootPreparedBudget
      12 0 0 H 0 rootPreparedWords kind =
    initialBinary H kind (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0) := by
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 7 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  simp only [startPairPicked, child, st_eq, topPairPicked, bR, haveRequired, len, budget,
    show Nat.ble 7 (Nat.sub 13 0) = true from rfl, show Nat.ble 7 1 = false from rfl,
    Bool.cond_true, Bool.cond_false]
  change (bif initialBinary H kind (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots
      12 12 11 0) then true else false) = _
  cases initialBinary H kind (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots
      12 12 11 0) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialBinary_of_check (H : ℕ) (kind : Bool)
    (h : chkPairPicked [] e8Q 8 12 0 H 0 kind = true) :
    initialBinary H kind
      (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0) = true := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8] at h
  simp only [guardStart, rootStart_eq, bR] at h
  cases hp : relevantStart 0 H 0 rootPreparedWords
  · simp [hp] at h
  · simpa [hp] using h

def wordEquals (a b : W) : Bool :=
  (a.s == b.s) && (a.a == b.a) && (a.b == b.b) && (a.c == b.c) && (a.r == b.r)

lemma wordEquals_spec {a b : W} (h : wordEquals a b = true) : a = b := by
  cases a
  cases b
  simp [wordEquals, Bool.and_eq_true] at h ⊢
  rcases h with ⟨⟨⟨⟨hs, ha⟩, hb⟩, hc⟩, hr⟩
  exact ⟨hs, ha, hb, hc, hr⟩

def frontierMissing (states : List (ℕ × List W)) (z : ℕ) (v : List W) : Bool :=
  !(states.any fun state => (z == state.1) && List.isEqv v state.2 wordEquals)

noncomputable def rootWithGate (i j mask : ℕ) (kind : Bool) : List W :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD i zero
  let b := rootPreparedWords.getD j zero
  let keep := (rootPreparedWords.zipIdx.filter fun e => mask.testBit e.2).map Prod.fst
  addS (opW kind a b) keep

lemma frontierMissing_false {states : List (ℕ × List W)} {z : ℕ} {v : List W}
    (h : frontierMissing states z v = false) : (z, v) ∈ states := by
  simp only [frontierMissing, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨j, w⟩, membership, rfl, he⟩ := h
  have hw : v = w := by
    clear membership
    induction v generalizing w with
    | nil => cases w <;> simp_all [List.isEqv]
    | cons a v ih =>
      cases w with
      | nil => simp [List.isEqv] at he
      | cons b w =>
        simp only [List.isEqv, Bool.and_eq_true] at he
        rw [wordEquals_spec he.1, ih w he.2]
  rwa [hw]

lemma initialBinary_from_frontier (H : ℕ) (kind : Bool) (states : List (ℕ × List W))
    (complete : initialBinary H kind (frontierMissing states) = false)
    (checked : ∀ state ∈ states,
      look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0 state.1 state.2 = false) :
    chkPairPicked [] e8Q 8 12 0 H 0 kind = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  have original := initialBinary_of_check H kind h
  unfold initialBinary at original complete
  obtain ⟨_, hit⟩ := nodePicked_distribute
    (branches := fun _ => frontierMissing states)
    I.NN false e8L rootPreparedMask rootPreparedSlots 12 7
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind
    (fun z v hit => by
      refine ⟨0, ?_⟩
      cases hm : frontierMissing states z v
      · exact Bool.noConfusion ((checked (z,v) (frontierMissing_false hm)).symm.trans hit)
      · exact hm)
    original
  exact Bool.noConfusion (complete.symm.trans hit)

abbrev SearchState := ℕ × List W

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f false e8L rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 11 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12)
      e8L rootPreparedMask rootPreparedSlots 11 0 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 11 10 0 z v))

lemma pureAt_of_covered (e : ℕ) (state : SearchState) (remaining : SearchState → Bool)
    (miss : ℕ → List W → Bool)
    (complete : pureAt e state miss = false)
    (covered : ∀ z v, miss z v = false → remaining (z,v) = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => miss)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : miss z v
        · exact Bool.noConfusion ((covered z v missed).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma pureAt_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : pureAt e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    pureAt e state (fun z v => remaining (z,v)) = false :=
  pureAt_of_covered e state remaining (frontierMissing states) complete
    (fun z v h => checked (z,v) (frontierMissing_false h))

lemma pureSecond_from_frontier (state : SearchState) (states : List SearchState)
    (complete : pureSecond state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, afterSecond x = false) :
    pureSecond state (fun z v => afterSecond (z,v)) = false :=
  pureAt_from_frontier 11 state states afterSecond complete checked

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 11)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false e8L 12 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 12 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 12 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (12 : ℕ) = Nat.succ 11 from rfl, look1C_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 0) e8L state.2 (tstC I.NN I.AA I.HX I.HY false e8L 12 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 0) e8L state.2 (bif pureSecond state
      (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 11 10 0)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def secondTransition (state : SearchState) (i j kept : ℕ) (kind : Bool) : SearchState :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := state.2.getD i zero
  let b := state.2.getD j zero
  let word := opW kind a b
  let keptWords := (state.2.zipIdx.filter fun e => kept.testBit e.2).map Prod.fst
  let budget := Nat.sub (Nat.add state.1 (Nat.land a.c b.c)) word.c
  let usedA := if kept.testBit i then a.c else 0
  let usedB := if kept.testBit j then b.c else 0
  (Nat.sub (Nat.sub budget usedA) usedB, addS word keptWords)

noncomputable def firstStates : List SearchState := [
  ⟨0xace96b5a95ad6b4ace759ca96a52d4a5ad4a5ad6a5ad6b5256a52939ce52a4a52a525294a7394a739ce7394e539ca72956b4a56959ca718c6538c635952949ce73a42129c651, rootWithGate 0 1 127 false⟩,
  ⟨0xa4a96b5a94a5294a4a5494eb6a52d5adad5adad6adad6b5676a529294a73a4e73a52739ce739ce94a52949d274a4e939d6b4a56959ce9294a7494a55952949ce73a46329c651, rootWithGate 0 1 127 true⟩,
  ⟨0xa5296b5a54a5295b52969ced6a52b5b5ab5b5ad5adad6ad25494a549ce73a4a5294a739ce939ce749d273a5675aceb39d6949d274a4e92946959ce55952749ca729c6529c650, rootWithGate 0 2 127 true⟩,
  ⟨0xad276b5a94ad6b4a5296a4ab59ceb4b5ad4b52d6a52d6b5294a5294a52529d294a5252a527394a739ce7394e55ad2b4a4e72956959ca718c6559ce7384a549ce73a42509c651, rootWithGate 0 3 127 false⟩,
  ⟨0xa5256b5a94a5295ad296a4a9494a95b5ad5b56d6ad6d6b5695a5294a525295294a5253a529494a74a52949d275ad2b4a52939d695a4a9294a759ce748ce749ce73a46519c651, rootWithGate 0 3 127 true⟩,
  ⟨0xad296b5695ad694b5294a4ad6a4ad4b52d4b5a96a56b5ad296a5254a525295292a4a54a4a7394a739ce73a4e959d27494eb2a56539ca718c6959c67594a948ce33942529c611, rootWithGate 0 4 127 false⟩,
  ⟨0xa5296b5294a5295b5295a4ed6a4ed5b56d5b5ab6a5294a5696a5274a52729d293a4e54a4e949ca93a4e93a5295a52949d2b3a5674a4e928ca959ca7594e9494e539c6529c631, rootWithGate 0 4 127 true⟩,
  ⟨0xad295b5a95a56b4b4a96a4ad4a52d4ad6b4b5ad6a5a96b52969529295252a4a9494a5494a7394a739ce73a56939cab4a4e74a4e559ca718c6939ce73952928c673a42528c651, rootWithGate 0 5 127 false⟩,
  ⟨0xa5294b5a94a5295b4e96a4ed5a52d4a5295b5ad6adab6b56969d2939d273a4e949ce749ce949ce939d294a5694a4eb4a5294a5275a4e7294a949ce749529394a73a465294651, rootWithGate 0 5 127 true⟩,
  ⟨0xa5296a5a94a5295b5276a4ed69d2d5b5ad4a5294adad5b5696a4e93a4e539d2749d2539d27494e94a4e749d694ad293a56b39d294a4e9194a9594e758d2939ce52a46529c251, rootWithGate 0 6 127 true⟩,
  ⟨0xb4a96b5a56b5ad4a4a54952b6a52b6adab6adad5b5ad6ad25494a5294a94a4a5294a9294a93a5295a56949d254a4a92956949d274a52b39ca7494a35952749ca729ca329c650, rootWithGate 1 2 127 true⟩,
  ⟨0xb4e76b5a94b5ad5a4e759ce959ceb6a5ad6a52d6b52d6b5a54a52939ce739ca52a525294a7394a75ad6b594e539ca7294e72956959cab39ce538c63384a549ce73a4a109c651, rootWithGate 1 3 127 false⟩,
  ⟨0xb4a56b5a95b5ad4a4a5494a9494a96adad6ad6d6b56d6b5a75a529294a5294e73a52729ce949ce95ad6b594e54a4e939d2939d695a4eb39ce5494a548ce749ce73a4a319c651, rootWithGate 1 3 127 true⟩,
  ⟨0xb4e96b5696b5a95ace749d296a4ad6a52d6a5a96ad6b5ada56a52539ce9294a52a4a5294a73a4ab3aceb394e539ca7294eb2a56539d2b38ce538c63594a948ce3394a129c611, rootWithGate 1 4 127 false⟩,
  ⟨0xb4a96b5296b5ab4a4a54952b6a4ed6ad6d6adab6a5294a5a76a527294a939ce72a4e739ca94a4eb4ad2b49ce749ce73952b3a5674a52b394e749465594e9494e539ca329c631, rootWithGate 1 4 127 true⟩,
  ⟨0xb4e95b5a96a5ad5aca759d294a52d5a56b6a5ad6b5a96b5a569529294e94a4a5294a9294a73a52b39d6b594e539ca7294e74a4e559d2739ce538c633952928c673a4a128c651, rootWithGate 1 5 127 false⟩,
  ⟨0xb4a94b5a96adad4a4a54952b5a52d4a5296adad6b5ab6b5a769d29294a94a4a739ce9394a94a52b4a56b59d2739ca939d294a5275a52939ce7394a549529394a73a4a3294651, rootWithGate 1 5 127 true⟩,
  ⟨0xb4a96a5a96b56d4a4a54952b69d2d6adad4a5294b5ad5b5a76a4e9294a749ce539d27294e749d2b5ad29595273a4e729d6b39d294a52b29ce748ca558d2939ce52a4a329c251, rootWithGate 1 6 127 true⟩,
  ⟨0xb5256b5a55b5ad6ad2969ca9494a96b5ab6b56d5b56d6ad25494a549ce5294a5294a729ceb49ce75a56949d255aceb39d27395274aceb39ca759ce548ce549ca729ca519c650, rootWithGate 2 3 127 true⟩,
  ⟨0xb5296b5256b5ab6b52959d2d6a4eb6b56b6b5ab5a5294a525494a549ce939ca5294a739cab4a4e94a5293a5275a4e93952939d253ad2b394a959ca5594e7494a5294a529c630, rootWithGate 2 4 127 true⟩,
  ⟨0xb5294b5a56adad6b4e969d2d5a52b4a5296b5ad5b5ab6ad25494a5394e94a4a5294a9394ab4a52949d694a5674a4ab39d2749ce54ad2939ca949ce5495273946729ca5294650, rootWithGate 2 5 127 true⟩,
  ⟨0xb5296a5a56b56d6b52769d2d69d2b6b5ab4a5294b5ad5ad25494a539ca749ca5294a7294e949d295a52749d674ace929d69394e73ad2b29ca9594e558d2739ca519ca529c250, rootWithGate 2 6 127 true⟩,
  ⟨0xb5276b5694b5a96a5294a4eb59cab6b52d6b5296ad2b5ada94a5254a527295292a4a52a4ab594a73aceb394e559d27494e7295653acab38ce559c67384a548ce3394a509c611, rootWithGate 3 4 127 false⟩,
  ⟨0xb5256b5295b5ab6ad295a4a9494a96b56d6b56b6a5294a5a95a5274a525295293a4e53a4eb59ca94ad2b49ce75a52949ce929d674aceb394e759ca748ca7494e539ca519c631, rootWithGate 3 4 127 true⟩,
  ⟨0xb5275b5a94a5ad6a4a96a4eb49ceb5ad6b6b52d6b5296b5a9495292952739ca9494a5294ab594a739d6b594e539cab4a4e7294e55aca739ce539ce7384a528c673a4a508c651, rootWithGate 3 5 127 false⟩,
  ⟨0xb5254b5a95adad6ace96a4a9494a94a5296b56d6b56b6b5a959d2939d25294e949ce739ceb59ce94a56b59d274a4eb4a4e739d275ace939ce749ce738ce7394a73a4a5194651, rootWithGate 3 5 127 true⟩,
  ⟨0xb5256a5a95b56d6ad276a4a9494a96b5ad4a5294b56d5b5a95a4e93a4e52952749d2529d29594e95ad29595274ad293a529295294aceb29ce7594e7484e739ce52a4a519c251, rootWithGate 3 6 127 true⟩,
  ⟨0xb5295b5696a5a96b4a94a52d4a4ad5ad2b6b5a96ad695ada96952529529294a9294a5494ab5a4ab39ceb3a4e939ca7494e72a4e53ad2738ce939c67394a928c63394a528c611, rootWithGate 4 5 127 false⟩,
  ⟨0xb5294b5296adab6b4e95a52d5a4ed4a5296b5ab6a5294a5a969d2739d2939ce939ca749cab5a4eb3a52b4a52949ce949ce93a5254ad29394e949ca7494e938ca539ca5294631, rootWithGate 4 5 127 true⟩,
  ⟨0xb5296a5296b56b6b5275a52d69ced6b56d4a5294a5294a5a96a4e73a4e73952739ce539ce959ceb4ace949d294a52739d2b29d273ad2b294e9594a758ce9394e329ca529c231, rootWithGate 4 6 127 true⟩,
  ⟨0xb5294a5a96ad6d6b4e76a52d59d2d4a5294a5294b5ab5b5a969ce929ce749ce7494e7394e959d2b4a52959d693a4e93a52939ce74ad2929ce9494e748d29294a52a4a5294251, rootWithGate 5 6 127 true⟩]

def firstCount : ℕ := 31

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def decodeStep (width : ℕ) (parent : ℕ → SearchState) (entry : ℕ) : SearchState :=
  let before := parent (entry % 2 ^ width)
  let left := (entry >>> width) % 16
  let right := (entry >>> (width + 4)) % 16
  let dropLeft := if entry.testBit (width + 8) then 2 ^ left else 0
  let dropRight := if entry.testBit (width + 9) then 2 ^ right else 0
  let kept := 2 ^ before.2.length - 1 - dropLeft - dropRight
  secondTransition before left right kept (entry.testBit (width + 10))


def secondCount : ℕ := 338

def secondCodes : List ℕ := [0x88634210e391159128eaa464123b331c828a88c4324329315008843c2114288718cccea4c410e3222194a8c8046518320314d08647c63123b2910ce0a4247637321118d1, 0xca84644e191218868a435743232a11d488eabc7330311314898e624522aba0958818ea1442222a1954448eacc420ab88918818c864410a30891d828ec44541239811d97, 0xac474411e191b14858cacd764239839506ae69c6238320d1841aa6c57106188315018a218642a32a954c28643c6404321d148b88684711a190d14458c60c53222a2758d3, 0xaea9d7666319214898a67c621432aa1910ceaac633a219115120ca10652232ab1912ac4547402310d14c58423865673b2b194b8a41e7346311319428c454652232af544f, 0x8e46475002a031447ac8bc510a3b091d138e214733a389115098644472122a1558ca8c834623e32135cd2aec447600311110cf8a41452222a1d190a8c630620a321d50c2, 0xccacc7206298f18828c44454422999195a8c88453123b2759538a68d646e98831d4cae6556104320419088e80c634229811d448e6364332b9181086884247632308d1506, 0xaea344302319115140a4105223299c150a8ca2475063b3950818c8a46546319b18878840e764732911940aea75720639a00c470cad441063b0318c5cead46236218f1d53, 0x841042223a0d10cc8c21464562a110c450ca64540a3a1510c4ac614764a321114c18eae44346328b1c8d8c814645c3289195baa8dc611432a39d9d8c67c653231171d0e, 0xc804511221131d8688455651aa91959048841c721a321f1d4e8ca0c711219095cc20a884762a29191c8a0c424653f980714848ec75653a39911c8e8ea94545632a75846, 0x8c23c320432a41502aa40c62123b215d578e8a4540e39211ccd8a40c531a32a59d098a6485452a80f18c78ea34423e299d10c1aa694421a3a941941ac86554123a2198d0, 0x23293194a8c83d610b3b131d028e84463023aa10c478ca74510432271c418c464651c2a110c85]

noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := secondCodes.getD (i / 32) 0
  decodeStep 6 firstAt ((block >>> (17 * (i % 32))) % 131072)

def secondBuckets : List ℕ := [0x8034200c00000000000000000000000000000000000000000200b000000000100240000080202007080184004000002003080082001000000000000000000000002000000000000, 0x806c00000806820190000000000806000000805c0000000002016000002015000000000000000000000002014000002013100442010100380000000000000, 0x202c00000000000000000000000202b080a80000080a40000000000000080a0202708098402418084202000000000000000201f00000201e00000000008074000000000201c, 0x80e40000000002038080dc2036000000000000000000000002035000004033100c4203000000202f000000000000000000000000000000000000080b8202d000000000000000000, 0x203e080f4000000000000000000000000000000000000203c00000203b00000203a000000000000000000000000000000000000, 0x4048000002047000000000000000000000000000000002046081144043081082041000000000000000000100fc0000000000000000000000, 0x8144000008140204f08138204d00000204c0000000000000000000000000000000000000000000000812c0000000000000081280000000000000000000000000000000000000000, 0x816000000000000000815c0000000002056000000000000002055000000000000000000000000000081502053000000000000000000000000000081480000000000000000000000, 0x40641018820610818000000817c000000000000000000000000000000008178205d00000000000000000000000000008170205b000000000081682059000000000, 0x81c40000081c0000000000406e00000000000000000000000206d081b0206b00000000000000000000000206a081a40000000004067000000000000000000000000000081980000, 0x2077000000000000000000000000000081d82075081d00000000000000000000000000000000000000000000000000000000000000002073081c80000, 0x102000000081fc0000081f80000000000000081f4000000000207c00000207b00000000000000000000000207a000000000000000000000000000081e40000000002078000000000, 0x822c000000000208a0000000000000000000000020891021c20861021000000000000000820c0000000000000000000000000002082000000000000000000000000000000000000, 0x20980000000000825c409518248209100000000000000000008240000000000000000000208f08238000000000000000000000000000000008234208c000000000, 0x20a50829000000000000000828c20a20000000000000000000000000000000020a108280209f00000000008278209d00000209c0826c000000000000000000209a082640000, 0x82b440ab082a800000000020a90000000000000000000000000000000000000000020a80000000000000000000000000000000000000000000000829c00000000000000000020a6, 0x82d820b50000020b40000000000000000000000000000000020b3082c800000000000000000000000000000000000000000000020b1182b80000000000000000000000000000000, 0x82f020bb082e800000000000000000000000000020b90000000000000000000000000000000000000000020b8000000000082dc0000000000000000000000000000000000000000, 0x831000000000020c30830820c1000000000000000000000000000083000000000000000082fc0000082f800000000000000000000000000020bd, 0x834020cf0000000000000000000000000000000020ce0000000000833400000000020cc0000000000000040ca0000000000000040c81031820c5, 0x837420dc0836c20da0836420d80000000000000000001035820d50000000000000000000000020d40000000000000040d2000000000083440000, 0x20f0083bc0000103b420ec000000000083ac0000103a420e80000020e70839800000000000000000000000000020e50839000000838c40e10838000000000020df083780000, 0x83f00000083ec20fa083e40000000000000000000000083e000000000000000000000000000020f7083d800000000020f50000040f3103c40000000000000000000000, 0x21050841000000000000000000000000000000000000021030000000000000000000000021020000021010000021000000020ff083f80000000000000000000000083f40000, 0x8434000000000000000000000000000000000000000000000000000000000008430000000000000000000000000000210b1042421080841c0000084180000000000000000000000, 0x211900000211800000211708458211500000211400000000000000000000000000000000211300000211210440410e000000000000000000000000000000000000000000000, 0x21270000000000849800000849400000000000000000021240848c00000000021221048000000847c000000000000000000000000000000000000211e10470211b084680000, 0x212d000000000000000000000000000000000000084b0000000000212b000000000000000000000000000000000000000000000084a80000104a00000000000000000000000, 0x84c42130000000000000000000000000000000000000084bc0000000000000084b80000000000000000000000, 0x213f000000000084f80000084f4213c084ec000000000000000000213a084e40000000000000000000000084e04136000000000184cc0000000000000000000000084c80000, 0x851c21460000000000000000000851400000000000000851000000850c2142000002141000000000000000000000002140, 0x854421500853c000008538214d00000000000000000000000000000000214c0852c000000000214a000000000000000000000000000000004148]

def thirdCount : ℕ := 1064

def thirdCodes : List ℕ := [0x8c900ae8fbb0e08b04fbd0e3dcea86ccb32ccb18d0c33cea31ce6a58ec368ca3a90a93885098e9088eafb8a8f3cc889acb3a8e890ec8878e726ce8528c8548caf08a81daed4e8ea5fd0e388c700ae8f0, 0xaec838cb058c865aea06aea048e9128a8348e916d0a658c90b90c750a8aeeea79b0cb6aec81ae49aac851d0e468eb058a90088630ccb23ae8d9d0c36cea93cea3acea35d0c348ea6f8cafb8ec3d90c6d, 0x8e9260c42ceeaf98e8b18c6258eb118c9108eb16b0e250c429b0cba8a4298e700b08f00e6260e6258ec4a8a90b8c626b0cb990e8790e8508500aec87aec1caec86aec858e91eccb468e91d90e83d0c3d, 0x8642990c83aea17ac62a90e8f8ec54aec98f08b3ae90b8ec50aec8f90908b0b0888625b08fb9069ab0e2e8cb118a910aec9690e918a42c8e8aef0f35aec308ca52ae9118ea80cec528ec51aca068ca4f, 0x8cb20aeca4b0b11ae744b0e3eac82ceec3e8e746b0e39f0c9690e9ace6caf0c9490ea1ac8298ec59aeca1aeca0ac62ed0e59aea26aea258642c8ec9bceaaa906a1cec5790c8690c84cc8aeac717aec9a, 0xd0c598ec65b0cdc0e646eca3fc86a5cea57ae7468a8548ec668eca6ae919aea33f0f49aca25ac87590abb8865290c9390c91d0e65f0c98aa829aeca7aea2a8ea90aea2ed0a7daca2690abccea52ce8bb, 0xb0cf08865fae4aeb0e4aca82c886468e9448c892ccb4ed0c65aecb3ae92fae4b1f0ca78e93aced4bee8bcaa451b0e47ceabbb0911ae4c68ecb18ca67aea368eb2faca33aec44b0e4290926aa82ceec42, 0xcec0d8cb3aa84ae90ebad0e7cf0e0d8a86db0cf9cec7f8eab190eb98eaaeaa211aecb98cb358ead98a865b0e54a84b18c93b8e9468eb3ab0cf6ae932aea418c8958c40ed0a97d0a9590eb6aa851aecb6, 0xcca1cacac78c42caca6090af0cca4590cb7906c6ac41e8cb43cec1dac654ac897f0e1d8e625b0d018a6a5aa452b0e5baeb00ca83c8cb3e90addcca3b8c4298ec7dac6518a93bac40eb0928d0e7d8e626, 0xeca6aac74eeeac7aca58aa8a690afbf0e2b8e8f3d0e97d0e968ec8dd0c7dcec2590cbcb0e6290cbb8c94e90cbad0e8dcec8caec5fb0546b0d08aea50b06c68e6038a6aeceadd9093ab0b3af08ee90ec6, 0x8a8868ca0690edc8e900cc908ceafb8ecd98ec95d0e9eaec72aa6b1eca7290ed78ca00d0c8d8ec98f0e388ec97b0e6dcec2e8ea068ec9290946ac435ae634d0e958a94ed0e94d0e92b09328c60eaec6f, 0xceb05d0ea88c62cf090c8ead4d0c98cc90090cd38ca10d0c95aeb228caa6d0ea7f0b1d8ea188caa58e825cec3ececa5ae63df0b12b0e75d0916aece0d0c978c6298e646c86d4aeb198eccdcea8cae63b, 0xae74e906fbcecaf8ca1dd0eb3f0ce08e834aea75ac61eca7198ecabcec4290ef690cdd90cdc90ef1aec7bb0d298a6cab0e81acae9d0eb08ca18eec818c8c690ef0aeb27ae645b0a06aecf08ea1db0d26, 0x90cf18a6fbcca6dae6518eb208ecb690cf08c835ac4268ea348ed00cec4aaec89acb00b0e8690cebb0e84eec86b04258e500aecfdae82ad0ca78ca28ccab290ef98c830ae8268cab18caaeb0a10b0426, 0x886aeaec9b8ed0b90cfbb0e93f0cfd90f08b0a2aaed0890b29885000e6958a835b0d328c697ceaaf90825b0a26b0e8f90708b0a25cec54ae654eec8f8a8308e846ae51eac880d0cab8eaf38a6d4ac452, 0xaea918c652ceccbcecca8ecc6b082690f118c64fb081fd0cb88ea4288695b0ea18ca3deeca18c840ac88cae83d8c72deea258eb00f0d02d0ec09082e8ea45aeb3bb0a2e8e62caea858c695ae82c8ea3d, 0x8c84cd0cc9cca83d0ed68a700c8719aca92b082a8ca47aed1e8ed1ad0ed2acb198ed18886a1ca72d8ca458eb0ba86b1acb178ca43f0e658ca42aed16b0d47ae8458cacab0d46ae842eea2eaea928a840, 0xb0c08aa4b1aa4aeb0eb7b0c04cece6886ca8ca51ac8a58a70b865098c908ae85190f288ea548a84c8e93bb072690d138c852acb27cecdf90f2690d11aed26aecae8ea518cad4ca73b907268ed22ce93a, 0xb08428c9168ecf58ea6590d288e94ecec81b0ebbb0eba8c85f8ca59ccaa1ac451b0845ae5468ecee8a857aed2fb0ebcb04548ed20cca9a8ea598ca54d0eeeac8fb8c8578ece0b0451cec758a852b0c0a, 0x8e695d0f02cec86cec848c86faeab9f0d2fcc94ef0e8dd081dacab68ca668ea6d8e6978ca659073a8c6c6b0c1fae687ae686d0efa8a85f8c91dccaa790f32ceae3aed3290854d0ce08a719aeab68ea66, 0xcca9bcec95cec93887098ed08ec804f0e95d0cfa886c6b08518e6a390746b0ed3ae693ac6c68a86facb3bcec8d8e8128e69aac66f8e6a190f3ad0cf58ca6dca60eee829d0f03aea2c90a08aeabad0f05, 0xd0f14cc630cea1d887008ea87ac9288ed11ae426b0c3ed0f12d0f16d0b2facac68ea7db0eddaea3c8e54eb0c3bb0746ee808b0edad0d05d0d028eb3b9086dced1090f4690d3aaed46aeac6f08180a830, 0x8c890cc83bac4b1ae66fac4aeceb10aeadcd0f258e8958ed1d8e83090e068854e90e048cb19d0f1d8ea86b0c45aec04b0c428cb18b0c41b0eebb0ef18ea838ed16aea408ca7d8e892ecb1eac8d4cc834, 0x8ec01aea4caeaee8ed28d0b44ec8788ea938a8908ed21aca15d0f2bb0ef98e83c8c944ccaae8e8a38eb4e8a73b8c6fb8ea968cb23aca0e8ca868ea91eea758c93a0ed118cb22b0efb8e8a18ca83aa8fb, 0x8e42c90c10d0f2f083098e6c68630990e2690e2590a4590a43ae89a90e1fd0d21eea15aec1faeaf69088690626906258e8408ca938a500ae897b0875ae8938a916aed0090c06b0c50d0d1dcecb7ecb00, 0x8c8af8c8ae8eab3ca82eb062eb0c618ed37aea5f0e712843098c711ae6c68c8b1aec34f0ec9b062acc64faeb02cea4290e2aced38b04a18ed30cecbb8ec2c8eaa7aca2c8e84490a428ed2faeaf986500, 0x8ea30f0c34aa90b8ed4488712cecd3ae451aec3e90c2eb0893906458cb3bd0f448a8afb0c6d8a8aeaed18aa74e0e71e90a5190a5490e3baec3b90c2aac90b8e84c8a8b1aeb08d0d2f908a18ed3aac6b1, 0x8eaba8e85fcc65f0ed3a8e85cd0d448a629b0c768871eb089a90e458e8c6aec46aec4590e41d0f49ac71daec42ea82aaec41cea54ca900ae8b6acb08aeb11ca65faed23aca40d0d378c81d8cab3aea72, 0xd0d4c8ea40ca6608cabe90a6dce86d8c834b0ab68a630ae8a6ec8ac8a62c8cabc8873b8cabbac8168ed4b8a93a8a6458c82ed0f51acb2dae8b98c825ce865acb118ed4cac919cecdd8e6ae8c6608eabb, 0x8cac9b0c838ec0dcecfb90e508c500d0e0dcec15ac826f0efab0ab9ccb1690c47ee863ae6b1d0d4baeb2890e51b0c818c8ca90c45ce8358ec0690c4390c42ac927d0a348e86fcecebcecf1f0c46aca4c, 0xccb00883098e708cecfe8ea4cb0c91d0e1bec66fb0f3a8ec1890a768ec588ec16d0e18ac4c6d0e17d0a3dcecfaaca57d0e16cecf990c4ab04c6aea88b0c87b0651b0c86b0654b0c858a8cad0d51ac82a, 0xeea578ca29cc886d0892d0e2bccb29b0c9a8ec26ac8d98e7118ec25a845290c54ac50bae708aa651aca5f8ca1eb08b9908c68ec1db0ac68eadc8ec17ced05cec2990c518cad9d0e1db0c8fb08b6f0f05, 0x8ca3088746cec35aeb3a8a54ed0e34ae7118a64fae8d4d0e2fd0e378e71ea874e8e88990e6d8ec2a8ec2e90a87aec6dac744b0ca190a83d0e338e7128ca2cea82c9066dd0c168eaf0aea9b8caddaa654, 0xd0e368a65290a868ec348ec338ca31cea298c8f3]

noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdCodes.getD (i / 32) 0
  decodeStep 9 secondAt ((block >>> (20 * (i % 32))) % 1048576)

def thirdBuckets : List ℕ := [0x402010078201d0807000001006820190806020170805800000805420140804c401108040200f08038200d08030400a0000000001002020070801800000801420040800c6000, 0x2037080d82035080d00000100c82031000000000000000000100bc202e100b0202b00000202a1809c2026000000000000000000080940000080902023000002022000000000, 0x816c40590816000000815c000008158000010150405200000000008144404f10134404b0000060481011820451010c404100000403f000000000080f8203d080f0403a080e42038, 0x8214208410208208108200207f081f8407c00000407a201d84074201c0606d101ac0000101a460660819400000000000001018c206200000206108180000000000405e101700000, 0x102a420a80000020a71029400001028c40a108280809c00000409a0000020990000000000826000000000080942024000000823c208e00000408c0822c208a082244087082180000, 0x831c00000000040c50000000000831040c20830420c0082fc20be0000040bc0000040ba0000040b8082dc00000000040b5082d020b3102c440af082b80000000000000082b440ab, 0x20e50000000000839060e10000040df1037420dc0836c00000836820d90000040d70835800000835400000835000000834c40d10000020d00000040ce2832400000000020c8, 0x21041040800001040020ff103f440fb000000000083e820f9083e040f6103d020f3083c840f0000000000183b440eb000000000000000000103a40000083a000000000040e6, 0x41230848841200847c211e0847400001046c00000846800000846421180845c21160845421140844c000000000211208444000000000610e00000410c0842c210a1841c4105, 0x852000000851c41451050c0000105042140104f80000104f0413a000000000000000000000006137084d82135000002134104c8612f104b4212c00000212b084a86127000004125, 0x105a421680859c216600000416400000216308588000010580415e08574215c1056841580855c21560855421540000021530854800000854400000854000000853c214e085348149, 0x1863400001062c418908620218708618618308608218108600617d00000417b000000000105e42178000000000105d82175105cc4171085c0000000000216f00000416d00000416b, 0x86b80000086b40000086b021ab086a841a80869c00000000041a50000000001068c21a21068000000867c219e08674219c0866c8197106544193000000000086482191000002190, 0x21d60875421d41874461ce2072821c91071c00001871000000000000000870c61c0086fc21be000000000086f421bc0000061b9106dc0000106d421b4106c80000106c021af, 0x87d821f5107cc21f2087c400000000041ef107b421ec0000021eb0000000002879821e50000000000000000000000021e41878421e00877c00001877041da0876421d80875c0000, 0x221810858221500000000008850000010848000008844820d1082c62080000000001881422041880461fe0000061fb000000000087e821f9000000000087e000000000021f7, 0x108bc000000000222e00000000000000422c108a82229088a042260000022250889000000888c00000000022221887c000000000000000000421d00000221c0886c0000108640000, 0x8934224c000000000109280000000000000089242248000000000000002247089186243089082241089000000108f8223d088f08238000000000108d82235108cc4231, 0x89b0426a00000626700000426508990226308988000008984226000000425e0897400001096c225a00000000010960425608954000008950225310944225000000424e000000000, 0x8a3c428d08a30628918a18228500000428308a080000000000000189fc227e000000000089f4227c089ec4279089e02277109d42274089cc0000089c80000189bc226e00000226d, 0x22a50000042a300000000000000000008a8822a108a80000010a78429c08a6c229a00000229908a60000000000000000000000000000429610a50000000000629108a400000, 0x8b1482c100000000008b0042be20ae800000000000000000022b900000000008ae042b60000022b500000000010acc22b20000000000000062af0000042ad10aac22aa10aa042a6, 0x10bb8000008bb462ea08ba482e510b8c000008b8842e008b7c000010b7442db00000000008b6862d70000022d600000000008b5442d328b38000018b2c42c908b2042c6000000000, 0x8c34430b00000000010c24000018c18000018c0c230210c0000000000042fe08bf400000000022fc08bec00000000042f908be0000018bd422f408bcc22f20000022f10000022f0, 0x8ca8000000000000008ca4000010c9c232608c94000000000232408c8c232200000000018c7c231e18c6c000008c68231908c60000000000231708c58231508c50431210c40430e, 0x234400000434210d00433e00000233d08cf0000008cec233a08ce4000008ce0233700000233608cd4433308cc8000008cc4000008cc0232f00000232e00000000010cb0232b, 0x236408d8c236210d80235f00000000000000000008d78435c00000000008d6c435930d4c635000000000000000000010d38234d08d30234b08d28000008d24000008d206345, 0x238c08e2c238a00000000000000238900000238818e14438308e08238108e00837c10de8237908de0000000000000010dd8437408dcc237208dc4836d10dac000020d9c4365, 0x23b000000000008ebc23ae10eb0000008eac63a808e9c43a508e9023a318e80239f10e74239c10e68000008e64239808e5c000008e58839208e44239008e3c000008e38238d, 0x18f5c23d600000000008f5423d418f44000010f3c000008f3863cb08f2800000000023c918f1843c410f0823c108f00000010ef823bd10eec000008ee8000018edc000018ed063b1, 0x900043fe10ff063f90000000000000023f828fcc000008fc8000008fc4000008fc023ef08fb823ed08fb043ea10fa043e608f9423e408f8c43e110f7c23de08f7443db08f680000, 0x44260000024251108c242221078241d1106c44190906000000905c241600000641319040440e09034240c00000240b00000240a210180000090140000090102403090082401]

def bucketMissing (count : ℕ) (atState : ℕ → SearchState)
    (table : List ℕ) (z : ℕ) (v : List W) : Bool :=
  st (z % 65521 % 1024) fun tag =>
    st (((table.getD (tag / 32) 0) >>> (18 * (tag % 32))) % 262144) fun code =>
      let a := code % 8192
      let n := code / 8192
      if a + n ≤ count then frontierMissing ((List.range' a n).map atState) z v else true

lemma bucketMissing_found {count : ℕ} {atState : ℕ → SearchState} {table : List ℕ}
    {z : ℕ} {v : List W} (h : bucketMissing count atState table z v = false) :
    ∃ i < count, atState i = (z,v) := by
  unfold bucketMissing at h
  simp only [st_eq] at h
  split at h
  · rename_i ok
    obtain ⟨i, hi, same⟩ := List.mem_map.mp (frontierMissing_false h)
    exact ⟨i, lt_of_lt_of_le (List.mem_range'_1.mp hi).2 ok, same⟩
  · contradiction


noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12)
      e8L rootPreparedMask rootPreparedSlots 10 0 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 10 9 0 z v))

lemma afterSecond_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 10)
    (mixed : mixedFromSecond state = false)
    (pure : pureAt 10 state (fun z v => afterThird (z,v)) = false) :
    afterSecond state = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false e8L 11 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 11 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 11 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [afterSecond, frc_eq, st_eq, show (11 : ℕ) = Nat.succ 10 from rfl, look1C_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 0) e8L state.2 (tstC I.NN I.AA I.HX I.HY false e8L 11 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 0) e8L state.2 (bif pureAt 10 state
      (look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 10 9 0)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeCheck_append (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all



noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  (!pureAt 10 state (bucketMissing thirdCount thirdAt thirdBuckets)) &&
    (decide (1 < state.2.length) && decide (state.2.length < 10))

noncomputable def thirdTest (j : ℕ) : Bool := !afterThird (thirdAt j)
noncomputable def secondMixedTest (j : ℕ) : Bool := !mixedFromSecond (secondAt j)

lemma checkedAfterSecond (i : ℕ) (hi : i < secondCount)
    (ready : rangeCheck readyForThird 0 secondCount = true)
    (mixed : rangeCheck secondMixedTest 0 secondCount = true)
    (third : rangeCheck thirdTest 0 thirdCount = true) :
    afterSecond (secondAt i) = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForThird, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, htwo, hsmall⟩ := h
  refine afterSecond_false (secondAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 10 (secondAt i) afterThird
    (bucketMissing thirdCount thirdAt thirdBuckets) (boolOfNeg hc) ?_
  intro z words found
  obtain ⟨j, hj, eq⟩ := bucketMissing_found found
  rw [← eq]
  exact boolOfNeg (rangeCheck_at third hj)

noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  (!pureSecond state (bucketMissing secondCount secondAt secondBuckets)) &&
    (decide (1 < state.2.length) && decide (state.2.length < 11))

noncomputable def mixedSecondPicked (state : SearchState) (b : Fin 8) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvPicked I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12)
      e8L rootPreparedMask rootPreparedSlots 11 0 z v 0 b))

lemma mixedSecondPicked_all (state : SearchState)
    (checked : ∀ b, mixedSecondPicked state b = false) : mixedSecond state = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  simp only [mixedSecond, frc_eq, st_eq] at h
  obtain ⟨b,hb⟩ := mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hc := checked b
  simp only [mixedSecondPicked, frc_eq, st_eq] at hc
  exact Bool.noConfusion (hc.symm.trans hb)

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    look1C I.NN I.AA I.HX I.HY e8L rootPreparedMask rootPreparedSlots 12 12 11 0
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 11 (firstAt i) afterSecond
    (bucketMissing secondCount secondAt secondBuckets) (boolOfNeg hc) ?_
  intro z words found
  obtain ⟨j, hj, eq⟩ := bucketMissing_found found
  rw [← eq]
  exact next j hj


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk3 : rangeCheck readyForSecond 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk4 : rangeCheck readyForSecond 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk5 : rangeCheck readyForSecond 20 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk6 : rangeCheck readyForSecond 24 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk7 : rangeCheck readyForSecond 28 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 firstCount = true := by
  exact (@rangeCheck_append readyForSecond 0 16 15
    (@rangeCheck_append readyForSecond 0 8 8
    (@rangeCheck_append readyForSecond 0 4 4
    firstCoverageChunk0 firstCoverageChunk1) (@rangeCheck_append readyForSecond 8 4 4
    firstCoverageChunk2 firstCoverageChunk3)) (@rangeCheck_append readyForSecond 16 8 7
    (@rangeCheck_append readyForSecond 16 4 4
    firstCoverageChunk4 firstCoverageChunk5) (@rangeCheck_append readyForSecond 24 4 3
    firstCoverageChunk6 firstCoverageChunk7)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 16 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 firstCount = true := by
  exact (@rangeCheck_append firstMixedTest 0 16 15
    firstMixedChunk0 firstMixedChunk1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 96 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 112 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 128 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 144 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 160 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 176 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk12 : rangeCheck readyForThird 192 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk13 : rangeCheck readyForThird 208 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk14 : rangeCheck readyForThird 224 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk15 : rangeCheck readyForThird 240 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk16 : rangeCheck readyForThird 256 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk17 : rangeCheck readyForThird 272 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk18 : rangeCheck readyForThird 288 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk19 : rangeCheck readyForThird 304 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk20 : rangeCheck readyForThird 320 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk21 : rangeCheck readyForThird 336 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 secondCount = true := by
  exact (@rangeCheck_append readyForThird 0 176 162
    (@rangeCheck_append readyForThird 0 80 96
    (@rangeCheck_append readyForThird 0 32 48
    (@rangeCheck_append readyForThird 0 16 16
    secondCoverageChunk0 secondCoverageChunk1) (@rangeCheck_append readyForThird 32 16 32
    secondCoverageChunk2 (@rangeCheck_append readyForThird 48 16 16
    secondCoverageChunk3 secondCoverageChunk4))) (@rangeCheck_append readyForThird 80 48 48
    (@rangeCheck_append readyForThird 80 16 32
    secondCoverageChunk5 (@rangeCheck_append readyForThird 96 16 16
    secondCoverageChunk6 secondCoverageChunk7)) (@rangeCheck_append readyForThird 128 16 32
    secondCoverageChunk8 (@rangeCheck_append readyForThird 144 16 16
    secondCoverageChunk9 secondCoverageChunk10)))) (@rangeCheck_append readyForThird 176 80 82
    (@rangeCheck_append readyForThird 176 32 48
    (@rangeCheck_append readyForThird 176 16 16
    secondCoverageChunk11 secondCoverageChunk12) (@rangeCheck_append readyForThird 208 16 32
    secondCoverageChunk13 (@rangeCheck_append readyForThird 224 16 16
    secondCoverageChunk14 secondCoverageChunk15))) (@rangeCheck_append readyForThird 256 48 34
    (@rangeCheck_append readyForThird 256 16 32
    secondCoverageChunk16 (@rangeCheck_append readyForThird 272 16 16
    secondCoverageChunk17 secondCoverageChunk18)) (@rangeCheck_append readyForThird 304 16 18
    secondCoverageChunk19 (@rangeCheck_append readyForThird 320 16 2
    secondCoverageChunk20 secondCoverageChunk21)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 96 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 112 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk8 : rangeCheck secondMixedTest 128 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk9 : rangeCheck secondMixedTest 144 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk10 : rangeCheck secondMixedTest 160 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk11 : rangeCheck secondMixedTest 176 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk12 : rangeCheck secondMixedTest 192 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk13 : rangeCheck secondMixedTest 208 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk14 : rangeCheck secondMixedTest 224 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk15 : rangeCheck secondMixedTest 240 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk16 : rangeCheck secondMixedTest 256 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk17 : rangeCheck secondMixedTest 272 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk18 : rangeCheck secondMixedTest 288 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk19 : rangeCheck secondMixedTest 304 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk20 : rangeCheck secondMixedTest 320 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk21 : rangeCheck secondMixedTest 336 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 secondCount = true := by
  exact (@rangeCheck_append secondMixedTest 0 176 162
    (@rangeCheck_append secondMixedTest 0 80 96
    (@rangeCheck_append secondMixedTest 0 32 48
    (@rangeCheck_append secondMixedTest 0 16 16
    secondMixedChunk0 secondMixedChunk1) (@rangeCheck_append secondMixedTest 32 16 32
    secondMixedChunk2 (@rangeCheck_append secondMixedTest 48 16 16
    secondMixedChunk3 secondMixedChunk4))) (@rangeCheck_append secondMixedTest 80 48 48
    (@rangeCheck_append secondMixedTest 80 16 32
    secondMixedChunk5 (@rangeCheck_append secondMixedTest 96 16 16
    secondMixedChunk6 secondMixedChunk7)) (@rangeCheck_append secondMixedTest 128 16 32
    secondMixedChunk8 (@rangeCheck_append secondMixedTest 144 16 16
    secondMixedChunk9 secondMixedChunk10)))) (@rangeCheck_append secondMixedTest 176 80 82
    (@rangeCheck_append secondMixedTest 176 32 48
    (@rangeCheck_append secondMixedTest 176 16 16
    secondMixedChunk11 secondMixedChunk12) (@rangeCheck_append secondMixedTest 208 16 32
    secondMixedChunk13 (@rangeCheck_append secondMixedTest 224 16 16
    secondMixedChunk14 secondMixedChunk15))) (@rangeCheck_append secondMixedTest 256 48 34
    (@rangeCheck_append secondMixedTest 256 16 32
    secondMixedChunk16 (@rangeCheck_append secondMixedTest 272 16 16
    secondMixedChunk17 secondMixedChunk18)) (@rangeCheck_append secondMixedTest 304 16 18
    secondMixedChunk19 (@rangeCheck_append secondMixedTest 320 16 2
    secondMixedChunk20 secondMixedChunk21)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 65 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 130 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 195 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 260 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 325 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 390 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 455 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 520 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 585 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 650 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 715 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 780 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 845 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 910 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 975 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 1040 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 thirdCount = true := by
  exact (@rangeCheck_append thirdTest 0 520 544
    (@rangeCheck_append thirdTest 0 260 260
    (@rangeCheck_append thirdTest 0 130 130
    (@rangeCheck_append thirdTest 0 65 65
    thirdTailChunk0 thirdTailChunk1) (@rangeCheck_append thirdTest 130 65 65
    thirdTailChunk2 thirdTailChunk3)) (@rangeCheck_append thirdTest 260 130 130
    (@rangeCheck_append thirdTest 260 65 65
    thirdTailChunk4 thirdTailChunk5) (@rangeCheck_append thirdTest 390 65 65
    thirdTailChunk6 thirdTailChunk7))) (@rangeCheck_append thirdTest 520 260 284
    (@rangeCheck_append thirdTest 520 130 130
    (@rangeCheck_append thirdTest 520 65 65
    thirdTailChunk8 thirdTailChunk9) (@rangeCheck_append thirdTest 650 65 65
    thirdTailChunk10 thirdTailChunk11)) (@rangeCheck_append thirdTest 780 130 154
    (@rangeCheck_append thirdTest 780 65 65
    thirdTailChunk12 thirdTailChunk13) (@rangeCheck_append thirdTest 910 65 89
    thirdTailChunk14 (@rangeCheck_append thirdTest 975 65 24
    thirdTailChunk15 thirdTailChunk16)))))

def initialIndices (kind : Bool) : List ℕ := if kind then [1, 2, 4, 6, 8, 9, 10, 12, 14, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 29, 30] else [0, 3, 5, 7, 11, 13, 15, 22, 24, 27]

noncomputable def initialStates (kind : Bool) : List SearchState := (initialIndices kind).map firstAt

lemma allInitialIndices (kind : Bool) : (initialIndices kind).all (fun i => decide (i < firstCount)) = true := by
  cases kind <;> decide +kernel

lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) : chkPairPicked [] e8Q 8 12 0 FF 0 kind = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : chk [] e8Q 8 12 0 FF 0 = false :=
  chkPair_picked [] e8Q 8 12 0 FF 0 binaryCertificate


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked0 : chkPicked [] e8Q 8 12 0 0 1 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked1 : chkPicked [] e8Q 8 12 0 0 1 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked2 : chkPicked [] e8Q 8 12 0 0 1 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked3 : chkPicked [] e8Q 8 12 0 0 1 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked4 : chkPicked [] e8Q 8 12 0 0 1 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked5 : chkPicked [] e8Q 8 12 0 0 1 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked6 : chkPicked [] e8Q 8 12 0 0 1 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked7 : chkPicked [] e8Q 8 12 0 0 1 7 = false := by decide +kernel

lemma unaryChecked : chk [] e8Q 8 12 0 0 1 = false := by
  apply chk_picked
  intro b
  fin_cases b
  · exact unaryChecked0
  · exact unaryChecked1
  · exact unaryChecked2
  · exact unaryChecked3
  · exact unaryChecked4
  · exact unaryChecked5
  · exact unaryChecked6
  · exact unaryChecked7


def rootCases : List (ℕ × ℕ) := [(FF, 0), (0, 1)]

lemma rootCases_full : mFull rootCases = true := by decide +kernel

lemma certify_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] e8Q 8 12 0 p.1 p.2 = false := by
  refine ⟨rootCases, rootCases_full, ?_⟩
  intro p hp
  simp only [rootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked



end CofactorEight

lemma e8_0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧
    ∀ p ∈ M, chk [] e8Q 8 12 0 p.1 p.2 = false :=
  CofactorEight.certify_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case0_false : chkPairPicked [] e8Q 8 12 1 0x400 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case0_true : chkPairPicked [] e8Q 8 12 1 0x400 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case0 : chk [] e8Q 8 12 1 0x400 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case0_false
  · exact e8_1_case0_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case1_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case1_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case1 : chk [] e8Q 8 12 1 0x1000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case1_false
  · exact e8_1_case1_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case2_false : chkPairPicked [] e8Q 8 12 1 0x400000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case2_true : chkPairPicked [] e8Q 8 12 1 0x400000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case2 : chk [] e8Q 8 12 1 0x400000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case2_false
  · exact e8_1_case2_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case3_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case3_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case3 : chk [] e8Q 8 12 1 0x1000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case3_false
  · exact e8_1_case3_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case4_false : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case4_true : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case4 : chk [] e8Q 8 12 1 0x10000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case4_false
  · exact e8_1_case4_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case5_false : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case5_true : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case5 : chk [] e8Q 8 12 1 0x40000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case5_false
  · exact e8_1_case5_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case6_false : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case6_true : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case6 : chk [] e8Q 8 12 1 0x100000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case6_false
  · exact e8_1_case6_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case7_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case7_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case7 : chk [] e8Q 8 12 1 0x1000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case7_false
  · exact e8_1_case7_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case8_false : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case8_true : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case8 : chk [] e8Q 8 12 1 0x4000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case8_false
  · exact e8_1_case8_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case9_false : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case9_true : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case9 : chk [] e8Q 8 12 1 0x100000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case9_false
  · exact e8_1_case9_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case10_false : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case10_true : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case10 : chk [] e8Q 8 12 1 0x10000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case10_false
  · exact e8_1_case10_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case11_false : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case11_true : chkPairPicked [] e8Q 8 12 1 0x100000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case11 : chk [] e8Q 8 12 1 0x100000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case11_false
  · exact e8_1_case11_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case12_false : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case12_true : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case12 : chk [] e8Q 8 12 1 0x10000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case12_false
  · exact e8_1_case12_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case13_false : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case13_true : chkPairPicked [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case13 : chk [] e8Q 8 12 1 0x10000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case13_false
  · exact e8_1_case13_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case14_false : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case14_true : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case14 : chk [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case14_false
  · exact e8_1_case14_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case15_false : chkPairPicked [] e8Q 8 12 1 0x400000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case15_true : chkPairPicked [] e8Q 8 12 1 0x400000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case15 : chk [] e8Q 8 12 1 0x400000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case15_false
  · exact e8_1_case15_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case16_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case16_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case16 : chk [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case16_false
  · exact e8_1_case16_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case17_false : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case17_true : chkPairPicked [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case17 : chk [] e8Q 8 12 1 0x1000000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case17_false
  · exact e8_1_case17_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case18_false : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case18_true : chkPairPicked [] e8Q 8 12 1 0x4000000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case18 : chk [] e8Q 8 12 1 0x4000000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case18_false
  · exact e8_1_case18_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case19_false : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000000000 0 false = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case19_true : chkPairPicked [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000000000 0 true = false := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_e8]
  decide +kernel

lemma e8_1_case19 : chk [] e8Q 8 12 1 0x40000000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact e8_1_case19_false
  · exact e8_1_case19_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_1_case20 : chk [] e8Q 8 12 1 0x3baffebbffeffefeefefbffeefffbffeefffbffffefffffffffbff 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

lemma e8_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧
    ∀ p ∈ M, chk [] e8Q 8 12 1 p.1 p.2 = false := by
  refine ⟨e8Cases, e8Full, fun p hp => ?_⟩
  simp only [e8Cases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e8_1_case0
  · exact e8_1_case1
  · exact e8_1_case2
  · exact e8_1_case3
  · exact e8_1_case4
  · exact e8_1_case5
  · exact e8_1_case6
  · exact e8_1_case7
  · exact e8_1_case8
  · exact e8_1_case9
  · exact e8_1_case10
  · exact e8_1_case11
  · exact e8_1_case12
  · exact e8_1_case13
  · exact e8_1_case14
  · exact e8_1_case15
  · exact e8_1_case16
  · exact e8_1_case17
  · exact e8_1_case18
  · exact e8_1_case19
  · exact e8_1_case20

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_2 : chk [] e8Q 8 12 2 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_3 : chk [] e8Q 8 12 3 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_4 : chk [] e8Q 8 12 4 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_5 : chk [] e8Q 8 12 5 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_6 : chk [] e8Q 8 12 6 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_7 : chk [] e8Q 8 12 7 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_8 : chk [] e8Q 8 12 8 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_9 : chk [] e8Q 8 12 9 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_10 : chk [] e8Q 8 12 10 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_11 : chk [] e8Q 8 12 11 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma e8_12 : chk [] e8Q 8 12 12 FF 1 = false := by
  rw [← chkFast_eq, chkFast, searchInputs_e8]
  decide +kernel

lemma one_e8 {t : ℕ} (h : chk [] e8Q 8 12 t FF 1 = false) :
    ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] e8Q 8 12 t p.1 p.2 = false :=
  ⟨[(FF,1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h⟩

lemma strongRow8 : Imp [] 8 13 := by
  apply imp_of (Or.inl rfl) e8Ok (by decide)
  · intro e he
    unfold e8Q pr at he
    exact hv1 e (List.mem_of_mem_filter (List.mem_of_mem_filter he))
  · right
    intro t ht
    interval_cases t
    · exact e8_0
    · exact e8_1
    · exact one_e8 e8_2
    · exact one_e8 e8_3
    · exact one_e8 e8_4
    · exact one_e8 e8_5
    · exact one_e8 e8_6
    · exact one_e8 e8_7
    · exact one_e8 e8_8
    · exact one_e8 e8_9
    · exact one_e8 e8_10
    · exact one_e8 e8_11
    · exact one_e8 e8_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked1 : okE [] (pr pv1 1) (1,12) = true := by decide +kernel

lemma strongRow1 : Imp [] 1 12 :=
  imp_okE (Or.inl rfl) strongChecked1 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked2 : okE [] (pr pv1 2) (2,12) = true := by decide +kernel

lemma strongRow2 : Imp [] 2 12 :=
  imp_okE (Or.inl rfl) strongChecked2 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked4 : okE [] (pr pv1 4) (4,12) = true := by decide +kernel

lemma strongRow4 : Imp [] 4 12 :=
  imp_okE (Or.inl rfl) strongChecked4 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked16 : okE [] (pr pv1 16) (16,11) = true := by decide +kernel

lemma strongRow16 : Imp [] 16 11 :=
  imp_okE (Or.inl rfl) strongChecked16 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked32 : okE [] (pr pv1 32) (32,11) = true := by decide +kernel

lemma strongRow32 : Imp [] 32 11 :=
  imp_okE (Or.inl rfl) strongChecked32 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked64 : okE [] (pr pv1 64) (64,11) = true := by decide +kernel

lemma strongRow64 : Imp [] 64 11 :=
  imp_okE (Or.inl rfl) strongChecked64 (fun e he => hv1 e (List.mem_of_mem_filter he))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongChecked128 : okE [] (pr pv1 128) (128,11) = true := by decide +kernel

lemma strongRow128 : Imp [] 128 11 :=
  imp_okE (Or.inl rfl) strongChecked128 (fun e he => hv1 e (List.mem_of_mem_filter he))

lemma strongRows_sound : ∀ e ∈ rStrong, Imp [] e.1 e.2 := by
  intro p hp
  simp only [rStrong, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact strongRow1
  · exact strongRow2
  · exact strongRow4
  · exact strongRow8
  · exact strongRow16
  · exact strongRow32
  · exact strongRow64
  · exact strongRow128

def rootBounds : List (ℕ × ℕ) :=
  (rStrong ++ pv1.filter (fun e => !(rStrong.any fun t => t.1 == e.1))).filter (fun p => p.2 ≥ 5)
lemma rootBounds_sound : ∀ p ∈ rootBounds, Imp [] p.1 p.2 := by
  intro p hp
  rcases List.mem_append.mp (List.mem_of_mem_filter hp) with h | h
  · exact strongRows_sound p h
  · exact hv1 p (List.mem_of_mem_filter h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_p : pOk 0 rootBounds = true := by decide +kernel

private def graph : (Fin 8 → Bool) → Bool := fun x =>
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

private def witness : Circuit := ⟨[
   ⟨.or, [4, 3]⟩,
   ⟨.or, [7, 0]⟩,
   ⟨.and, [8, 9]⟩,
   ⟨.and, [1, 4]⟩,
   ⟨.or, [2, 1]⟩,
   ⟨.or, [7, 5]⟩,
   ⟨.and, [12, 13]⟩,
   ⟨.or, [4, 2]⟩,
   ⟨.or, [15, 0]⟩,
   ⟨.and, [16, 6]⟩,
   ⟨.and, [5, 7]⟩,
   ⟨.or, [10, 11]⟩,
   ⟨.or, [19, 14]⟩,
   ⟨.or, [20, 17]⟩,
   ⟨.or, [21, 18]⟩], 22⟩

lemma witness_basis : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

lemma witness_size : witness.gates.length = 15 := rfl

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)

lemma f_graph (x : Fin 8 → Bool) : f x = graph x := by
  have hx : f x = true ↔ (x 0 = true ∧ x 3 = true) ∨ (x 0 = true ∧ x 4 = true) ∨ (x 1 = true ∧ x 4 = true) ∨ (x 1 = true ∧ x 5 = true) ∨ (x 2 = true ∧ x 5 = true) ∨ (x 0 = true ∧ x 6 = true) ∨ (x 2 = true ∧ x 6 = true) ∨ (x 4 = true ∧ x 6 = true) ∨ (x 1 = true ∧ x 7 = true) ∨ (x 2 = true ∧ x 7 = true) ∨ (x 3 = true ∧ x 7 = true) ∨ (x 4 = true ∧ x 7 = true) ∨ (x 5 = true ∧ x 7 = true) := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  unfold graph
  rw [Bool.eq_iff_iff, hx, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h)
    · exact ⟨0, by decide, by simpa using h⟩
    · exact ⟨1, by decide, by simpa using h⟩
    · exact ⟨2, by decide, by simpa using h⟩
    · exact ⟨3, by decide, by simpa using h⟩
    · exact ⟨4, by decide, by simpa using h⟩
    · exact ⟨5, by decide, by simpa using h⟩
    · exact ⟨6, by decide, by simpa using h⟩
    · exact ⟨7, by decide, by simpa using h⟩
    · exact ⟨8, by decide, by simpa using h⟩
    · exact ⟨9, by decide, by simpa using h⟩
    · exact ⟨10, by decide, by simpa using h⟩
    · exact ⟨11, by decide, by simpa using h⟩
    · exact ⟨12, by decide, by simpa using h⟩
  · rintro ⟨i, hi, h⟩
    have hi' : i < 13 := hi
    interval_cases i <;> simp_all

set_option maxHeartbeats 5000000 in
lemma witness_eval (x : Fin 8 → Bool) : witness.eval (List.ofFn x) = graph x := by
  rw [← f_graph]
  simp only [witness, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  change ((((((x 4 || x 3) && (x 7 || x 0)) || (x 1 && x 4)) || ((x 2 || x 1) && (x 7 || x 5))) || (((x 4 || x 2) || x 0) && x 6)) || (x 5 && x 7)) = f x
  unfold f
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

def EF : ℕ := (((((((((((((rawP0.getD 0 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 5 0 &&& rawP0.getD 7 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP0.getD v.val 0).testBit b) = rawP0.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len0]
  · intro i h1 h2
    have : i < rawP0.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨out, hout⟩
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hu : UniqueNot gates) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length 1 S0 := by
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD o 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) o
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD o false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hu hnot ⟨o, hout⟩

def rootPreparedWords : List W := [
  ⟨0x1ffffdffffdf00000000000000000000000000000000000000000000000000000000000004894c04e000170000b8001380138000000000180000006000600000000001800180000000c006000018000000000000000000ffe00ffe00fbf00041f80021007e000821f80011f80021043f0004213f00042088203e00b56b6ab7ffaabffd55ffeadffedffe000000000000000000000000000000000000000000000000000000026863f8391937ac7, 0x80000000100000000200000100000080000000000000004210000108421080000002100420000000000000000004210000000000084200000000000000210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x40000000004210840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x40000000004210840000000080000000100000000200000100000080000000000000004210000108421080000002100420000000000000000004210000000000084200000000000000210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 3⟩,
  ⟨0x1ffffc0000007fffefbffff7bee00000000000000000000000000000000000000000000016ad6800980004c000260002600260125ab428570092885c025c0000000001600160000000b005800016000000000000000000fc1c0801c0020fe07d07f03df701e004000780000780108200f0020000f00210440201c0b56b60000000000000000000000000dad5b56afff6d56bffdbffc00000000000000000000000000000000a4cfbb63b53967a1, 0x4000000008000000010000000000004000000000000000000000100000004000002008000084210000000000000000042108400000010842108420000210000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x2000000000000002108421000000000000000000000000000000000000000108421080000000000000000000000000000000000000000421080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000000000000002108421004000000008000000010000000000004000000108421080000000100000004000002008000084210000000421080000042108400000010842108420000210000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 3⟩,
  ⟨0x1ffffc000000000000000000000003ffff8000000000000000007fffe07c1f070000000040642201211009089190919090000020008440021212121300010028c888c8880020a44422312488c000000000000000004046d544600012304005184110024608504f4c000858410801070848459703e0f8380460000603000008000040008c000c0000010300000001508001bffc0818034600060000850d0003ffdb6ffffb1b26c7ec74e930, 0x1000000000000000004000000000000000000000000401080000000000000084210840000000000000000000021080000000000000000000842108420084000000000001000000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x80000000000000000000000000000000000000000000084210842000000000000000000000000000000000000084210842108000000000042108421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x80000000000001000000000000000004000000000000084210842000401080000000000000084210840000000084210842108021080000042108421000000842108420084000000000001000000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 3⟩,
  ⟨0x7fffef800000000ffffdf7bffffb8000000000000000000000000000000012000152170000b0000580005800581b52a60004c000001300130254b126085c085c0000002c016000058000000000000000008203060030830f187c840c0080611f0fbd847e1d00700040200e0110200e010822102030b0000ab7ff80000000000000000000dad5b000000000000000001ab5adb56fff6fff0000000000000000084bd5419e9fb170e, 0x4000002000000000000000000400000000800008000000200000000000000000000008000000200000108401000000000000000000000000000000084210840000001080000842000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x100000000000000000000084210840000000000000000000000000000000000000004210842000000000000000000000000000000000000004210800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x100000004000002000000084210840000400000000800008000000200000000000004210842008000000200000108401000000000000000004210800000000084210840000001080000842000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 3⟩,
  ⟨0x7fffe03ffff7800ffffc078000003ffff78007fffef7b000000000000000102401101cc500ea2a077000760076185a00ac06a8da801ac01ac35005b4007300730d68003a81d424877000000000000000002080206002224f010126c0bc00491c203c202040a44cbc000c4937bd8800300200808802816008800028000155ffe000000000c2d005600006d4000000001a802db0000000006b4000000001b6fff7c284fed028b254b, 0x10000008000000010002000000000000040000020000000800100021004000840000000000000000000000004000800108420084200840008421084010802000421084200800100421000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x400000000000000000000000000108421084000000000000000000000000000000000000108421084210840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000010000008000000010002108421084000040000020000000800100021004000840108421084210840000000004000800108420084200840008421084010802000421084200800100421000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 3⟩,
  ⟨0x3ffff03e000000000000000000000007fffe0787fffef001f7000000202000086000432202294023082380081020420cc22c08630860000410a0218421c4224210e08630c2280000000000000000082180061808120c090ec601f002098108080704081a0821094ba03c054ba7800fb80218010300000000000110000a0000dffe00c18102000611600018000204218500006fff631617ff800186000289adfbe3e7ad990, 0x40000020000000040000000080000002000000000000002000000000010042000001000000040000000000010002008000000210800100401004200000008021004000002008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x1000000000000000000000000000000000000000108421000000000000000000000000000000000000000000421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000040000020000000040000000080000002108421000000002000000000010042000001000000040000421000010002008000000210800100401004200000008021004000002008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 3⟩,
  ⟨0xffffdf00000003ffff7bef00000000000000000000000000001400485402c000140001400140900008500b000000280028356a000001200120948900b005800014000000000000000004110c1810c4088862043031044519ccf80424180c64f3df79081c0081081c0840109110c04000a00002abffc00000000000000d800056afff000000000001ab58000000000006b56d7ffbffc0000051ff4ca4c6a68795, 0x200000100000000200000000020000000000000400000010000108400000000000000400000010000000021080000842000421000000042100021000000002108000004000000108000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x8000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x8000000200000100000000200002000020000000000000400000010000108400000000000000400000010000000021080000842000421000000042100021000000002108000004000000108000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 3⟩,
  ⟨0x3ffff03e07fffef007fffef7dc0000000000000000e4400b2800694807800700000081002c482500f000e1020480a403c0038d02d802c0163600680000000000000000104a0018a01024501010a8082204520210111808956c01f00a6d2780066d27bee00004a0000800000022000140000adffe0000020404080006c16bffc00018302c056fff00006816c0000001b00003a33cd08dd25e728, 0x800000400000000800000001000000000000001000000040008020080200802000020000000800000000000200040100401084010802008020080210040100401080010040000400080010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x20000000000000000000000000000000000210842000000000000000000000000000000000000000000002108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000800000400000000800000001000210842000001000000040008020080200802000020000000802108000000200040100401084010802008020080210040100401080010040000400080010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 3⟩]
def rootPreparedMask : ℕ := 0x1ffffdffffdf7fffefbffff7beeffffdf7bffffbbffff7bef7fffef7b7fffef7ddf777ffd6ad6d56fff557ffaabffd5bffdbffdb5ab6ad5ffedaad7ffb7ffb56b5b6adffedffed6adafff7ffb6dffe0000000000000000ffffeffffefbffff7dffffbdf77fffefbdffffddffffbdf7bffff7bdbffff7beefbbbffeb56b6ab7ffaabffd55ffeadffedffedad5b56afff6d56bffdbffdab5adb56fff6fff6b56d7ffbffdb6fffffffffffffffffff
def rootPreparedSlots : ℕ := 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
def rootPreparedBudget : ℕ := 0x62d6cd6f7b6739ce737bdf37be737bdf36c6318c5b18c6738c6339cdf37bdef8c6318c6318c6319ce739be739ce739ce739c6318c6318c6739ce739ce739ce739ce739ce739ce739ce739c6319cdef7ce718ce337be2f7be718ce6f9b6318c6717be738bdf19bdaf5b5af6b56b6adab5adad6ada95a5ad69ce738ca52

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedWords_eq : avl (PZ rootBounds) (mz 0) (rawL []) = rootPreparedWords :=
  Eq.refl rootPreparedWords
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedMask_eq : mz 0 = rootPreparedMask := Eq.refl rootPreparedMask
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedSlots_eq : pL (rootBounds.map fun _ => 16) = rootPreparedSlots := Eq.refl rootPreparedSlots
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedBudget_eq : pL (rootBounds.map fun e => 16 + (14 - e.2)) = rootPreparedBudget :=
  Eq.refl rootPreparedBudget
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedL_eq : lz 0 = I.AA := Eq.refl I.AA
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allRootInputsNeeded (d : Bool) :
    allInputsNeeded I.NN d I.AA rootPreparedWords 0 = true := by
  cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma searchInputs_atRoot (t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    searchInputs [] rootBounds 0 14 t H ph test =
      guardStart t H ph (test I.NN I.AA I.HX I.HY I.AA rootPreparedMask
        rootPreparedSlots rootPreparedBudget 0) rootPreparedWords := by
  simp only [searchInputs, frc_eq, st_eq, rootPreparedWords_eq, rootPreparedMask_eq,
    rootPreparedSlots_eq, rootPreparedBudget_eq, rootPreparedL_eq]
  change anySubC I.NN (pos t) I.AA rootPreparedWords 0 _ = _
  rw [anySub_allInputs (allRootInputsNeeded (pos t))]
  rfl






lemma pair_distribute {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pair f a c = true → ∃ b, pair (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,bR]
  cases hb : f w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · simp only [hb,Bool.cond_false]
    intro hor
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hor
    refine ⟨b, ?_⟩
    rw [hb]
    simp
  · intro _
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hb
    exact ⟨b,by rw [hb]; rfl⟩



noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootStart_eq (H : ℕ) (kind : Bool) :
    startPairPicked I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots rootPreparedBudget
      14 1 0 H 0 rootPreparedWords kind =
    initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) := by
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 8 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  simp only [startPairPicked, child, st_eq, topPairPicked, bR, haveRequired, len, budget,
    show Nat.ble 8 (Nat.sub 15 1) = true from rfl, show Nat.ble 8 1 = false from rfl,
    Bool.cond_true, Bool.cond_false]
  change (bif initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) then true else false) = _
  cases initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialBinary_of_check (H : ℕ) (kind : Bool)
    (h : chkPairPicked [] rootBounds 0 14 1 H 0 kind = true) :
    initialBinary H kind
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = true := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_atRoot] at h
  simp only [guardStart, rootStart_eq, bR] at h
  cases hp : relevantStart 1 H 0 rootPreparedWords
  · simp [hp] at h
  · simpa [hp] using h

def wordEquals (a b : W) : Bool :=
  (a.s == b.s) && (a.a == b.a) && (a.b == b.b) && (a.c == b.c) && (a.r == b.r)

lemma wordEquals_spec {a b : W} (h : wordEquals a b = true) : a = b := by
  cases a
  cases b
  simp [wordEquals, Bool.and_eq_true] at h ⊢
  rcases h with ⟨⟨⟨⟨hs, ha⟩, hb⟩, hc⟩, hr⟩
  exact ⟨hs, ha, hb, hc, hr⟩

def frontierMissing (states : List (ℕ × List W)) (z : ℕ) (v : List W) : Bool :=
  !(states.any fun state => (z == state.1) && List.isEqv v state.2 wordEquals)

noncomputable def rootWithGate (i j mask : ℕ) (kind : Bool) : List W :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD i zero
  let b := rootPreparedWords.getD j zero
  let keep := (rootPreparedWords.zipIdx.filter fun e => mask.testBit e.2).map Prod.fst
  addS (opW kind a b) keep

lemma frontierMissing_false {states : List (ℕ × List W)} {z : ℕ} {v : List W}
    (h : frontierMissing states z v = false) : (z, v) ∈ states := by
  simp only [frontierMissing, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨j, w⟩, membership, rfl, he⟩ := h
  have hw : v = w := by
    clear membership
    induction v generalizing w with
    | nil => cases w <;> simp_all [List.isEqv]
    | cons a v ih =>
      cases w with
      | nil => simp [List.isEqv] at he
      | cons b w =>
        simp only [List.isEqv, Bool.and_eq_true] at he
        rw [wordEquals_spec he.1, ih w he.2]
  rwa [hw]

lemma initialBinary_from_frontier (H : ℕ) (kind : Bool) (states : List (ℕ × List W))
    (complete : initialBinary H kind (frontierMissing states) = false)
    (checked : ∀ state ∈ states,
      look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false) :
    chkPairPicked [] rootBounds 0 14 1 H 0 kind = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  have original := initialBinary_of_check H kind h
  unfold initialBinary at original complete
  obtain ⟨_, hit⟩ := nodePicked_distribute
    (branches := fun _ => frontierMissing states)
    I.NN true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind
    (fun z v hit => by
      refine ⟨0, ?_⟩
      cases hm : frontierMissing states z v
      · exact Bool.noConfusion ((checked (z,v) (frontierMissing_false hm)).symm.trans hit)
      · exact hm)
    original
  exact Bool.noConfusion (complete.symm.trans hit)

abbrev SearchState := ℕ × List W

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f true I.AA rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 12 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1 z v))

lemma pureAt_of_covered (e : ℕ) (state : SearchState) (remaining : SearchState → Bool)
    (miss : ℕ → List W → Bool)
    (complete : pureAt e state miss = false)
    (covered : ∀ z v, miss z v = false → remaining (z,v) = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => miss)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : miss z v
        · exact Bool.noConfusion ((covered z v missed).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma pureAt_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : pureAt e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    pureAt e state (fun z v => remaining (z,v)) = false :=
  pureAt_of_covered e state remaining (frontierMissing states) complete
    (fun z v h => checked (z,v) (frontierMissing_false h))

lemma pureSecond_from_frontier (state : SearchState) (states : List SearchState)
    (complete : pureSecond state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, afterSecond x = false) :
    pureSecond state (fun z v => afterSecond (z,v)) = false :=
  pureAt_from_frontier 12 state states afterSecond complete checked

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (14 : ℕ) = Nat.succ 13 from rfl, look1C_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureSecond state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def secondTransition (state : SearchState) (i j kept : ℕ) (kind : Bool) : SearchState :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := state.2.getD i zero
  let b := state.2.getD j zero
  let word := opW kind a b
  let keptWords := (state.2.zipIdx.filter fun e => kept.testBit e.2).map Prod.fst
  let budget := Nat.sub (Nat.add state.1 (Nat.land a.c b.c)) word.c
  let usedA := if kept.testBit i then a.c else 0
  let usedB := if kept.testBit j then b.c else 0
  (Nat.sub (Nat.sub budget usedA) usedB, addS word keptWords)

noncomputable def firstStates : List SearchState := [
  ⟨0x5a95c52d6adad6b5ad4a52d49d6f5ad6f2a5ad6b5294b5ef4b5af7acef5ad6b4a5294a4e73ad6b4a5294952d6b5a94a52969ce73ad6b5ad294a4e73ace739ceb59ce739ce739ce75ad6949ce74a4a52a5273a4e9294e5295273b5a969d6b5adab4a5ad5a52b69ca7194a72946328d2739d2949d253952948425284631, rootWithGate 0 1 255 false⟩,
  ⟨0x5675c52d6ad6b5ad6b39ceb3a5af5ad6f3adad6b52b5b5ef5b5af7b52f5ad6b39ce739d294ad6b4ad6b59d6d6b5a95ad6b6a5294ad6b5ace739d294ad294a52b5a5294a5294a5295ad694a5295ace73ad694ad2b39d2739d694b5a969d6b5adab4a5ad5a52b69ce929ce939ca53952739d2949d253952948c65284631, rootWithGate 0 1 255 true⟩,
  ⟨0x56b5c52d69d6b5ad6f5ad6f4a5ef5ad6f3b5ad6b4eb6b5ef5b5af7aceb39ce75ad2b4a5294ad6b5ad6b5956b5ad6b5b56b69ce739ce739d694a5294ace739ce73a5295a5294a5295a52b5a5295ace72adab5b52d4a52949da94b5a959d695a56b49dab4a4e95a4e929ce74a4e74952739ce949ce538d2738ca5284630, rootWithGate 0 2 255 true⟩,
  ⟨0x5ab4c52d6ad6d6b5ab5ad6f59dad4a52f2b52d6b5296a5ef4a5af7ad6b5ad6b5ad6b5ace73a5294a529495a96b5a94a5294ad6b5ad6b5ad6b5ace73a56b5ad6b59ce739ceb5ad6b39d6949ce74a4a52a5273a4ed4a5694a5ab5a52548ce739d2b4a5ad5a52b69ca7194a72a4e749ca318ca949d2539529484a1284631, rootWithGate 0 3 255 false⟩,
  ⟨0x56b3c52d6ad6b5ad6d5ad6f59d6b39cef3b56d6b52b6adef5adaf7b56d5ad6b5ad6b5ace739ce75a56b59dab6b5ab4ad2b5ad6b5ad6b5ad6b5ace739d6b5ad6b59ce74a52b5ad6b4a56b59ce75ace73ad694ad2d4a5694a5ab5ad67595294a56b4a5ad5a52b6a4a929ce93a4e749ce5294e949d253952948ca3284631, rootWithGate 0 3 255 true⟩,
  ⟨0x56b5c52d4ad6b5ad6f5ad6d5a5ef5ad2f3b5ad6ad2b6b5ed4a52b5b56f5ad695ad6b5ad293ad295ad6b49dad6b56b5b5294ad6b4ad695a56b5ad273a56b4ad2b4a4e75ad6b5a5694ad2b5a5275a4e53a5ab5ad6d49d693a56b4b5a769d2b4ad6b3a56d49d295a4e929ca94a4e739d273952949525294e938ca5284611, rootWithGate 0 5 255 true⟩,
  ⟨0x5ab5bd2d6adab6b5af3ad6f59deb5ad6d2b5a96b5296b5ef4b52f7ad6f3ad6b39ceb5ace73ad6b4a529495ad4b5a94b52949d6b59ce75ace73ace73ace73ad6739ce75ad6739d6b5ace949ce74a4a52a52b5b569294e94a5ab5a52549d6b5ada7295293a52b69ca7194a7494e749ca739d2528ca539529484a5084631, rootWithGate 0 6 255 false⟩,
  ⟨0x56b5b52d6ad6b5ad6f4ad6f5a5ed5ad6b3b5ab6b52b6b5ef5b56f7b56f4ad6b4a52b5ad294ad6b5ad2b59dad5b5ab5b5695a56b5a5295ad294ad294ad294ad694a5295ad694a56b5ad2b5a5294a4e73ad6b5b56b39d294a5ab5ad6759d6b5ada939d6b4a52b6a4e729ce949ce749ce739d27394e53952948ca5184631, rootWithGate 0 6 255 true⟩,
  ⟨0x56b5c5296ad6b5ad6f5ad2f5a5ef5a56f3b5ad5b5294a56b5b5af6b56f5ad2b5a5695a5274a5695ad6959dad6ada94a56b6ad695ad2b4ad2b4a4e93a5695a56959d274ad2b4ad2b4a56b4a4e95aca73a5ab4b56d3a5674a5695b5696956b4a5a94a56b59ceb5a4e9294e94a4e549d2729d2939d23394e748ca5284231, rootWithGate 0 7 255 true⟩,
  ⟨0x5e75c52d69def7bdeb39ceb3adaf5ad6f4adad6b4ed5b5ef6b5af7aceb39ce739ce739d6b5ad6b5b5ad69d2b5ad6b6adad69ce739ce739ce739d6b5ace739ce73ad6b49ce739ce75a52b5ad6b6b5293b5694aceb39ce7395673b5a959d695a56b49dab4a4e95a52b3a52939ca538d2739ce949ce538d2739465284630, rootWithGate 1 2 255 true⟩,
  ⟨0x5e94c52d6ad6f7bdeb4a52d4a56d4a52f4a52d6b52d4a5ef6a5af7bceb5ad6b4a5294a5294a5294a5ad6a5296b5a94a52d49ce73ad6b5ad294a5294a4e739ceb59ce739ce739ce739d6949ce76b5294b5273a4e9294e5295273a52548ce739d2b4a5ad5a52b69cab3a52b2946328ca318ca949d253952949421284631, rootWithGate 1 3 255 false⟩,
  ⟨0x5e73c52d6adaf7bdeb39ceb39d6b39cef4ad6d6b52d5adef6adaf7bd2d5ad6b39ce739ce739ce75adad6a56b6b5ab5a56d5a5294ad6b5ace739ce739d294a52b5a52939ce94a5294a56b5a5296b5294b5273a4eb39d2739d694ad67595294a56b4a5ad5a52b6a4eb3a52b29ca5394e5294e949d253952949463284631, rootWithGate 1 3 255 true⟩,
  ⟨0x5e75c52d4adef7bdab39ceb3adaf5ad2f4adad6ad2d5b5ed4a52b5bd2f5ad6939ce739d6b4ad295b5ad5a56d6b56b6ad294a5293ad695a4e739d694a5293a4eb4ad294a52949d274ad2b5ad696ad274ad694a52b3952729d293b5a769d2b4ad6b3a56d49d295a52b3a4eb39ca5295273952949525294e939465284611, rootWithGate 1 5 255 true⟩,
  ⟨0x5e95bd2d6adeb7bded3a52d4ad6b5ad6d4a5a96b52d4b5ef6b52f7bcef3ad6b39ce94a56b5ad6b4b52d6a52d4b5a96a5a949ce739ce75ace73a56b5ace739ce73ad6b39ce739ce75ace94ad6b4a5294b5273a4e9294e5295273a52549d6b5ada7295293a52b69d273a52b2946328ca739d2528ca53952949425084631, rootWithGate 1 6 255 false⟩,
  ⟨0x5e75b52d6aded7bdeb39ceb3adad5ad6b4adab6b52d5b5ef6b56f7bd2f4ad6b39ce739d6b5ad6b5b56d6a56d5b5ab6adab59d294a5295ace739d6b5ace73a5294ad6b4a52739d295ad2b5ad6b5ad294b5294ad29294e739d694ad6759d6b5ada939d6b4a52b6a5293a52b394a5394e739d27394e53952949465184631, rootWithGate 1 6 255 true⟩,
  ⟨0x5e75c5296adef7b5eb39ceb3adaf5a56f4adad5b5294a56b6b5af6bd2f5ad2b39ce739d695a5695b5ab6a56d6ada94a5ad6a5274ad2b4ace739d2b4a52749d295a5693a4e93a4e94a56b4ad2b6b4e94ad693ad2b29d2539d274b5696956b4a5a94a56b59ceb5a52b39d2b39ca33952729d2939d23394e749465284231, rootWithGate 1 7 255 true⟩,
  ⟨0x5eb3c52d69daf7bded5ad6f49d6b39cef4b56d6b4ed6adef6adaf7aceb39ce75ad2b4a4e739ce76adad69d695ad6d5ad6d59ce739ce739d694a4e739ce739ce73a52949ce94a52949d2d6a5296b5293b5694aced4a52949da94ad674952749d2b49dab4a4e95aceb3a5293a4e7494e5294a949ce538d27394a3284630, rootWithGate 2 3 255 true⟩,
  ⟨0x5eb5c52d49def7bdaf5ad6d4adef5ad2f4b5ad6aced6b5ed4a52b5aceb39ce75ad2b4a56b4ad296b5ad59d6b5ad2d6b52949ce739ce739d694a5694a4e739ce73ad295a52949d274a4ed6ad696ad273adab5ad2d49d2939d693b5a759d294a52b39d6b39ce74ad2b3a4e94a4e739527394e9494e528ce7294a5284610, rootWithGate 2 5 255 true⟩,
  ⟨0x5eb5b52d69ded7bdef4ad6f4aded5ad6b4b5ab6b4ed6b5ef6b56f7aceb39ce74a4eb4a56b5ad6b6b56d69d6b4ad6d6b5ab59ce739ce739d273a56b5ace739ce73ad6b5a52739d295a4ed6ad6b5ad293b56b5b52b39ce949da94ad6749d695a569395693a4e95ad293a52949ce7494e739ce7394a538d27394a5184630, rootWithGate 2 6 255 true⟩,
  ⟨0x5eb5c52969def7b5ef5ad2f4adef5a56f4b5ad5b4e94a56b6b5af6aceb39ce75a52949d695a5696b5ab69d6b5a5694a5ad69ce739ce739d2939d2b4a4e739ce73a5694a4e93a4e949d2d5ad2b6b4e93adab4b52d3a52749d674b5695956949d6949d6949ca94ad2b39d294a4e54952729ce939ce338ce5394a5284230, rootWithGate 2 7 255 true⟩,
  ⟨0x5eb3c52d4adaf7bdad5ad6d59d6b39cef4b56d6ad2d6aded4a52b5bd6d5ad695ad6b5ace739ce76adad5a5ab6b56d5ad294ad6b4ad695a56b5ace739d6b4ad2b4a4e74a52b5a5693a52d6a5276ad274ad694a52d49d693a56b4ad65594e93a52b3a56d49d295aceb3a4eb3a4e739ce528ce949525294e9394a3284611, rootWithGate 3 5 255 true⟩,
  ⟨0x5eb4bd2d6ad6b7bdeb3ad6f5a5ab4a52d4b5296b52d6a5ef6a52f7bd6b3ad6b39ceb5ad294a5296a52d6a5a94b5ad4a52949d6b59ce75ace73ad294a4e73ad6739ce739ce739d6b39ced69ce74a5294b5273a4e9294e94a5ab5a52548ce739d27295293a52b6aca73a52b294e749ca318ca528ca539529494a1084631, rootWithGate 3 6 255 false⟩,
  ⟨0x5eb3b52d6adad7bded4ad6f59d6b39ceb4b56b6b52d6adef6ad6f7bd6d4ad6b4a52b5ace739ce76ad6d6a5ab5b5ad5ad6b4a56b5a5295ad294ace739d294ad694a5294a5294a56b4a52d6a5295ad294b5294ad2b39d294a5ab5a525495294a56939d6b4a52b6ace93a52b39ce749ca5294e7394e539529494a3184631, rootWithGate 3 6 255 true⟩,
  ⟨0x5eb3c5296adaf7b5ed5ad2f59d6b39cef4b56d5b5294a56b6adaf6bd6d5ad2b5a5695a4e739ce76adab6a5ab6ada94a56d5ad695ad2b4ad2b4a4e739d695a56959d273a4eb4ad2b39d6d5a4e96b4e94ad693ad2d3a5674a5695ad2758d2939d694a56b59ceb5aceb39d2b3a4e549ce5194e939d23394e7494a3284231, rootWithGate 3 7 255 true⟩,
  ⟨0x5eb5b4ed6aded7bdef4ad6f5aded5ad6d3ad6b5aced6b5ef6b56f7bd6f4ad6b4a52b5ad6b5ad6b5ad6b59d6b5ad6d6b5ab5a56b5a5295ad294ad6b5ad294ad694ad6b5ad694a56b5ad2d6ad6b5ad294b56b5b56b39d294a5ab5ad6759d6b5ada939d6b4a52b6ad293a52b49ce749ce739d27394e539529494a5184631, rootWithGate 4 6 239 true⟩,
  ⟨0x5eb5b52d4aded7bdaf4ad6d5aded5ad2b4b5ab6ad2d6b5ed4a52b5bd6f4ad694a52b5ad6b4ad296b56d5a5ad5b56d6b5294a56b4a5275a5294ad694a5293ad293ad295ad6949d694aced6ad695a5274ad6b5ad6b395293a56b4ad6559d2b4ad6929d2b39d295ad293a4eb49ce739ce73952738ce5294e9394a5184611, rootWithGate 5 6 255 true⟩,
  ⟨0x5eb5c5294adef7b5af5ad2d5adef5a52f4b5ad5ad294a56b4a52b5bd6f5ad295a5695a5694a5276b5ab5a5ad6ad694a5294ad694ad294a52b4a52939d694a5294a5274ad2b4a5293a52d5ad296ace74a5ab4ad6d39d673a5294b5676952b3a5693a52b494e94ad2b39ceb4a4e539d272952939523294a7394a5284211, rootWithGate 5 7 255 true⟩,
  ⟨0x5eb5b5296aded7b5ef4ad2f5aded5a56b4b5ab5b5294a56b6b56f6bd6f4ad2b49d295a5695a5696b56b6a5ad5ada94a5ab5a5695a4e94ace93a52b4a5274a5674a5694ad293a52b4a52d5ad2b5ace94ad6b4b56b29d274a5695ad275956b4a5a739d2949ceb5ad2939d2b49ce549ce729d27294e3394e7494a5184231, rootWithGate 6 7 255 true⟩]

def firstCount : ℕ := 28

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def decodeStep (width : ℕ) (parent : ℕ → SearchState) (entry : ℕ) : SearchState :=
  let before := parent (entry % 2 ^ width)
  let left := (entry >>> width) % 16
  let right := (entry >>> (width + 4)) % 16
  let dropLeft := if entry.testBit (width + 8) then 2 ^ left else 0
  let dropRight := if entry.testBit (width + 9) then 2 ^ right else 0
  let kept := 2 ^ before.2.length - 1 - dropLeft - dropRight
  secondTransition before left right kept (entry.testBit (width + 10))


def secondCount : ℕ := 317

def secondCodes : List ℕ := [0x90814722ebaa11d83b0eb44226210521c0ae884644eba9f1d018e4548416210b1cc690824311a390714cd88424620639131d978ec5842203a191c828e88d75523a0f20c0, 0xe847635643055c41ae467751e3b261c858e8007212421718c89023c510e3a8d5d45eea94861388015d4490ea7312a32b10c8dae82473224213188a90c858104210f210e, 0x8e87c43303a2321c590c5d755eb11721c4d0e7d752ebb23618c90674730643b318c790465742e3a2920c590e84721a40821c82aea4c8626ba9d1cc790625750b419f218e, 0xe601c753631131c8c8c414872ec08919088eac5630a3a0b1883b040c74123981a1978ecb4832eb99314460e80c6212439d5cc290e4c7442c38f21c28c60c7106399b58d0, 0xd0c9d8646319f2044cc82c821eb9032116ae22c742c21051d988ec44641c210b10c88e67c8430188d188b8e4687402baa71d8a8e84c520e3a1d1912ce83c740bb09b18c0, 0xd0e9c42223b0320ccaec2c6402399d1c458860d755a290d18c490cb47112a1034c418ec3d753343b51c888644473164103590490214431e39881d0f8ec95710a408b1901, 0xb0ca4643e42231d80d0844841e319761ce8843c875b31991c818640c43021883218a90e60742638875d4aa861484483a051ccb8c20c744e319d1c878643c41043a0b1c42, 0x9042c8556321d19029042452363b1f0843ac224861e30875d51aea3c531a3209a1888867d841243951d0cb045c864a42035d528c884420721961c888ca1c822b3b2d5d48, 0x8c224742243a321c78867484523217610bd0e44830631112089b068482383a2710c58ec24820a190d10c490e94831fb00d2181908056206388d5d41b0c2c764232135c89, 0x160c990885763221961843b06157452390b08468c43c744a190b1d43ce674610a43830c84ac81c721220851d89aea04822e43011d8ecec3c760ab9a31ccc]

noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := secondCodes.getD (i / 32) 0
  decodeStep 6 firstAt ((block >>> (17 * (i % 32))) % 131072)

set_option maxRecDepth 100000 in
def secondSuccessorsList : List (List ℕ) := [
  [0, 24, 45, 55, 113, 128, 138, 186, 210, 220, 263, 293, 295],
  [10, 20, 34, 45, 60, 73, 82, 98, 99, 107, 115, 153, 160, 169, 176, 177, 183, 189, 194, 199, 209, 211, 212, 230, 233, 260, 262, 264, 278, 301],
  [4, 25, 31, 61, 66, 72, 100, 104, 118, 123, 130, 149, 162, 167, 176, 192, 201, 203, 209, 252, 270, 290, 297, 302, 311],
  [13, 28, 50, 116, 127, 134, 205, 227, 245, 248, 299, 304, 312],
  [11, 15, 39, 44, 46, 54, 67, 88, 106, 114, 121, 127, 156, 165, 168, 178, 180, 194, 238, 241, 247, 251, 268, 271, 287, 297, 298, 300],
  [17, 18, 48, 56, 76, 92, 117, 145, 151, 155, 161, 170, 184, 187, 193, 199, 247, 255, 259, 272, 287, 302, 305, 309],
  [14, 16, 49, 74, 108, 141, 181, 242, 261, 265, 269, 308],
  [1, 33, 51, 58, 60, 68, 80, 98, 101, 131, 146, 151, 154, 162, 166, 175, 178, 184, 192, 195, 196, 215, 218, 243, 246, 265, 266, 284, 291, 307],
  [6, 34, 38, 51, 52, 63, 73, 120, 121, 144, 147, 156, 161, 167, 171, 172, 190, 219, 224, 228, 240, 277, 279, 286],
  [9, 26, 37, 70, 71, 103, 109, 125, 135, 171, 195, 206, 211, 248, 256, 257, 276, 296, 300, 305, 308, 316],
  [6, 19, 33, 36, 42, 136, 141, 145, 149, 204, 208, 226, 237],
  [7, 11, 14, 17, 25, 26, 30, 42, 53, 78, 86, 89, 91, 110, 122, 140, 150, 177, 190, 200, 215, 217, 229, 230, 235, 280, 281, 294, 313],
  [5, 10, 50, 59, 79, 84, 89, 94, 106, 108, 123, 124, 125, 140, 142, 174, 188, 207, 213, 236, 262, 277, 288, 307, 314],
  [12, 40, 54, 56, 72, 97, 126, 129, 139, 228, 250, 312],
  [4, 9, 30, 32, 59, 64, 69, 83, 105, 124, 129, 133, 153, 172, 185, 196, 197, 212, 216, 245, 253, 256, 274, 283, 292, 298, 303, 309],
  [21, 65, 79, 87, 95, 115, 143, 154, 157, 164, 169, 205, 222, 235, 239, 249, 251, 255, 261, 270, 274, 276, 294],
  [23, 29, 35, 40, 75, 94, 96, 102, 144, 166, 183, 203, 210, 229, 231, 239, 258, 268, 269, 272, 275, 283, 313, 315],
  [3, 36, 52, 80, 85, 93, 96, 99, 118, 128, 134, 157, 158, 180, 181, 197, 213, 217, 221, 244, 250, 285, 289],
  [19, 38, 47, 68, 82, 104, 109, 113, 116, 132, 143, 163, 165, 170, 185, 200, 202, 232, 234, 267, 288, 289, 303, 306],
  [0, 13, 22, 57, 65, 67, 74, 76, 83, 110, 137, 139, 159, 188, 191, 198, 226, 266, 273, 275, 278, 311, 316],
  [2, 12, 22, 43, 77, 120, 132, 146, 155, 160, 168, 186, 222, 223, 231, 241, 242, 252, 253, 257, 281, 282, 310],
  [5, 62, 63, 93, 107, 138, 164, 193, 201, 206, 254, 273],
  [1, 3, 20, 23, 27, 39, 55, 62, 77, 78, 95, 102, 111, 114, 117, 130, 131, 133, 135, 150, 152, 179, 182, 198, 214, 225, 236, 286, 306, 310],
  [8, 15, 16, 18, 31, 32, 37, 53, 90, 97, 112, 142, 152, 202, 218, 219, 221, 233, 238, 263, 280, 282, 315],
  [2, 21, 29, 41, 44, 47, 48, 58, 66, 69, 71, 86, 90, 119, 137, 148, 174, 182, 204, 224, 232, 243, 244, 260, 295, 299],
  [7, 8, 41, 57, 81, 85, 111, 136, 147, 163, 175, 187, 189, 220, 225, 227, 249, 258, 271, 290, 291, 292, 296, 314],
  [35, 46, 49, 61, 64, 70, 84, 91, 112, 119, 126, 158, 159, 173, 179, 208, 223, 234, 240, 246, 254, 259, 264, 293, 304],
  [24, 27, 28, 43, 75, 81, 87, 88, 92, 100, 101, 103, 105, 122, 148, 173, 191, 207, 214, 216, 237, 267, 279, 284, 285, 301]]

def secondSuccessors (i : ℕ) : List ℕ := secondSuccessorsList.getD i []


def thirdCount : ℕ := 1894

def thirdCodes : List ℕ := [0xb08509093390ec2f2ebcf30f69286ab0c75b0c7b90e5690897d303d90e55d284f10b15aea79906a7ee80590a3490c7488497aeb2cb0c7890a33b0a8490935d303990e5990ebef0d33aeb2a8a8c7926d1, 0xb2ed9aeb39d3043aa6d3d3049b0c808e92690899d304090ec3cea118e649aed21cc659926d790ec6b0f20e612bb06e68e4b0ac64890e60b0c7daa6d1d3046906ab8c87fce84f90ec0b28b7b0f1f8c8e4, 0x930638ca81b0a90d0e5faea869306292e878a8d48c8ebd304c886b292aa0b0c84f0c018eccb90eca8e92ab0c828eae690a41d2e6e90e83906b290ec89305e0e47992e82d08c4b2ae68e83c90a9b8e83b, 0x92aa590e688a6a7ca9268a8d790ed190a4cb0f319080bb086393066b28c3b0f358eccdf0eb8d2a90b0f2e886b8d0e62b311b90a4390a49908a292e85b0a8cb28c0b0c87b0a92906b80a27f90606884a2, 0xb0c91b0c900e937aa92ed08d492aaab3124b2ee790ed790e6d8c47fb0c8fb0c8e8a6ab10b2e8eaef90811b2af190ed3d0e549306ad3053d304fb0c8cae4f8f310a92aa6aea0b906beaa929f0c13b0f33, 0x906c3d2a9cb28d1b0aa0906c790a5390a4f884b08ece0d0b0ab312a8e606886e4f31128c4810e93c0a633886c2906c090a5290a50b0a9c10b31ce86a908b1d0e66d305bb0c92d0c79906c290edb90eda, 0x8a8e69307590e749307bd0673b0c968c60e8e622e8406f0c2192ab2aa804d2aa18e80bb0c958a6b2b28d3b0f36b3135b08f78e662b28d28e859cc66c886c793072aea9b908b0b3132d305fb0e03b2eec, 0x90ee690621d0e72b0aa692ab992ab88e860b0c9db0c9c90a5eb0cf2b0aa5f0c26b0c9a8ece5886eb8c9058a6b8b2ef192e9592ab7aea99b0c98908b58eafbb0e0ab3133f2edd8c900aea9792ab490e76, 0xcc8388a6c0b30038ecebd306ef311eb30018a709d0c8bce87caeaa2b0cf48ca7fb087d8eb0a9269190ca2906d1aec9bb0e12b0ca190a631069c904f7b0ca090a62d0c8990ee9b0e11904f5b087b90c99, 0x8eb12b0ca5b2efc9308492ac5b3009d2e9092ea68e868b24628a6c38eb0e8a6c293082d2aac92ac492ea5ae8b1b2b0c8e81e8c42db2609c860ed2aa792ac0b0cfab0cf7906d7ca80bb08808c42ab3004, 0xb0caab071590697b0ab4b0ca9d0e85b2f018a6c790a6e8e86daeaa8b0ab290eefb08e58eb148eceed0e8293087f0c3390a6af0804b0ca7b0ca6d2aab92ac3ca811b260b90e8692ac2ee83f106a18c622, 0x908cbd3078106a78eb1690cb190cb0b0e17b0e24aa81992ac8d0e77ac4b0b0cac8c30990833b040eae686d0e73b2efd8e632b0d068c913d0e87886f7b0ab7f08098e621b261190699b260a92ac7b0cab, 0x92ad48827fb0abe930928eb1bf0c44930918e8738870692ad18a42dd2e9c92eb2b0aba8a6d18a42a8a8fbd2e98eea3c8e63ce8421b3014ca81ecea4cac836aeab1aeab0b2b198ecf80e82290a718c479, 0xb06f8aea4390ad58ed00b0cba90e97b261e90a7b93096b0cb8b0ac2ce88cb2619d2abe92eb9b0cb7b2f10ce6f592ad3b301e865098a8ff90efbb2b1fb0cb4d0e7992eb78e63bd0b3390cb68e876b0cb2, 0x90e9b8c63c8eb2f8eb29b0cbed2ea7b0e348ed04b0cbc930a090e9990a80b2f19b072cb2b2990f078eb26aec32f0eec8c63692ad9b30218e8790c62dae6be9084990a7d92ad7aec308e833b0e27b261a, 0xd289a92ec4b0cc392ec0b0cc2b0ac88c934b2b2ab2f1fb0733f0c52ae890d0e9a90f0c8eb2c9271fd2eabf0c5092ec2b0731d0e98906b1b2b2cb069590f0aae8cbb0cc08eb2aae6c2d0e96d2eacd0e89, 0x90ccb8e849b0ad2d308fb0cc88e4f790f14928b8ceca2ae529b2b398ed138c93cb0700d3090930a6b0cc7b0cc6b0cc58a91592ec38e4f8aec3b90f0eb0d2190ea2b2f2010a34928b2ee85db089d8c937, 0xd309390f16b0cd1b0ade90cccae695d0912d0ea6930aaee86b9272e8ea0010a4190eae9272c90ea8aeacd92cc990a8f92aec92ec8b0e4c864f7aeacbb0cca90a8c9272a8e659930a5ae6a29272992ae6, 0xb2f2eae6d3b043cd309aa8648d28a992ed410a49f2f15b2f338e69c10a4cb0cd392ed192733b0ad9b060ab070d92731b0cd2b08a7b0e3cb0ad78ea04ae6d18ed18b290c90eb192ccef0c62b3037f28ef, 0xb0e45d30a1928c7b3044b0cd7eea68b0e5090f1e928c4b2f31930b7d2ebeb080eb0e4f84309aecd592ed3b2a0bb0e3bb0cd490eb0b0d36ae6d7b2f3590862d309db2910d309c928c2b08ab8ea0992735, 0xaec59d08e4930b8b0ae78a935d0eb2884f7b0c0290a9d90f29ae8a6b0cdeeea6d90a9a92ed7b0cddb08b48e899ae6b0d0e9e930b4b0cdbb0cdaac6a290f26b2a118e8978c4a2b0cd9930b28a92af2f1a, 0xb2e0a9260bb304d908fab0ce2ae422f0c71ae8ebb061a8e8a2f3033b2e0390f2a9071590ebbb0ae6d0eb98ea9bae8a78e6a78a933930bdaec6090aa0d2ec69086a90f2ccecb6b291b930ba908f7b2c05, 0xb2e1190aa5b0e63b3050eea748c82290f39c86598ea1ad30ac92611b2a1992ee692afd909068ed37d30a7930c0aeae5d092a92afc8ea1eae6e6b0c0cb0e4e8e862d2eca909008ea19b0e5ed30a98e6ab, 0x90ce890aab90aaa86309ae8b7b08c090aa9b29298e673b0af19071fb2a1a928d7f290ed0a33b0ce9ac6b0d09358c4b08ed3cd30ab930c390aa7930c2b0ce7b0aef90ce590aa690f3b92b01b0ce6b2a1e, 0x8e8b18e8b0b293190ecbf3040d0ec308497b0e6ad0ec68e679926198a80aee88ab0cecd30b390e06d0ec4b292e90aac10a63aeaeb8ea26b08c3b292cd0ec08e6b2b08c5f2914ee4e48c709930c78871f, 0xd06cd90cf58e6be90ab78ea33f0a929072990ab4ae432d2ee2b3062b0cf190ab2b2939d0ce090e0f930d18c673f0c84d0a448ec0db0cefaeaeeb266290e0bae8f78a47f8a62db0734ce83cd2edaac879, 0xb24b2aec76b08d3d0ce4b0e75b0e7b8ec158e6c3b28048e6c2b0afdae8d5b0836aeaf8ae43cb306690ed5b0afc9072e90cf8b08d1b0afb9072c90cf3aeaf5ae8c090ab88e6c0a8422d30bed30bcb2e24, 0xb0b0c0e4f78847fd0edaf2e12b0cfccc897d30c6b24b8b0cfbd2ee9d0ed7f0c8f90e148c83c90abcb0e7d88622b2809aeaf7f305392b1b930d98c6790e8738ec17b0b0190731f0f33930d7084a28a81e, 0x90e208ea44f2e168a481906918ea438ea49b0649b0b109043290ac090e1f8ea41b0c30909218ec1db0d01aeb00b0cffaa87b90ac292b2090e190a6a70e876b306fb08d990d00d0a50b0cfdb0e80f0c92, 0xd0cee92b2aaec868ec27906f592b29ae8d290ee590e269060bd30d08c84890ac38a729930e790e2590d04ae8d1b0d0790ac78e6d190ac5b30728cb09ceaa18ec2290e1a8c84af305fb0c32aeb06f0e03, 0x8a833b2a4db267cf0aa692b3590b2f930ecb281992b2e8ca2ab0b19d2b15f0c9a90611b0d0cb24c0d081e92b2cb0c388e8cb92b328a72eb24c2ae913b0d0aeea978e6978a72cb3075d0ecd8642d90ac8, 0x88638b0d14eeaa2b0e8c0a6b8b0b1b8ca2dd06ebaeb139089cb0b1f90934ceaaa9089a92b33a843cb0d108ec2cb0d0e8e699d0a62b281a92b31b307c88636ee8a48e6d7b0c3b906f7b24c78a7319043c, 0x9061990ad98c509f0ca590ef5b3085b0d1990ad790e35b0859b3082aa64990ad38863c8ea53e628d9070690e33b0e918ead5d0ee0908a190ad48ea52d0edfb0e8eb0d15930f1aea9c90ad1cece8d30de, 0x8a849b0d1fb0d1e92f1bac8e58e422b0b26ca88cf0caa8e89cb2e4db24d10a6c090ef490ade8863baeb18f0ab292a04d30e290ef892a03b3087b0d16b0d1be8491ec8f7b0d1ab0628d2b1e92a01f0ca6, 0xb0d26b0e9d8e6b190d27e8495cecf3b0b2c8ec4290e41f2e34b2e50aec971071f92a0aaeb21b0d208e89ab0b2aae6f8ceab8aeaa58ec3c908ac8c699d2f07b0b298642290ef78ea62b066292a09d2f0a, 0x8ea6e90f2fae700ee8c1b0d2c92f2992a149310293101d2d11b066ab04c790ae6ce63bb0ea1b2a66f0cb2930fd90f06d0eebb309290e43b0d2990e49b0c59930fcb0b39b268c8ec47b04c2d30ea90f00, 0x8c86daeab292a19d2f16906339310c90d34b0d31a86a2b0c60d30efb2e5e92f2c8eb2b92f32ae8efb0e97b0d2a8a84fb2a6a908b2b2c5db3096d0705f0cb9f0cb88c868d28fb92f2ab0d2ed0d1390f04, 0x8c6b1aecae90e5293110b0e99b0d398e432aa662b2e638ea71aeb37aeb3688633b0d358e8a988422908b8ceac7f2e4c9291fd0d1892a1e8c4f8cc706926628e8acb0d33d28ff107298ec4e8e8eb88659, 0xb0ea29266a8643cec338b0c04aa8a7b067df0cc08a86292e0410aa7908beee8c9b090e8e43c9310fb0c00b04d1d2f1ed30f9b067b90aefb2a728c873d0f0ab0648aeb3cb0eaab0d3bb0a0bd30f61072e, 0x93119ce915d30ffb0c0a8e62df0cc88c879aeac29292a90649a86b090e5fb0c03d2912b0c098ec5af0cc3b0a11ae60b908c28e8b2eeb1f92e0910aab92e01d30fb8ec56ee8ceb0914b2e6ab0c06f0cc4, 0xf0ad7b0c12b0a19b30afd0f039311fd0a92b0c1190afcd3108ae90c90afb8a86ab0a168a30992935b0eb8ac40eb0c0f90e620e8b0929338e8f7b30a688649f0ccab0c6caea0d908c7b0c0bc86b1b0eb4, 0x8e8c292e148843caea17b0c16d0d378e8c4b0ebc908368e90692e1390c17f309aac70d93122b0a1ab04b0b0c76b0c148a68190f218e8beae90e90b018e900d310a90aff8e6cd9267bb0a1e8a633b0c13, 0x92e19d2e00b2e7d8c27fb068cd2a26f0cda8867390b0ace8979312ad0f13b30b28ec68ae619b30b993129b2e7cf0cd790838b285ed0d3cf0e5090e6ed310ed2f3bd0f1eb2e75b2e7bd08229083c93128, 0xaa8c092a4492e1ad2e0692e21b0c1fb092990f3693135b0ec7b2e80b0c1eb30b8b0ec58c88bb2a8c908d79280b9312eb0c19ac4228ec6dae61ad3115d292692e1e9312c9083bd0a9a8ed2bb0eb6d3114, 0xd0f3290c28aea2790b14f0879ce8a28ec73b0c26b0c86b092ed311690c278c6cd908488a649b2e848e913b0c25b092cae91b9313392811b0c248ea8f90c1d93131aea22b0c1ab0c2190b0eb0c20ca8be, 0xf2e78d312593003b2a9690e02d311e90b16d2a34b30c3d0aa6ce933d2a33b30c593007b26c2f30acb30c4e62ccb30c0d0c10886628ea2ab0931d2e0f8e8d490f3a10ac7d0c0d9313990b159066288679, 0xee85eb0804b0ed98e72c8e921aea3290b20b2e92f30b3b2e91aa8d18ea9a92a5290b1b92a509066a8c899f08c590c2cae92910ad18e729ac82d8ec2f864818e8d78ec798a87fd3126b2e8cb26c78ea2d, 0xd0ab2ac43c90b298c8a29086093011cc8f7d2e25b251fb0a4390e87d0f30b0c37ae939d0c220ead590b26b08098e6eb9085906309b0c35d2e1fb0eddd087cb0c34d0e01926219300b90e82b0c3390c36, 0x8ec3ad0ab9d0ab8b287d90c42ee436b26d4aea3c92a5e8c6e4b0c97b2aa5930148ea3eaea3bca8d790b2cce80ab26d1904978e42ad0f37d2a4990c3c8a88cd2e208eaa68ec8990e17b287bb30d48eaa5, 0xb2ea0cec17b30d790b2e8eaa98e42df0e7593019d30008c6eb90b33ee438b252992a6390c478eaacae649b26d792a628eaa78e8e6b0c43b26d3d0f3c90b2a8a662b0c4190c45ceaffae804d2e26b06ab, 0x8eab290868b0c4c90e2790636b08b18e479f2a9c8a27fb081990e1d8e93cf30c690e8f90c48b0eec90b318869790632904a2d0e14d30068c8b1ae4b08e6f7b0c498e93790e908eaab92e4490b358e6f5, 0xaeafbd0e21d2e338eab9d0ac4b2ab48e706ca8e6ceb10aea4e90a049086d8a89a9086c90638b2ab2d0ac0d0e0d8eab788699f2e8e908fb92a6a90c4eee448b081a90a008e60b864798427f8c8b0ae859, 0xb0caeee87b92e52c86ebb051fb0c538ec2df0d0a90a0a8ec2a90e9cb26e6ee911cec27b0c52b062490e9ab2eaaae860b0c509063cb0a5e90a098ec999063bd0ac3908ff92a71d2e35b0ca88c6f5b0c4f, 0x8e8fb884798eac0ceb1f90e320a72e8c422d3016926b2b06c38eac2b06c290e30d2e439087692a7bce699a84b0d2c3f8eca290c56aecf7ae819aeb0c8e619904b0b30ecaea5990e2cb0ee8d0e15aecf4, 0xb2ebaac628b0c62d0e33f2ea1b2eb8886b1b0a6ed0c4a92a8092a7c90ea68eac3926b8d2e4992e62b0a6ab06c790a1690ea5b0cb58a8a9b2ac2aea60b2695b0c5fb0c5e8eac4b2eb4ae66292a7d8a8ac, 0x8eac890e47b052eb0c6690a1990e3baed0690eacea819b2ac88a509ae4c28a8b2cc63290ea7d3026b0ef38c8cbd0e3790a8390e42b0834b0eff90915b0ef5b0529d0ad790ea9d3023b0c63d0e2290e3c, 0x926c2b2cc1eec97b0c6ab06d392a87eeb219069cf0d2010aff8649792c6bcec3cd08ac8e82290a1a8ecb18ecb090659aea6892a858a8b8926c092a84b06a20e906b06d190eab8e49792a828c68190a1e, 0xb0f10ceb31886a18e4a2b2ec7d0c5ab2ec590eb78ead3926c7d302e90c6db28a6ceb35b0f00b0a78906a1cc63baa6c2ceb2e8ead4d2e5390eb28869c8ead1b0c6ed0e449091faea6d90a2690c68926c3, 0xaea74f0d32aeb298a8c4aea7392a92ae4d18c62d9092a8c43cb0f158ead790e4eb2ad9ae879aa90e8a8c2b0c72ee700d3034f2abeb2ad7b0c7192a8cd303392862aa4d1d2a78aa6c792e718e633b30fd, 0xcec4e93050d0879aea76b06b0d0c61]

noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdCodes.getD (i / 32) 0
  decodeStep 9 secondAt ((block >>> (20 * (i % 32))) % 1048576)

set_option maxRecDepth 100000 in
def thirdSuccessorsList : List (List ℕ) := [
  [202, 564, 1231, 1374, 1591, 1594, 1637],
  [9, 66, 82, 100, 171, 252, 262, 281, 340, 585, 645, 658, 694, 740, 812, 819, 837, 917, 947, 1048, 1057, 1255, 1367, 1509, 1589, 1659],
  [10, 83, 164, 263, 269, 341, 443, 660, 664, 743, 813, 820, 890, 896, 898, 911, 1049, 1060, 1204, 1339, 1467],
  [14, 171, 193, 249, 266, 285, 348, 417, 468, 514, 592, 663, 692, 824, 899, 928, 938, 1036, 1054, 1066, 1267, 1469, 1499, 1677],
  [16, 44, 173, 212, 270, 288, 331, 584, 825, 845, 855, 1055, 1069, 1227, 1238, 1243, 1502, 1570, 1608, 1639, 1653, 1797, 1852],
  [15, 18, 672, 1520, 1798],
  [97, 175, 180, 215, 784, 904, 1249, 1404, 1610],
  [4, 72, 151, 241, 255, 259, 284, 482, 582, 647, 671, 729, 807, 884, 905, 933, 982, 1020, 1047, 1186, 1253, 1352, 1458, 1501, 1807, 1893],
  [80, 160, 161, 260, 268, 336, 464, 491, 582, 739, 816, 892, 916, 927, 944, 1030, 1047, 1264, 1512],
  [38, 191, 298, 314, 358, 522, 609, 695, 841, 868, 877, 1089, 1241, 1257, 1265, 1518, 1673, 1819],
  [52, 203, 230, 354, 591, 606, 703, 713, 749, 788, 854, 939, 1106, 1276, 1550, 1687, 1721, 1878],
  [119, 132, 208, 210, 291, 307, 325, 622, 665, 702, 807, 946, 950, 964, 1218, 1261, 1282, 1390, 1507, 1636, 1726, 1837],
  [32, 287, 391, 712, 948, 1324, 1393],
  [149, 447, 811, 831, 955, 1284, 1444, 1613, 1646],
  [217, 297, 368, 627, 764, 1040, 1294],
  [127, 142, 190, 213, 225, 301, 323, 622, 673, 816, 954, 958, 974, 1225, 1293, 1335, 1448, 1641, 1891],
  [232, 627, 770, 1012, 1452, 1650],
  [12, 53, 143, 238, 259, 326, 344, 356, 646, 665, 725, 735, 970, 978, 993, 1062, 1262, 1304, 1418, 1530, 1859],
  [22, 65, 154, 204, 211, 250, 268, 353, 424, 646, 673, 891, 983, 987, 1001, 1310, 1356],
  [97, 129, 254, 289, 488, 923, 1312, 1333, 1680],
  [66, 106, 172, 188, 262, 266, 302, 359, 394, 408, 437, 566, 654, 680, 688, 761, 798, 799, 802, 828, 882, 907, 940, 1003, 1026, 1033, 1043, 1139, 1145, 1325, 1334, 1342, 1465, 1555, 1611, 1687, 1809, 1880],
  [148, 242, 248, 347, 559, 660, 779, 810, 857, 883, 886, 909, 979, 1005, 1022, 1119, 1573, 1664, 1697, 1734, 1883],
  [273, 362, 380, 392, 446, 512, 531, 564, 915, 922, 925, 932, 1041, 1151, 1298, 1339, 1393, 1720, 1741],
  [93, 252, 359, 377, 486, 541, 742, 870, 919, 968, 988, 1018, 1332, 1340, 1539, 1598, 1674, 1677],
  [577, 674, 1470, 1591, 1689],
  [40, 96, 125, 184, 286, 375, 401, 435, 707, 724, 789, 905, 946, 970, 984, 1055, 1115, 1181, 1309, 1361, 1375, 1388, 1592, 1622, 1703, 1705, 1710, 1783, 1787],
  [60, 146, 309, 448, 695, 727, 756, 933, 964, 993, 1002, 1328, 1385, 1405, 1412, 1638, 1808],
  [206, 282, 285, 377, 394, 449, 577, 701, 711, 848, 931, 937, 963, 1045, 1065, 1161, 1495, 1619, 1701],
  [221, 275, 324, 962, 1051, 1067, 1378, 1524, 1646, 1723, 1767],
  [158, 329, 432, 552, 588, 717, 743, 810, 912, 977, 1007, 1015, 1056, 1063, 1210, 1219, 1340, 1415, 1621, 1733, 1736, 1788],
  [45, 131, 292, 300, 393, 428, 441, 695, 714, 736, 864, 950, 975, 978, 1055, 1194, 1314, 1371, 1382, 1396, 1792],
  [105, 196, 295, 296, 383, 406, 465, 715, 724, 916, 954, 983, 1069, 1181, 1402, 1426, 1513, 1630, 1712, 1713, 1794],
  [56, 251, 304, 305, 315, 415, 504, 708, 722, 736, 874, 927, 958, 986, 987, 1069, 1089, 1194, 1380, 1409, 1542, 1749, 1793, 1803],
  [175, 214, 254, 357, 395, 458, 793, 865, 1019, 1075, 1403, 1411, 1508, 1515, 1662],
  [216, 320, 386, 698, 730, 835, 878, 934, 1082, 1093, 1200, 1346, 1387, 1413, 1521, 1721, 1761, 1809],
  [152, 312, 313, 421, 431, 543, 741, 1084, 1153, 1172, 1174, 1332, 1350, 1415, 1438, 1763],
  [180, 357, 376, 400, 570, 832, 1417, 1680],
  [327, 328, 429, 489, 708, 738, 756, 944, 974, 1001, 1012, 1089, 1422, 1528, 1652, 1729, 1818],
  [97, 216, 243, 369, 454, 587, 610, 778, 790, 951, 1014, 1034, 1097, 1236, 1370, 1432, 1569, 1768, 1770, 1776, 1810, 1826],
  [170, 244, 340, 348, 437, 449, 806, 842, 956, 1013, 1070, 1094, 1102, 1113, 1428, 1437, 1526, 1628, 1682, 1743, 1873],
  [179, 603, 999, 1023, 1059, 1438, 1479, 1758],
  [183, 451, 472, 676, 857, 912, 1006, 1025, 1112, 1114, 1123, 1214, 1253, 1264, 1540, 1696],
  [215, 289, 395, 400, 982, 1040, 1062, 1115, 1450, 1547, 1686],
  [206, 316, 382, 412, 470, 479, 560, 674, 701, 945, 1024, 1028, 1031, 1126, 1131, 1134, 1143, 1279, 1400, 1467, 1720, 1856],
  [17, 46, 247, 318, 341, 416, 423, 507, 809, 820, 876, 886, 977, 1006, 1052, 1086, 1129, 1135, 1147, 1166, 1282, 1293, 1437, 1485, 1578, 1699, 1820, 1870],
  [299, 405, 456, 804, 961, 1017, 1275, 1472, 1481, 1594, 1689, 1880],
  [37, 163, 237, 293, 303, 403, 404, 493, 503, 959, 1146, 1155, 1171, 1250, 1428, 1448, 1485, 1504, 1666, 1714, 1731, 1845],
  [129, 243, 501, 634, 659, 697, 731, 813, 883, 1052, 1079, 1274, 1286, 1480, 1815, 1817],
  [25, 159, 226, 267, 269, 351, 438, 451, 527, 876, 909, 914, 966, 1007, 1079, 1086, 1154, 1158, 1176, 1202, 1304, 1310, 1629, 1715],
  [245, 936, 1177, 1285, 1452, 1739, 1751],
  [364, 414, 462, 823, 918, 930, 1193, 1209, 1498, 1613, 1723, 1778],
  [9, 175, 310, 333, 369, 450, 693, 753, 827, 863, 887, 976, 991, 1038, 1179, 1203, 1313, 1460, 1505, 1661, 1756, 1857, 1863],
  [14, 180, 320, 450, 473, 500, 516, 542, 685, 872, 1078, 1110, 1190, 1278, 1322, 1464, 1510, 1558, 1770, 1868],
  [167, 374, 388, 434, 452, 459, 533, 544, 622, 1047, 1181, 1194, 1468, 1514, 1516, 1667, 1864],
  [70, 98, 265, 391, 460, 851, 894, 999, 1107, 1187, 1335, 1504, 1562, 1627],
  [385, 402, 468, 541, 577, 787, 1523, 1637, 1773, 1880],
  [287, 321, 894, 973, 1023, 1107, 1216, 1356, 1588, 1649],
  [6, 48, 487, 532, 554, 574, 720, 748, 791, 811, 1111, 1130, 1223, 1336, 1352, 1540],
  [3, 214, 333, 397, 494, 578, 896, 966, 979, 1021, 1056, 1135, 1158, 1240, 1263, 1357, 1369, 1567, 1688],
  [64, 350, 420, 502, 521, 621, 823, 996, 1072, 1138, 1141, 1227, 1380, 1553, 1671, 1786, 1838],
  [66, 396, 397, 478, 586, 605, 802, 849, 881, 992, 1008, 1042, 1098, 1233, 1245, 1341, 1345, 1534, 1544, 1560, 1675, 1760, 1811, 1878],
  [21, 69, 236, 271, 317, 378, 474, 508, 543, 558, 594, 607, 1146, 1238, 1326, 1338, 1347, 1375, 1513, 1563, 1617, 1825],
  [15, 322, 514, 566, 787, 998, 1148, 1235, 1252, 1554, 1683],
  [18, 322, 386, 516, 600, 1237, 1256, 1709],
  [55, 94, 104, 256, 365, 433, 481, 510, 601, 616, 795, 830, 900, 996, 1084, 1150, 1155, 1238, 1257, 1358, 1382, 1542, 1572, 1834, 1849],
  [19, 76, 219, 511, 563, 576, 602, 754, 772, 831, 915, 1016, 1111, 1156, 1160, 1188, 1266, 1383, 1573],
  [24, 78, 209, 277, 330, 389, 485, 552, 573, 634, 890, 1005, 1021, 1112, 1129, 1154, 1205, 1240, 1243, 1388, 1402, 1563, 1771, 1804, 1890],
  [26, 61, 107, 149, 446, 515, 581, 611, 760, 776, 922, 995, 1130, 1156, 1196, 1271, 1390, 1526, 1578, 1627, 1714],
  [30, 31, 68, 254, 369, 396, 410, 546, 615, 636, 762, 777, 812, 926, 965, 1010, 1163, 1199, 1391, 1406, 1602, 1829],
  [234, 371, 525, 620, 639, 839, 898, 910, 1063, 1159, 1166, 1202, 1243, 1248, 1265, 1396, 1409, 1553, 1572, 1690],
  [39, 89, 345, 495, 523, 579, 623, 630, 844, 900, 1171, 1177, 1257, 1354, 1373, 1405, 1528, 1585, 1844],
  [41, 101, 352, 509, 595, 659, 850, 910, 911, 1022, 1123, 1147, 1176, 1221, 1263, 1265, 1412, 1422, 1585, 1790, 1827],
  [43, 381, 603, 948, 1187, 1216, 1222, 1426, 1617, 1639],
  [52, 59, 106, 310, 454, 542, 600, 920, 921, 969, 994, 1044, 1076, 1087, 1128, 1270, 1287, 1425, 1545, 1583, 1606, 1745],
  [590, 803, 932, 1053, 1160, 1751],
  [42, 71, 108, 117, 377, 528, 529, 629, 796, 848, 945, 952, 1144, 1173, 1178, 1212, 1288, 1364, 1443, 1539, 1621, 1763],
  [86, 121, 272, 349, 392, 536, 554, 596, 613, 637, 782, 797, 995, 1188, 1196, 1197, 1296, 1418, 1629, 1649],
  [668, 680, 686, 701, 758, 981, 990, 1073, 1077, 1303, 1305, 1320, 1741],
  [103, 302, 413, 506, 585, 592, 688, 696, 711, 1081, 1186, 1262, 1309, 1311, 1314, 1328, 1632, 1640, 1654, 1752, 1875, 1893],
  [19, 36, 137, 185, 354, 593, 626, 918, 989, 1124, 1165, 1246, 1315, 1664],
  [31, 171, 357, 450, 478, 494, 633, 648, 661, 710, 732, 838, 899, 1103, 1109, 1259, 1337, 1353, 1461, 1478, 1489, 1676, 1781, 1892],
  [6, 20, 153, 575, 682, 689, 902, 1144, 1228, 1232, 1308, 1329, 1344, 1446, 1458],
  [118, 155, 172, 216, 299, 396, 454, 501, 615, 653, 759, 843, 861, 1004, 1032, 1117, 1213, 1260, 1283, 1491, 1657, 1681, 1693, 1711],
  [138, 177, 186, 355, 530, 631, 675, 855, 875, 877, 955, 1041, 1266, 1271, 1296, 1671, 1690, 1834],
  [28, 140, 192, 363, 517, 598, 599, 672, 703, 930, 996, 1127, 1172, 1250, 1285, 1347, 1358, 1373, 1474, 1643, 1695],
  [20, 51, 193, 376, 473, 633, 681, 733, 862, 897, 928, 957, 1118, 1280, 1353, 1394, 1501, 1512, 1696],
  [23, 136, 218, 390, 475, 539, 635, 643, 717, 737, 779, 1049, 1071, 1119, 1210, 1253, 1274, 1282, 1304, 1357, 1388, 1396, 1412, 1454, 1514, 1654, 1700, 1707, 1830],
  [137, 178, 194, 366, 540, 604, 614, 705, 931, 962, 1024, 1132, 1173, 1228, 1254, 1277, 1331, 1351, 1376, 1475, 1697],
  [61, 139, 181, 198, 275, 422, 449, 547, 560, 612, 642, 651, 744, 937, 1028, 1092, 1178, 1232, 1254, 1306, 1359, 1363, 1365, 1381, 1507, 1628, 1699, 1845],
  [5, 50, 201, 455, 548, 617, 671, 728, 1046, 1127, 1184, 1261, 1294, 1361, 1516, 1632, 1700, 1805],
  [147, 233, 551, 649, 650, 656, 752, 809, 941, 1060, 1071, 1219, 1264, 1286, 1293, 1310, 1369, 1402, 1409, 1422, 1514, 1850],
  [63, 75, 165, 379, 467, 555, 628, 657, 723, 735, 741, 1127, 1195, 1375, 1382, 1405, 1450, 1474, 1640, 1667, 1707],
  [86, 205, 222, 409, 442, 479, 567, 638, 669, 689, 769, 963, 1092, 1167, 1212, 1277, 1306, 1307, 1389, 1395, 1399, 1414, 1530, 1715],
  [514, 516, 780, 903, 1162, 1520],
  [71, 246, 407, 524, 683, 706, 728, 788, 908, 1072, 1080, 1165, 1172, 1184, 1299, 1355, 1503, 1543, 1559, 1674, 1733],
  [76, 92, 185, 194, 408, 557, 572, 658, 663, 696, 742, 761, 842, 931, 998, 1073, 1081, 1185, 1226, 1268, 1300, 1317, 1379, 1410, 1436, 1519, 1734],
  [42, 249, 500, 661, 681, 763, 953, 1083, 1168, 1174, 1301, 1330, 1420, 1503, 1522, 1531, 1677, 1736, 1758],
  [670, 700, 851, 1335, 1356, 1426, 1793, 1888],
  [90, 109, 203, 262, 310, 578, 615, 710, 808, 821, 1003, 1090, 1091, 1122, 1140, 1191, 1208, 1230, 1239, 1292, 1441, 1451, 1574, 1581, 1730, 1744, 1757, 1862],
  [95, 118, 266, 320, 405, 478, 542, 710, 733, 751, 763, 780, 814, 942, 1096, 1192, 1201, 1207, 1215, 1343, 1447, 1550, 1579, 1586, 1762],
  [21, 126, 220, 224, 288, 306, 518, 619, 718, 719, 796, 815, 1045, 1126, 1247, 1329, 1351, 1359, 1389, 1453, 1546, 1592, 1771],
  [27, 134, 229, 458, 586, 693, 732, 821, 1131, 1167, 1247, 1288, 1331, 1363, 1395, 1453, 1463, 1597],
  [117, 166, 246, 249, 668, 740, 828, 848, 895, 972, 1125, 1136, 1226, 1423, 1462, 1490, 1788],
  [39, 150, 314, 334, 746, 747, 1065, 1067, 1120, 1143, 1344, 1376, 1381, 1414, 1463, 1576, 1790, 1841],
  [126, 257, 311, 331, 488, 546, 587, 634, 653, 762, 843, 1157, 1234, 1362, 1401, 1430, 1502, 1622, 1630, 1804, 1825],
  [55, 138, 153, 469, 639, 726, 1050, 1051, 1120, 1134, 1360, 1365, 1399, 1455, 1786],
  [26, 139, 168, 332, 384, 414, 483, 597, 678, 774, 792, 854, 1141, 1164, 1246, 1250, 1261, 1299, 1482, 1488, 1500, 1636, 1641, 1743, 1820],
  [386, 456, 566, 600, 780, 871, 1291, 1445, 1483, 1798, 1812],
  [200, 1285, 1294, 1297, 1650],
  [150, 274, 342, 358, 610, 659, 777, 861, 1101, 1149, 1183, 1251, 1386, 1421, 1449, 1518, 1638, 1652, 1827, 1844, 1869],
  [75, 283, 338, 343, 490, 755, 818, 984, 1002, 1016, 1151, 1352, 1383, 1390, 1418, 1547, 1752, 1805, 1830],
  [48, 193, 346, 632, 676, 859, 870, 882, 902, 956, 1186, 1268, 1439, 1506, 1509, 1525, 1616],
  [228, 398, 640, 709, 801, 885, 891, 959, 1095, 1195, 1350, 1448, 1452, 1513, 1528, 1542, 1643, 1667, 1850, 1888],
  [290, 299, 385, 697, 1206, 1668, 1858, 1865],
  [107, 198, 253, 332, 457, 734, 758, 819, 824, 895, 907, 937, 1218, 1225, 1289, 1300, 1533, 1535, 1551, 1575, 1870],
  [219, 366, 408, 605, 759, 808, 814, 871, 1224, 1327, 1368, 1433, 1457, 1473, 1549, 1883],
  [13, 221, 364, 367, 430, 731, 805, 1101, 1316, 1600, 1887],
  [25, 121, 197, 222, 645, 686, 765, 806, 837, 859, 919, 940, 963, 1013, 1148, 1262, 1289, 1317, 1348, 1366, 1565, 1593, 1596, 1601, 1615],
  [43, 224, 417, 570, 648, 685, 751, 838, 862, 903, 942, 1321, 1326, 1484, 1570, 1694, 1705, 1713, 1890],
  [261, 276, 373, 418, 571, 664, 767, 817, 840, 914, 943, 1116, 1170, 1415, 1480, 1485, 1563, 1567, 1572, 1585, 1695, 1707, 1850],
  [10, 32, 382, 730, 778, 800, 827, 921, 935, 1027, 1273, 1471, 1580, 1584, 1603, 1840, 1860],
  [17, 70, 163, 384, 422, 457, 790, 800, 872, 1273, 1435, 1440, 1477, 1625, 1635, 1726, 1873, 1891],
  [5, 23, 165, 283, 428, 439, 580, 711, 834, 866, 873, 952, 1132, 1161, 1279, 1443, 1458, 1475, 1507, 1530, 1592, 1597, 1686, 1875],
  [24, 220, 257, 372, 440, 583, 644, 684, 749, 836, 858, 908, 939, 1227, 1315, 1347, 1361, 1482, 1538, 1694, 1703, 1712],
  [278, 591, 690, 989, 1000, 1209, 1241, 1358, 1371, 1488, 1511, 1749],
  [41, 274, 453, 606, 704, 856, 879, 1193, 1241, 1373, 1385, 1500, 1564, 1729],
  [94, 279, 294, 712, 860, 973, 1438, 1504, 1617, 1888],
  [37, 98, 149, 275, 414, 805, 893, 1372, 1476, 1623, 1634],
  [58, 290, 405, 468, 897, 953, 1397, 1750],
  [94, 177, 771, 924, 1244, 1324, 1479, 1562, 1588, 1639, 1793],
  [69, 78, 306, 311, 335, 417, 440, 486, 694, 745, 798, 846, 917, 972, 1026, 1045, 1094, 1235, 1303, 1309, 1410, 1434, 1506, 1533, 1596, 1605, 1647, 1653, 1787, 1794],
  [74, 182, 419, 753, 802, 826, 899, 988, 1003, 1070, 1305, 1311, 1366, 1379, 1434, 1462, 1535, 1565, 1647, 1670, 1765, 1772],
  [8, 83, 316, 477, 778, 813, 926, 1011, 1032, 1099, 1157, 1183, 1206, 1416, 1424, 1536, 1660, 1791, 1800],
  [64, 104, 186, 346, 654, 781, 853, 938, 1018, 1033, 1050, 1102, 1314, 1319, 1490, 1566, 1575, 1601, 1653, 1659, 1673, 1792, 1803],
  [91, 324, 367, 893, 957, 1427, 1431, 1665, 1778],
  [89, 101, 334, 342, 361, 453, 766, 869, 947, 1043, 1065, 1113, 1252, 1319, 1320, 1328, 1436, 1525, 1551, 1615, 1620, 1670, 1673, 1808, 1818],
  [376, 784, 982, 1037, 1662],
  [261, 471, 480, 526, 699, 967, 1015, 1064, 1205, 1221, 1231, 1284, 1339, 1540, 1573, 1578, 1629, 1688, 1690, 1830],
  [456, 787],
  [177, 279, 1059, 1222, 1393, 1627, 1649],
  [103, 136, 436, 550, 713, 829, 997, 1020, 1080, 1124, 1371, 1385, 1392, 1474, 1543, 1636, 1703, 1864],
  [1040, 1515],
  [147, 445, 556, 721, 906, 980, 1009, 1030, 1046, 1106, 1164, 1380, 1392, 1516, 1559, 1641, 1643, 1650, 1712, 1729, 1749, 1864],
  [148, 513, 540, 557, 569, 759, 883, 1010, 1234, 1251, 1316, 1416, 1517, 1618, 1642, 1669],
  [93, 112, 158, 179, 313, 500, 524, 529, 878, 991, 1087, 1242, 1408, 1440, 1604, 1728],
  [159, 272, 409, 793, 923, 1019, 1037, 1062, 1494, 1722],
  [100, 164, 273, 280, 412, 826, 827, 881, 889, 896, 926, 1091, 1100, 1131, 1182, 1305, 1492, 1496, 1532, 1541, 1631, 1725, 1732, 1747, 1876, 1882],
  [4, 161, 183, 473, 575, 632, 784, 934, 951, 1038, 1128, 1137, 1349, 1477, 1604, 1685, 1756, 1777, 1784, 1796, 1877],
  [23, 373, 480, 562, 639, 1035, 1074, 1152, 1377, 1378, 1467, 1621, 1697, 1698, 1699, 1715, 1771, 1775, 1790],
  [209, 236, 488, 570, 865, 904, 1075, 1115, 1722, 1735],
  [201, 218, 343, 439, 482, 550, 799, 960, 981, 1048, 1054, 1125, 1139, 1161, 1185, 1218, 1468, 1519, 1765, 1787, 1792, 1808],
  [12, 22, 226, 349, 442, 645, 793, 889, 965, 966, 1108, 1167, 1366, 1548, 1557, 1614, 1795, 1813, 1821],
  [233, 398, 491, 556, 971, 990, 1057, 1058, 1066, 1136, 1145, 1225, 1468, 1772, 1794, 1803, 1818],
  [56, 234, 256, 355, 469, 654, 698, 849, 920, 1004, 1090, 1096, 1211, 1487, 1608, 1644, 1672, 1711, 1716, 1742, 1797],
  [49, 242, 370, 499, 511, 593, 604, 605, 658, 808, 979, 992, 1010, 1103, 1191, 1331, 1379, 1492, 1548, 1582, 1612, 1651, 1679, 1719, 1746, 1801, 1824],
  [53, 65, 197, 269, 287, 392, 479, 686, 889, 935, 1011, 1061, 1100, 1198, 1258, 1529, 1571, 1655, 1724, 1836, 1842, 1854],
  [170, 190, 247, 265, 404, 597, 612, 863, 969, 1014, 1027, 1078, 1527, 1587, 1624, 1685, 1816, 1832],
  [36, 57, 248, 513, 614, 663, 814, 1103, 1118, 1168, 1201, 1321, 1427, 1590, 1727],
  [63, 228, 276, 294, 519, 652, 692, 832, 1109, 1110, 1162, 1174, 1207, 1326, 1397, 1431, 1731, 1739, 1849],
  [28, 75, 261, 279, 679, 822, 925, 1088, 1142, 1153, 1180, 1197, 1338, 1354, 1374, 1444, 1714, 1751, 1834],
  [77, 84, 188, 263, 380, 470, 680, 730, 804, 881, 921, 1032, 1091, 1198, 1224, 1272, 1487, 1595, 1599, 1609, 1633, 1645, 1717, 1831, 1835, 1847],
  [211, 267, 321, 638, 887, 935, 994, 1034, 1137, 1527, 1755, 1839, 1853],
  [96, 105, 271, 277, 518, 535, 546, 644, 648, 694, 865, 1021, 1175, 1247, 1434, 1532, 1612, 1708, 1799, 1852],
  [47, 51, 72, 80, 687, 951, 1025, 1213, 1220, 1362, 1386, 1439, 1618, 1740, 1829],
  [563, 871, 998, 1814],
  [119, 127, 244, 303, 318, 547, 655, 678, 716, 734, 790, 805, 1014, 1052, 1099, 1163, 1260, 1401, 1421, 1536, 1556, 1607, 1642, 1740, 1828, 1879],
  [123, 133, 252, 312, 329, 427, 528, 568, 661, 683, 740, 988, 991, 1042, 1056, 1175, 1239, 1288, 1407, 1462, 1541, 1552, 1614, 1651, 1748, 1779, 1802, 1843, 1884],
  [16, 125, 296, 330, 381, 474, 587, 684, 685, 719, 745, 904, 976, 1076, 1237, 1242, 1580, 1587, 1777],
  [2, 11, 341, 391, 446, 560, 800, 1027, 1061, 1099, 1182, 1258, 1272, 1663, 1666, 1885],
  [0, 347, 354, 602, 705, 761, 992, 1191, 1201, 1561, 1577, 1595, 1684, 1702, 1738, 1764, 1823, 1846],
  [7, 143, 154, 351, 567, 750, 765, 923, 965, 1011, 1034, 1079, 1199, 1220, 1283, 1430, 1449, 1607, 1669, 1678, 1828],
  [38, 146, 328, 352, 495, 610, 704, 747, 766, 1093, 1203, 1256, 1287, 1568, 1603, 1635, 1796, 1832, 1853],
  [16, 38, 131, 305, 350, 371, 481, 690, 698, 726, 771, 781, 920, 1082, 1097, 1179, 1190, 1270, 1456, 1568, 1584, 1625, 1728, 1784, 1810, 1816, 1839],
  [21, 27, 39, 55, 140, 165, 373, 652, 785, 795, 949, 1031, 1121, 1217, 1302, 1307, 1470, 1495, 1524, 1763, 1845],
  [3, 24, 41, 136, 147, 471, 562, 624, 786, 929, 1029, 1104, 1189, 1214, 1276, 1498, 1553, 1664, 1695, 1700, 1733, 1815, 1820],
  [35, 54, 128, 151, 160, 487, 633, 783, 1038, 1098, 1108, 1114, 1292, 1295, 1308, 1509, 1679, 1708, 1748, 1829, 1833],
  [44, 184, 196, 372, 378, 389, 619, 653, 749, 751, 798, 1269, 1291, 1327, 1608, 1633, 1702, 1710, 1806, 1889],
  [40, 167, 302, 379, 390, 490, 580, 799, 835, 1008, 1044, 1117, 1208, 1215, 1281, 1609, 1626, 1710, 1753, 1807, 1837, 1859],
  [73, 85, 208, 213, 340, 403, 416, 515, 642, 666, 774, 819, 863, 1070, 1122, 1135, 1163, 1182, 1259, 1363, 1535, 1631, 1648, 1691, 1719, 1766, 1779, 1833],
  [69, 74, 89, 104, 192, 398, 418, 618, 679, 692, 785, 1077, 1169, 1229, 1255, 1332, 1342, 1348, 1428, 1495, 1554, 1640],
  [79, 168, 210, 225, 348, 423, 460, 651, 655, 824, 872, 893, 1078, 1259, 1280, 1301, 1343, 1484, 1658, 1727, 1731],
  [200, 217, 232, 1330, 1739, 1781],
  [25, 78, 82, 101, 218, 233, 418, 526, 676, 786, 1085, 1204, 1267, 1325, 1340, 1377, 1437, 1523, 1654, 1734, 1788, 1870, 1886],
  [1, 34, 88, 223, 235, 359, 407, 421, 432, 629, 763, 788, 828, 878, 961, 1042, 1087, 1239, 1269, 1281, 1368, 1493, 1644, 1645, 1656, 1738, 1753, 1848, 1871],
  [99, 110, 113, 238, 250, 438, 536, 669, 837, 887, 1019, 1100, 1140, 1158, 1199, 1295, 1395, 1565, 1691, 1746, 1754, 1789, 1802],
  [7, 68, 251, 420, 433, 687, 773, 1004, 1097, 1149, 1159, 1360, 1502, 1518, 1566, 1600, 1660, 1879],
  [402, 443, 564, 674, 804, 1206, 1759],
  [33, 111, 113, 115, 120, 259, 268, 451, 554, 689, 859, 1037, 1108, 1137, 1220, 1295, 1398, 1593, 1706, 1769, 1821, 1855],
  [19, 26, 28, 471, 833, 880, 1039, 1290, 1336, 1355, 1538, 1564, 1613, 1671, 1805],
  [29, 109, 122, 141, 230, 255, 260, 472, 574, 682, 733, 882, 934, 1017, 1098, 1128, 1213, 1292, 1398, 1433, 1611, 1672, 1764, 1785, 1806, 1807, 1811, 1848],
  [4, 125, 131, 146, 215, 413, 434, 455, 475, 628, 829, 834, 835, 1044, 1200, 1236, 1313, 1322, 1408, 1425, 1726, 1867],
  [6, 61, 86, 134, 138, 283, 480, 833, 875, 888, 1068, 1318, 1364, 1429, 1546, 1576, 1591, 1619, 1646, 1720],
  [35, 102, 173, 286, 295, 485, 508, 718, 762, 775, 836, 838, 917, 976, 1075, 1230, 1240, 1407, 1453, 1647, 1725, 1766, 1789, 1801],
  [145, 169, 596, 1148, 1445, 1814, 1822],
  [29, 162, 174, 307, 323, 437, 483, 493, 507, 611, 744, 854, 907, 969, 1122, 1260, 1272, 1343, 1457, 1716, 1717, 1737, 1780, 1823, 1837, 1861, 1871],
  [54, 85, 110, 116, 191, 309, 327, 509, 523, 625, 746, 777, 794, 856, 947, 1203, 1245, 1263, 1451, 1463, 1670, 1718, 1747, 1813, 1824],
  [68, 73, 99, 173, 191, 292, 304, 502, 510, 631, 783, 849, 1090, 1179, 1233, 1248, 1337, 1441, 1455, 1659, 1718, 1732, 1795, 1852, 1884],
  [79, 278, 300, 315, 525, 773, 924, 938, 1096, 1190, 1337, 1394, 1420, 1447, 1459, 1486, 1570, 1665, 1838, 1849],
  [48, 76, 107, 121, 182, 186, 343, 526, 679, 791, 880, 888, 968, 1298, 1367, 1423, 1465, 1526, 1605, 1619, 1620, 1637, 1683, 1741, 1752],
  [1, 187, 199, 344, 353, 527, 637, 769, 940, 994, 1140, 1198, 1283, 1398, 1445, 1473, 1742, 1780, 1846, 1851, 1859, 1881],
  [72, 119, 143, 289, 374, 506, 539, 548, 555, 901, 960, 975, 1117, 1236, 1274, 1391, 1517, 1622, 1638, 1782, 1791],
  [145, 157, 558, 903, 1235, 1237, 1291, 1483],
  [80, 127, 154, 251, 374, 551, 709, 906, 913, 971, 986, 1286, 1370, 1406, 1491, 1556, 1630, 1652, 1668, 1782, 1800],
  [81, 130, 156, 212, 375, 383, 486, 543, 552, 603, 796, 908, 972, 1175, 1242, 1269, 1407, 1493, 1774, 1783, 1872],
  [129, 159, 209, 214, 571, 699, 1249, 1312, 1411, 1417, 1454],
  [114, 258, 559, 831, 918, 962, 1316, 1372, 1427],
  [169, 176, 579, 1252, 1256],
  [5, 71, 137, 139, 140, 220, 229, 562, 621, 833, 847, 985, 1000, 1133, 1384, 1419, 1446, 1701, 1723, 1786],
  [236, 571, 822, 832, 949, 1333, 1403, 1404, 1450, 1494],
  [0, 40, 122, 189, 270, 401, 406, 573, 583, 594, 815, 843, 939, 942, 1026, 1076, 1230, 1483, 1493, 1549, 1797, 1831, 1861, 1881],
  [202, 541, 588, 953, 961],
  [60, 141, 174, 199, 207, 429, 595, 606, 623, 861, 1043, 1093, 1245, 1287, 1451, 1577, 1819, 1847],
  [44, 45, 88, 155, 162, 187, 270, 415, 591, 601, 620, 1033, 1082, 1233, 1270, 1441, 1447, 1537, 1561, 1819, 1835],
  [36, 50, 168, 200, 278, 436, 445, 624, 847, 852, 1036, 1192, 1278, 1461, 1503, 1520, 1550, 1694, 1778, 1838],
  [117, 194, 195, 198, 222, 281, 306, 334, 439, 785, 888, 902, 985, 1050, 1377, 1400, 1466, 1469, 1539, 1555, 1628, 1875],
  [12, 49, 96, 123, 151, 208, 238, 286, 292, 309, 395, 452, 585, 617, 635, 657, 755, 764, 866, 884, 997, 1008, 1048, 1208, 1311, 1313, 1341, 1357, 1391, 1478, 1552, 1574, 1582, 1597, 1765, 1866, 1876],
  [108, 178, 181, 205, 288, 314, 428, 621, 795, 875, 1000, 1211, 1456, 1459, 1537, 1767, 1841, 1856],
  [50, 57, 63, 210, 217, 300, 400, 436, 459, 592, 643, 873, 901, 1054, 1083, 1215, 1322, 1478, 1501, 1522, 1579, 1590, 1705, 1874],
  [22, 105, 133, 160, 213, 250, 295, 304, 327, 452, 649, 770, 801, 892, 1009, 1057, 1345, 1369, 1406, 1460, 1489, 1581, 1648, 1772, 1866, 1882],
  [112, 161, 190, 211, 296, 305, 328, 434, 650, 670, 980, 1058, 1346, 1370, 1435, 1460, 1464, 1545, 1624, 1860, 1867, 1891],
  [464, 897, 1017, 1773],
  [225, 228, 232, 315, 445, 459, 656, 700, 913, 1066, 1464, 1489, 1512, 1531, 1586, 1658, 1713, 1750, 1874],
  [87, 144, 231, 239, 308, 319, 337, 463, 572, 660, 915, 1024, 1073, 1224, 1416, 1492, 1571, 1595, 1663],
  [152, 237, 245, 317, 345, 365, 467, 618, 640, 664, 712, 925, 1031, 1077, 1424, 1471, 1496, 1599, 1666, 1759],
  [10, 17, 158, 183, 243, 247, 267, 330, 333, 352, 371, 475, 650, 817, 1029, 1035, 1085, 1249, 1413, 1432, 1505, 1510, 1606],
  [92, 166, 253, 335, 361, 461, 482, 491, 791, 928, 1349, 1593, 1598, 1611, 1682, 1773, 1893],
  [272, 699, 822, 1068, 1508, 1547, 1735],
  [114, 387, 462, 811, 957, 1476],
  [32, 70, 179, 265, 321, 381, 670, 771, 860, 1558],
  [124, 241, 297, 326, 338, 393, 717, 728, 741, 952, 1080, 1083, 1281, 1408, 1552, 1656, 1692, 1783],
  [45, 60, 67, 77, 184, 223, 255, 307, 344, 401, 544, 688, 713, 723, 737, 1139, 1200, 1341, 1425, 1574, 1579, 1656, 1684],
  [62, 144, 152, 362, 411, 668, 743, 945, 1541, 1645, 1655, 1704, 1774],
  [83, 148, 318, 351, 410, 539, 551, 767, 1025, 1104, 1105, 1159, 1312, 1432, 1681, 1698, 1804, 1827, 1865, 1886, 1887],
  [56, 67, 84, 167, 196, 235, 260, 323, 353, 406, 415, 429, 544, 721, 752, 885, 1106, 1145, 1275, 1345, 1346, 1491, 1545, 1581, 1586, 1626, 1737],
  [13, 303, 433, 517, 519, 555, 709, 767, 1121, 1150, 1169, 1333, 1424, 1480, 1569, 1602, 1678, 1693, 1825, 1844, 1858],
  [87, 240, 284, 325, 356, 368, 435, 696, 779, 1016, 1132, 1185, 1517, 1582, 1590, 1692],
  [15, 64, 103, 185, 192, 201, 246, 332, 419, 440, 453, 461, 550, 556, 786, 880, 985, 1036, 1334, 1442, 1497, 1589, 1616, 1632, 1674, 1687, 1701, 1743],
  [409, 458, 949, 1068, 1610, 1686],
  [204, 336, 424, 465, 489, 504, 809, 851, 959, 1164, 1435, 1556, 1624, 1648, 1658, 1737],
  [124, 144, 240, 339, 399, 426, 576, 742, 810, 1165, 1168, 1173, 1226, 1368, 1651, 1692, 1738, 1872],
  [163, 313, 404, 474, 481, 495, 599, 628, 817, 860, 1110, 1229, 1404, 1471, 1521, 1569, 1661, 1709, 1745, 1755],
  [132, 142, 231, 237, 476, 484, 497, 758, 820, 922, 1028, 1273, 1529, 1536, 1631, 1704, 1717, 1724],
  [239, 245, 280, 505, 932],
  [82, 164, 226, 242, 277, 329, 410, 416, 438, 485, 509, 635, 649, 840, 967, 1114, 1189, 1248, 1411, 1505, 1560, 1676, 1757, 1775],
  [58, 91, 248, 276, 423, 494, 525, 624, 643, 656, 1074, 1105, 1267, 1417, 1510, 1676, 1696, 1736, 1762, 1817, 1890],
  [135, 258, 430, 522, 823, 830, 839, 955, 1051, 1209, 1244, 1600, 1623, 1665, 1767],
  [27, 74, 271, 312, 403, 508, 510, 523, 598, 657, 801, 840, 936, 1088, 1109, 1217, 1255, 1403, 1496, 1544, 1557, 1567, 1602, 1661, 1744, 1754],
  [204, 264, 293, 360, 538, 553, 665, 673, 806, 876, 894, 995, 1061, 1092, 1289, 1529, 1607, 1706],
  [135, 387, 447, 522, 844, 850, 1067, 1101, 1193, 1634],
  [92, 114, 284, 339, 425, 499, 520, 537, 626, 647, 857, 1111, 1118, 1228, 1268, 1433, 1618, 1679, 1764, 1769],
  [43, 294, 460, 700, 924, 1558, 1758],
  [231, 264, 325, 399, 425, 496, 545, 549, 561, 702, 842, 886, 1156, 1246, 1254, 1300, 1372, 1457, 1642, 1663, 1719, 1727, 1823],
  [308, 317, 476, 512, 584, 707, 715, 846, 890, 948, 1126, 1157, 1303, 1532, 1580, 1633, 1725, 1774, 1831, 1836, 1885],
  [2, 227, 319, 365, 411, 477, 484, 584, 609, 714, 722, 853, 898, 1041, 1134, 1324, 1487, 1584, 1660, 1732, 1835, 1842, 1856],
  [558, 579, 672, 1142, 1162, 1554, 1709, 1812, 1822],
  [264, 356, 426, 496, 565, 589, 608, 725, 909, 1188, 1277, 1317, 1473, 1548, 1571, 1669, 1746, 1769, 1814, 1846],
  [135, 227, 444, 466, 492, 530, 708, 900, 910, 1120, 1149, 1319, 1568, 1718, 1841, 1869],
  [11, 227, 337, 345, 497, 505, 531, 609, 727, 738, 869, 911, 1143, 1183, 1320, 1603, 1747, 1847, 1854],
  [81, 166, 241, 339, 498, 532, 568, 681, 706, 729, 739, 870, 912, 1144, 1598, 1604, 1748, 1848, 1855],
  [293, 431, 503, 607, 616, 630, 735, 891, 914, 973, 1197, 1307, 1348, 1494, 1557, 1678, 1754, 1755, 1822, 1851],
  [234, 263, 347, 389, 390, 397, 432, 472, 501, 507, 527, 573, 578, 595, 620, 737, 752, 929, 943, 1064, 1152, 1276, 1325, 1413, 1481, 1560, 1606, 1681, 1757, 1762, 1883],
  [239, 368, 370, 1160],
  [363, 372, 407, 483, 583, 721, 929, 1039, 1133, 1192, 1334, 1387, 1534, 1583, 1657, 1730, 1785, 1798],
  [464, 941, 1095, 1275, 1668, 1750],
  [256, 363, 378, 379, 421, 493, 594, 601, 623, 703, 723, 885, 943, 1180, 1207, 1302, 1342, 1472, 1521, 1544, 1599, 1693, 1744, 1745, 1812, 1851],
  [280, 370, 427, 625, 764, 770, 936, 1053, 1297, 1515, 1781],
  [102, 116, 134, 182, 273, 349, 487, 511, 515, 536, 631, 755, 967, 1053, 1088, 1223, 1290, 1318, 1367, 1508, 1675, 1688, 1799, 1843, 1862],
  [126, 150, 195, 221, 316, 540, 547, 567, 636, 1121, 1323, 1360, 1698, 1776],
  [130, 291, 301, 360, 399, 498, 581, 641, 895, 977, 999, 1178, 1299, 1301, 1440, 1704, 1779, 1871],
  [297, 427, 590, 1330],
  [0, 308, 435, 520, 545, 565, 754, 789, 1005, 1234, 1315, 1321, 1327, 1351, 1410, 1549, 1612, 1702, 1801, 1872],
  [29, 33, 253, 336, 425, 498, 662, 666, 677, 691, 792, 807, 816, 956, 1006, 1130, 1232, 1280, 1476, 1477, 1682, 1685, 1706, 1740, 1833],
  [1, 156, 326, 360, 426, 431, 613, 667, 919, 1007, 1023, 1212, 1614, 1655, 1802, 1855],
  [157, 176, 563, 596, 1142, 1683],
  [178, 258, 298, 319, 441, 549, 569, 608, 989, 1266, 1561],
  [34, 202, 338, 362, 532, 576, 581, 590, 613, 675, 818, 968, 1015, 1059, 1153, 1355, 1364, 1423, 1843],
  [298, 337, 448, 537, 561, 589, 772, 1022, 1251, 1376, 1436, 1577, 1824],
  [18, 52, 350, 384, 455, 524, 597, 599, 684, 690, 704, 829, 980, 1029, 1278, 1384, 1387, 1442, 1583, 1721, 1768, 1857, 1877],
  [34, 189, 207, 219, 355, 380, 490, 574, 602, 611, 637, 1039, 1064, 1180, 1429, 1465, 1594, 1675, 1862, 1889],
  [59, 282, 382, 422, 529, 575, 612, 638, 693, 719, 726, 747, 834, 1035, 1384, 1456, 1466, 1610, 1761, 1776, 1863, 1868],
  [67, 582, 627, 646, 724, 736, 756, 1046, 1071, 1195, 1392, 1626, 1782, 1866, 1867, 1874],
  [53, 62, 77, 87, 132, 388, 463, 467, 707, 714, 727, 981, 1049, 1151, 1279, 1609, 1791, 1876],
  [65, 84, 142, 388, 640, 715, 722, 738, 990, 1060, 1800, 1860, 1882],
  [88, 108, 212, 393, 411, 641, 667, 675, 864, 874, 1018, 1063, 1072, 1084, 1420, 1479, 1490, 1644, 1728, 1884],
  [90, 281, 412, 442, 518, 528, 604, 636, 642, 669, 718, 746, 866, 1217, 1308, 1318, 1419, 1455, 1760, 1775, 1863, 1892],
  [20, 42, 95, 224, 285, 324, 614, 651, 652, 732, 847, 873, 1074, 1323, 1459, 1469, 1868, 1892],
  [9, 14, 93, 106, 170, 282, 322, 413, 457, 632, 745, 753, 766, 781, 1058, 1085, 1229, 1349, 1442, 1466, 1809, 1826, 1840, 1873],
  [33, 424, 496, 503, 534, 757, 768, 1013, 1086, 1107, 1196, 1258, 1306, 1527, 1691, 1724, 1780, 1828],
  [30, 47, 257, 274, 364, 420, 517, 548, 678, 852, 906, 1104, 1138, 1497, 1511, 1657, 1768, 1815],
  [31, 51, 118, 290, 367, 513, 519, 655, 773, 852, 901, 913, 1105, 1323, 1486, 1499, 1680, 1770, 1817],
  [35, 81, 111, 122, 335, 520, 535, 662, 720, 775, 858, 862, 905, 916, 1112, 1329, 1362, 1506, 1708, 1777, 1806],
  [109, 113, 499, 535, 568, 666, 775, 794, 867, 884, 892, 1223, 1353, 1662, 1756, 1811, 1821],
  [115, 153, 346, 444, 521, 687, 691, 783, 927, 1394, 1672, 1784],
  [1095, 1116, 1374, 1397, 1470, 1472, 1759, 1858],
  [49, 57, 124, 441, 448, 463, 647, 702, 725, 789, 1081, 1119, 1124, 1383, 1475, 1519, 1684],
  [58, 443, 588, 697, 941, 1116, 1231, 1481, 1523, 1865],
  [54, 120, 141, 361, 387, 444, 537, 677, 748, 794, 879, 933, 944, 1123, 1344, 1386, 1525, 1796],
  [130, 465, 476, 534, 545, 662, 760, 825, 946, 954, 1094, 1129, 1146, 1187, 1359, 1401, 1482, 1484, 1533, 1587, 1766, 1861, 1885],
  [2, 73, 79, 162, 181, 466, 484, 504, 538, 549, 641, 691, 716, 757, 825, 841, 950, 958, 1102, 1141, 1155, 1166, 1271, 1365, 1488, 1562, 1575, 1623, 1625, 1716, 1816, 1879],
  [46, 91, 559, 731, 839, 850, 1170, 1284, 1378, 1498, 1887],
  [11, 85, 174, 466, 489, 497, 553, 561, 677, 768, 776, 841, 964, 974, 1113, 1147, 1171, 1381, 1421, 1500, 1551, 1634, 1635, 1832],
  [59, 90, 95, 366, 394, 469, 470, 580, 586, 619, 629, 682, 705, 744, 769, 815, 821, 1133, 1152, 1211, 1302, 1429, 1537, 1555, 1689, 1760, 1761],
  [111, 145, 156, 534, 565, 607, 782, 845, 970, 983, 1154, 1216, 1389, 1430, 1596, 1722, 1789, 1836, 1881],
  [155, 331, 358, 430, 477, 569, 716, 750, 975, 986, 1138, 1150, 1486, 1511, 1711, 1810, 1869],
  [13, 37, 830, 844, 930, 1170, 1431, 1444, 1524],
  [110, 120, 169, 199, 492, 553, 589, 630, 768, 797, 868, 993, 1001, 1176, 1414, 1449, 1615, 1813, 1853, 1854],
  [8, 172, 195, 244, 311, 342, 385, 506, 557, 734, 765, 812, 960, 971, 1169, 1439, 1497, 1499, 1566, 1826, 1886],
  [3, 30, 128, 203, 229, 419, 502, 593, 598, 617, 644, 683, 774, 836, 856, 867, 997, 1009, 1189, 1290, 1297, 1419, 1461, 1534, 1589, 1730, 1857, 1878],
  [505, 625, 803, 1012, 1177],
  [7, 99, 115, 187, 205, 492, 538, 608, 616, 667, 750, 757, 845, 868, 978, 987, 1202, 1296, 1399, 1588, 1601, 1742, 1795, 1839, 1842],
  [8, 100, 188, 197, 206, 402, 572, 618, 826, 846, 853, 869, 1204, 1298, 1400, 1840],
  [102, 157, 189, 512, 720, 754, 760, 782, 855, 984, 1205, 1222, 1338, 1538, 1546, 1605, 1735, 1799, 1889],
  [98, 1244],
  [62, 123, 223, 240, 291, 375, 533, 729, 818, 864, 1125, 1184, 1210, 1443, 1522, 1543, 1753],
  [47, 128, 230, 461, 462, 521, 626, 671, 706, 792, 858, 867, 879, 1020, 1030, 1214, 1336, 1446, 1616, 1785, 1877],
  [112, 133, 235, 301, 383, 533, 739, 874, 1136, 1219, 1350, 1531, 1559],
  [116, 176, 207, 447, 530, 531, 748, 772, 776, 797, 803, 877, 1002, 1221, 1354, 1564, 1576, 1620]]

def thirdSuccessors (i : ℕ) : List ℕ := thirdSuccessorsList.getD i []


noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 12 1 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1 z v))

lemma afterSecond_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 11)
    (mixed : mixedFromSecond state = false)
    (pure : pureAt 11 state (fun z v => afterThird (z,v)) = false) :
    afterSecond state = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 12 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 12 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [afterSecond, frc_eq, st_eq, show (13 : ℕ) = Nat.succ 12 from rfl, look1C_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureAt 11 state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeCheck_append (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all



noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  let ids := thirdSuccessors i
  (!pureAt 11 state (frontierMissing (ids.map thirdAt))) &&
    ((ids.all fun j => decide (j < thirdCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 11)))

noncomputable def thirdTest (j : ℕ) : Bool := !afterThird (thirdAt j)
noncomputable def secondMixedTest (j : ℕ) : Bool := !mixedFromSecond (secondAt j)

lemma checkedAfterSecond (i : ℕ) (hi : i < secondCount)
    (ready : rangeCheck readyForThird 0 secondCount = true)
    (mixed : rangeCheck secondMixedTest 0 secondCount = true)
    (third : rangeCheck thirdTest 0 thirdCount = true) :
    afterSecond (secondAt i) = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForThird, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterSecond_false (secondAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_from_frontier 11 (secondAt i) ((thirdSuccessors i).map thirdAt) afterThird (boolOfNeg hc) ?_
  intro state membership
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp membership
  have hj' : j < thirdCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact boolOfNeg (rangeCheck_at third hj')


noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  let ids := secondSuccessors i
  (!pureSecond state (frontierMissing (ids.map secondAt))) &&
    ((ids.all fun j => decide (j < secondCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def mixedSecondPicked (state : SearchState) (b : Fin 8) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvPicked I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0 b))

lemma mixedSecondPicked_all (state : SearchState)
    (checked : ∀ b, mixedSecondPicked state b = false) : mixedSecond state = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  simp only [mixedSecond, frc_eq, st_eq] at h
  obtain ⟨b,hb⟩ := mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hc := checked b
  simp only [mixedSecondPicked, frc_eq, st_eq] at hc
  exact Bool.noConfusion (hc.symm.trans hb)

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureSecond_from_frontier (firstAt i) ((secondSuccessors i).map secondAt) (boolOfNeg hc) ?_
  intro state membership
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp membership
  have hj' : j < secondCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact next j hj'


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk3 : rangeCheck readyForSecond 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk4 : rangeCheck readyForSecond 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk5 : rangeCheck readyForSecond 20 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk6 : rangeCheck readyForSecond 24 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 firstCount = true := by
  exact (@rangeCheck_append readyForSecond 0 12 16
    (@rangeCheck_append readyForSecond 0 4 8
    firstCoverageChunk0 (@rangeCheck_append readyForSecond 4 4 4
    firstCoverageChunk1 firstCoverageChunk2)) (@rangeCheck_append readyForSecond 12 8 8
    (@rangeCheck_append readyForSecond 12 4 4
    firstCoverageChunk3 firstCoverageChunk4) (@rangeCheck_append readyForSecond 20 4 4
    firstCoverageChunk5 firstCoverageChunk6)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk2 : rangeCheck firstMixedTest 3 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk3 : rangeCheck firstMixedTest 5 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk4 : rangeCheck firstMixedTest 6 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk5 : rangeCheck firstMixedTest 7 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk6 : rangeCheck firstMixedTest 8 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk7 : rangeCheck firstMixedTest 9 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk8 : rangeCheck firstMixedTest 12 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk9 : rangeCheck firstMixedTest 14 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk10 : rangeCheck firstMixedTest 16 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk11 : rangeCheck firstMixedTest 17 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk12 : rangeCheck firstMixedTest 18 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk13 : rangeCheck firstMixedTest 19 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk14 : rangeCheck firstMixedTest 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk15 : rangeCheck firstMixedTest 22 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk16 : rangeCheck firstMixedTest 24 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk17 : rangeCheck firstMixedTest 25 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part0 : mixedSecondPicked (firstAt 26) 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part1 : mixedSecondPicked (firstAt 26) 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part2 : mixedSecondPicked (firstAt 26) 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part3 : mixedSecondPicked (firstAt 26) 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part4 : mixedSecondPicked (firstAt 26) 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part5 : mixedSecondPicked (firstAt 26) 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part6 : mixedSecondPicked (firstAt 26) 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18Part7 : mixedSecondPicked (firstAt 26) 7 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18 : rangeCheck firstMixedTest 26 1 = true := by
  have result : mixedSecond (firstAt 26) = false := by
    apply mixedSecondPicked_all
    intro b
    fin_cases b
    · exact firstMixedChunk18Part0
    · exact firstMixedChunk18Part1
    · exact firstMixedChunk18Part2
    · exact firstMixedChunk18Part3
    · exact firstMixedChunk18Part4
    · exact firstMixedChunk18Part5
    · exact firstMixedChunk18Part6
    · exact firstMixedChunk18Part7
  simp [rangeCheck, firstMixedTest, result]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk19 : rangeCheck firstMixedTest 27 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 firstCount = true := by
  exact (@rangeCheck_append firstMixedTest 0 16 12
    (@rangeCheck_append firstMixedTest 0 7 9
    (@rangeCheck_append firstMixedTest 0 3 4
    (@rangeCheck_append firstMixedTest 0 2 1
    firstMixedChunk0 firstMixedChunk1) (@rangeCheck_append firstMixedTest 3 2 2
    firstMixedChunk2 (@rangeCheck_append firstMixedTest 5 1 1
    firstMixedChunk3 firstMixedChunk4))) (@rangeCheck_append firstMixedTest 7 2 7
    (@rangeCheck_append firstMixedTest 7 1 1
    firstMixedChunk5 firstMixedChunk6) (@rangeCheck_append firstMixedTest 9 3 4
    firstMixedChunk7 (@rangeCheck_append firstMixedTest 12 2 2
    firstMixedChunk8 firstMixedChunk9)))) (@rangeCheck_append firstMixedTest 16 6 6
    (@rangeCheck_append firstMixedTest 16 2 4
    (@rangeCheck_append firstMixedTest 16 1 1
    firstMixedChunk10 firstMixedChunk11) (@rangeCheck_append firstMixedTest 18 1 3
    firstMixedChunk12 (@rangeCheck_append firstMixedTest 19 1 2
    firstMixedChunk13 firstMixedChunk14))) (@rangeCheck_append firstMixedTest 22 3 3
    (@rangeCheck_append firstMixedTest 22 2 1
    firstMixedChunk15 firstMixedChunk16) (@rangeCheck_append firstMixedTest 25 1 2
    firstMixedChunk17 (@rangeCheck_append firstMixedTest 26 1 1
    firstMixedChunk18 firstMixedChunk19)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 96 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 112 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 128 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 144 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 160 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 176 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk12 : rangeCheck readyForThird 192 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk13 : rangeCheck readyForThird 208 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk14 : rangeCheck readyForThird 224 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk15 : rangeCheck readyForThird 240 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk16 : rangeCheck readyForThird 256 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk17 : rangeCheck readyForThird 272 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk18 : rangeCheck readyForThird 288 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk19 : rangeCheck readyForThird 304 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 secondCount = true := by
  exact (@rangeCheck_append readyForThird 0 160 157
    (@rangeCheck_append readyForThird 0 80 80
    (@rangeCheck_append readyForThird 0 32 48
    (@rangeCheck_append readyForThird 0 16 16
    secondCoverageChunk0 secondCoverageChunk1) (@rangeCheck_append readyForThird 32 16 32
    secondCoverageChunk2 (@rangeCheck_append readyForThird 48 16 16
    secondCoverageChunk3 secondCoverageChunk4))) (@rangeCheck_append readyForThird 80 32 48
    (@rangeCheck_append readyForThird 80 16 16
    secondCoverageChunk5 secondCoverageChunk6) (@rangeCheck_append readyForThird 112 16 32
    secondCoverageChunk7 (@rangeCheck_append readyForThird 128 16 16
    secondCoverageChunk8 secondCoverageChunk9)))) (@rangeCheck_append readyForThird 160 80 77
    (@rangeCheck_append readyForThird 160 32 48
    (@rangeCheck_append readyForThird 160 16 16
    secondCoverageChunk10 secondCoverageChunk11) (@rangeCheck_append readyForThird 192 16 32
    secondCoverageChunk12 (@rangeCheck_append readyForThird 208 16 16
    secondCoverageChunk13 secondCoverageChunk14))) (@rangeCheck_append readyForThird 240 32 45
    (@rangeCheck_append readyForThird 240 16 16
    secondCoverageChunk15 secondCoverageChunk16) (@rangeCheck_append readyForThird 272 16 29
    secondCoverageChunk17 (@rangeCheck_append readyForThird 288 16 13
    secondCoverageChunk18 secondCoverageChunk19)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 16 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 31 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 46 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 54 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 58 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 60 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 70 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk8 : rangeCheck secondMixedTest 84 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk9 : rangeCheck secondMixedTest 92 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk10 : rangeCheck secondMixedTest 101 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk11 : rangeCheck secondMixedTest 116 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk12 : rangeCheck secondMixedTest 126 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk13 : rangeCheck secondMixedTest 134 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk14 : rangeCheck secondMixedTest 150 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk15 : rangeCheck secondMixedTest 159 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk16 : rangeCheck secondMixedTest 171 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk17 : rangeCheck secondMixedTest 178 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk18 : rangeCheck secondMixedTest 189 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk19 : rangeCheck secondMixedTest 201 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk20 : rangeCheck secondMixedTest 217 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk21 : rangeCheck secondMixedTest 229 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk22 : rangeCheck secondMixedTest 244 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk23 : rangeCheck secondMixedTest 259 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk24 : rangeCheck secondMixedTest 271 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk25 : rangeCheck secondMixedTest 285 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk26 : rangeCheck secondMixedTest 301 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk27 : rangeCheck secondMixedTest 314 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 secondCount = true := by
  exact (@rangeCheck_append secondMixedTest 0 150 167
    (@rangeCheck_append secondMixedTest 0 70 80
    (@rangeCheck_append secondMixedTest 0 46 24
    (@rangeCheck_append secondMixedTest 0 16 30
    secondMixedChunk0 (@rangeCheck_append secondMixedTest 16 15 15
    secondMixedChunk1 secondMixedChunk2)) (@rangeCheck_append secondMixedTest 46 12 12
    (@rangeCheck_append secondMixedTest 46 8 4
    secondMixedChunk3 secondMixedChunk4) (@rangeCheck_append secondMixedTest 58 2 10
    secondMixedChunk5 secondMixedChunk6))) (@rangeCheck_append secondMixedTest 70 31 49
    (@rangeCheck_append secondMixedTest 70 14 17
    secondMixedChunk7 (@rangeCheck_append secondMixedTest 84 8 9
    secondMixedChunk8 secondMixedChunk9)) (@rangeCheck_append secondMixedTest 101 25 24
    (@rangeCheck_append secondMixedTest 101 15 10
    secondMixedChunk10 secondMixedChunk11) (@rangeCheck_append secondMixedTest 126 8 16
    secondMixedChunk12 secondMixedChunk13)))) (@rangeCheck_append secondMixedTest 150 79 88
    (@rangeCheck_append secondMixedTest 150 28 51
    (@rangeCheck_append secondMixedTest 150 9 19
    secondMixedChunk14 (@rangeCheck_append secondMixedTest 159 12 7
    secondMixedChunk15 secondMixedChunk16)) (@rangeCheck_append secondMixedTest 178 23 28
    (@rangeCheck_append secondMixedTest 178 11 12
    secondMixedChunk17 secondMixedChunk18) (@rangeCheck_append secondMixedTest 201 16 12
    secondMixedChunk19 secondMixedChunk20))) (@rangeCheck_append secondMixedTest 229 42 46
    (@rangeCheck_append secondMixedTest 229 15 27
    secondMixedChunk21 (@rangeCheck_append secondMixedTest 244 15 12
    secondMixedChunk22 secondMixedChunk23)) (@rangeCheck_append secondMixedTest 271 30 16
    (@rangeCheck_append secondMixedTest 271 14 16
    secondMixedChunk24 secondMixedChunk25) (@rangeCheck_append secondMixedTest 301 13 3
    secondMixedChunk26 secondMixedChunk27)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 65 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 130 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 195 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 260 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 325 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 390 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 455 60 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 515 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 580 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 645 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 710 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 775 42 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 817 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 882 49 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 931 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 996 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk17 : rangeCheck thirdTest 1061 49 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk18 : rangeCheck thirdTest 1110 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk19 : rangeCheck thirdTest 1175 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk20 : rangeCheck thirdTest 1240 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk21 : rangeCheck thirdTest 1305 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk22 : rangeCheck thirdTest 1370 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk23 : rangeCheck thirdTest 1435 60 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk24 : rangeCheck thirdTest 1495 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk25 : rangeCheck thirdTest 1560 63 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk26 : rangeCheck thirdTest 1623 55 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk27 : rangeCheck thirdTest 1678 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk28 : rangeCheck thirdTest 1743 65 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk29 : rangeCheck thirdTest 1808 42 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk30 : rangeCheck thirdTest 1850 44 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 thirdCount = true := by
  exact (@rangeCheck_append thirdTest 0 931 963
    (@rangeCheck_append thirdTest 0 455 476
    (@rangeCheck_append thirdTest 0 195 260
    (@rangeCheck_append thirdTest 0 65 130
    thirdTailChunk0 (@rangeCheck_append thirdTest 65 65 65
    thirdTailChunk1 thirdTailChunk2)) (@rangeCheck_append thirdTest 195 130 130
    (@rangeCheck_append thirdTest 195 65 65
    thirdTailChunk3 thirdTailChunk4) (@rangeCheck_append thirdTest 325 65 65
    thirdTailChunk5 thirdTailChunk6))) (@rangeCheck_append thirdTest 455 255 221
    (@rangeCheck_append thirdTest 455 125 130
    (@rangeCheck_append thirdTest 455 60 65
    thirdTailChunk7 thirdTailChunk8) (@rangeCheck_append thirdTest 580 65 65
    thirdTailChunk9 thirdTailChunk10)) (@rangeCheck_append thirdTest 710 107 114
    (@rangeCheck_append thirdTest 710 65 42
    thirdTailChunk11 thirdTailChunk12) (@rangeCheck_append thirdTest 817 65 49
    thirdTailChunk13 thirdTailChunk14)))) (@rangeCheck_append thirdTest 931 504 459
    (@rangeCheck_append thirdTest 931 244 260
    (@rangeCheck_append thirdTest 931 130 114
    (@rangeCheck_append thirdTest 931 65 65
    thirdTailChunk15 thirdTailChunk16) (@rangeCheck_append thirdTest 1061 49 65
    thirdTailChunk17 thirdTailChunk18)) (@rangeCheck_append thirdTest 1175 130 130
    (@rangeCheck_append thirdTest 1175 65 65
    thirdTailChunk19 thirdTailChunk20) (@rangeCheck_append thirdTest 1305 65 65
    thirdTailChunk21 thirdTailChunk22))) (@rangeCheck_append thirdTest 1435 243 216
    (@rangeCheck_append thirdTest 1435 125 118
    (@rangeCheck_append thirdTest 1435 60 65
    thirdTailChunk23 thirdTailChunk24) (@rangeCheck_append thirdTest 1560 63 55
    thirdTailChunk25 thirdTailChunk26)) (@rangeCheck_append thirdTest 1678 130 86
    (@rangeCheck_append thirdTest 1678 65 65
    thirdTailChunk27 thirdTailChunk28) (@rangeCheck_append thirdTest 1808 42 44
    thirdTailChunk29 thirdTailChunk30)))))

def initialIndices (kind : Bool) : List ℕ := if kind then [1, 2, 4, 5, 7, 8, 9, 11, 12, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27] else [0, 3, 6, 10, 13, 21]

noncomputable def initialStates (kind : Bool) : List SearchState := (initialIndices kind).map firstAt

lemma allInitialIndices (kind : Bool) : (initialIndices kind).all (fun i => decide (i < firstCount)) = true := by
  cases kind <;> decide +kernel

lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) : chkPairPicked [] rootBounds 0 14 1 FF 0 kind = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : chk [] rootBounds 0 14 1 FF 0 = false :=
  chkPair_picked [] rootBounds 0 14 1 FF 0 binaryCertificate


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked0 : chkPicked [] rootBounds 0 14 1 0 1 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked1 : chkPicked [] rootBounds 0 14 1 0 1 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked2 : chkPicked [] rootBounds 0 14 1 0 1 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked3 : chkPicked [] rootBounds 0 14 1 0 1 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked4 : chkPicked [] rootBounds 0 14 1 0 1 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked5 : chkPicked [] rootBounds 0 14 1 0 1 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked6 : chkPicked [] rootBounds 0 14 1 0 1 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked7 : chkPicked [] rootBounds 0 14 1 0 1 7 = false := by decide +kernel

lemma unaryChecked : chk [] rootBounds 0 14 1 0 1 = false := by
  apply chk_picked
  intro b
  fin_cases b
  · exact unaryChecked0
  · exact unaryChecked1
  · exact unaryChecked2
  · exact unaryChecked3
  · exact unaryChecked4
  · exact unaryChecked5
  · exact unaryChecked6
  · exact unaryChecked7


def rootCases : List (ℕ × ℕ) := [(FF, 0), (0, 1)]

lemma rootCases_full : mFull rootCases = true := by decide +kernel

lemma certify_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rootBounds 0 14 1 p.1 p.2 = false := by
  refine ⟨rootCases, rootCases_full, ?_⟩
  intro p hp
  simp only [rootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3Pair : Lg I.NN (mz 0) (tz 0) 65 := by
  unfold Lg
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3Region : mz 8 &&& mz 0 = mz 8 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3Target : tz 8 ≠ 0 ∧ tz 8 ≠ mz 8 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3SeparatorsKilled : (rawL []).all (fun w =>
    !(sepb I.NN true (w &&& mz 0) 65) || Nat.beq ((w &&& mz 0) &&& mz 8) 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3SeparatorConstant {x : ℕ} (hin : x ∈ C (mz 0) (WZ [] 0))
    (hsep : sepb I.NN true x 65 = true) : Cst (mz 8) x := by
  rcases hin with h | h
  · obtain ⟨w, hw, rfl⟩ := h
    have hz := List.all_eq_true.mp x3SeparatorsKilled w hw
    simp only [hsep, Bool.not_true, Bool.false_or] at hz
    exact Or.inl (Nat.eq_of_beq_eq_true hz)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by rw [Nat.and_comm, x3Region])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x3ProjectedInputs {S : Finset ℕ} (hs : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) :
    C (mz 8) (Im (mz 8) S) ⊆ C (mz 8) (WZ [] 8) := by
  rintro x (⟨word, hw, rfl⟩ | hx)
  · rcases hs hw with h | h
    · obtain ⟨w, input, rfl⟩ := h
      exact Or.inl ⟨w, input, by
        change (w &&& mz 0) &&& mz 8 = w &&& mz 8
        rw [Nat.and_assoc, Nat.and_comm (mz 0), x3Region]⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact Or.inr (by simp)
      · apply Or.inr
        change mz 0 &&& mz 8 ∈ ({0, mz 8} : Set ℕ)
        rw [Nat.and_comm, x3Region]
        exact Set.mem_insert_of_mem _ rfl
  · exact Or.inr hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lower14 : Imp [] 0 14 := by
  intro q hq solution
  classical
  let existsSol : ∃ n, Sol Z0 (mz 0) (tz 0) n (C (mz 0) (WZ [] 0)) := ⟨q, solution⟩
  obtain ⟨k, hk, t, S, hS, live⟩ := (Nat.find_spec existsSol).live
  have leSize := le_trans hk (Nat.find_min' existsSol solution)
  have ambient : C (mz 0) (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have minimal : Min Z0 (mz 0) (tz 0) k t S :=
    ⟨live, fun n hn smaller => Nat.find_min existsSol (lt_of_lt_of_le hn hk) (smaller.mono le_rfl ambient)⟩
  obtain ⟨wire, hwire, separated⟩ := live.cov x3Pair.1 x3Pair.2.1 x3Pair.2.2.1 x3Pair.2.2.2
  have constant := x3SeparatorConstant (hS hwire) (sepb_weak (pos' t) separated)
  have killed : 0 < (S.filter (Cst (mz 8))).card :=
    Finset.card_pos.mpr ⟨wire, Finset.mem_filter.mpr ⟨hwire, constant⟩⟩
  obtain ⟨n, leaner, solved⟩ := minimal.const x3Region
    (by rw [tz_sub x3Region]; exact x3Target.1) (by rw [tz_sub x3Region]; exact x3Target.2)
  rw [tz_sub x3Region] at solved
  exact strongRow8 n (by omega) (solved.mono le_rfl (x3ProjectedInputs hS))

lemma needs15 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 14 1 S) : False := by
  have hmin : ∀ q < 14, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => lower14 q hq
  exact imp_of_live (L := 15) (Or.inl rfl) root_p (by norm_num) rootBounds_sound
    (by norm_num) hS hl hmin (Or.inr certify_1)

lemma onFinal : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfit hone hev
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 15 ≤ gates.length := by
      by_contra! hlt
      have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y :=
        fun y => (hev y).trans (f_graph y).symm
      by_cases hsmall : gates.length < 14
      · exact lower14 gates.length hsmall (bridge ⟨gates, o⟩ (fanInTwo_of hfit) hf)
      · have hsize : gates.length = 14 := by omega
        rcases bridge_not gates o (fanInTwo_of hfit) hone hnot hf with hsol | ⟨S, hS, hl⟩
        · exact lower14 (gates.length - 1) (by omega) hsol
        · rw [hsize] at hl
          exact needs15 hS hl
    exact ⟨witness.gates, witness.output, witness_basis, by rw [witness_size]; omega, witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    rcases hfit g hg with ⟨h | h | h, hl⟩
    · exact ⟨Or.inl h, hl⟩
    · exact ⟨Or.inr h, hl⟩
    · exact (hnot ⟨g, hg, h⟩).elim

end inst_data
end PEqualNP.Outside.L_meta_51640_aux

theorem PEqualNP.Outside.L_meta_51640 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_51640_aux.onFinal
