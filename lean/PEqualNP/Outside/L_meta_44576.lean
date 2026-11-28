import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44576_aux

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
  rawP_len : I.rawP.length = 6


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
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
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
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)) b d
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
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end coreC

def bigNat_0 : Nat := ([0, 18444210790328942591, 18122483800984256475, 13175139967468305919, 18158491398085238779, 18365116291540301567, 18374682081289563583, 63] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_1 : Nat := ([0, 2533283380609024, 324260272725295140, 5271604106241245696, 4] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_2 : Nat := ([0, 0, 0, 0, 288252675624312832, 81627782169250048, 72061992419988032, 64] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_3 : Nat := ([12297829382473034410, 1688858449919999, 18086457202970722328, 438960218026541567, 4276414916963030296, 5052384779410179732, 5058977056999892155, 13, 5982636339709990656, 9325833172617088026, 108638367416321977, 18442271259898150913, 1080855148831637505, 8191] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_4 : Nat := ([14757395258967641292, 18444210781739532287, 252199380126269467, 3514778037457517568, 15610430215582927464, 11151002641006243946, 11117817006406609197, 18, 12904198494524631808, 9923139069012231251, 2560624184684979401, 496978922307592, 6917529061998231548, 562881233952767] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_5 : Nat := ([17361641481138401520, 1970316246745088, 252200479578128320, 9281918835634470912, 8159898006344893363, 17024765909986120271, 17069681689620300161, 32, 15071643952900354560, 10817131993658802336, 5193229178005377128, 18443370771725156544, 481036369917, 9222246145536868352] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_6 : Nat := ([18374966859414961920, 18442240474082426879, 17870283321430245339, 13114482118577094143, 11082914149963943115, 3641555669850038387, 3642508519614393358, 59, 16161783626622745600, 2618923107099052332, 9654177235507568, 18443885343477334355, 72052096479821821, 8589279232, 8191] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_7 : Nat := ([18446462603027742720, 18444210790328696832, 24117211, 13175139963794096128, 16289389028015935731, 4328390142755550851, 4391277658936426544, 60, 176696910916927488, 4062370834482466255, 7691145410835964288, 411, 72052611873439744, 9222809035361746944, 8191] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_8 : Nat := ([18446744069414584320, 0, 18122483800960139264, 13175139967468305919, 283729146810605315, 13897536704283149564, 13906838555411090879, 63, 34903962266042368, 4575796859515175408, 7728036538742799873, 474, 7926335344172072960, 9222809043951083519, 8191] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_9 : Nat := ([] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_10 : Nat := ([] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_11 : Nat := ([18368756680266647552, 18444210790328942591, 18122483800984256475, 13175139967468305919, 18158491398085238779, 18365116291540301567, 18374682081289563583, 63] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def NN0 : Nat := 455
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 78), (78, 82), (82, 97), (97, 112), (112, 115), (115, 130), (130, 133), (133, 148), (148, 151), (151, 153), (153, 168), (168, 183), (183, 186), (186, 201), (201, 216), (216, 218), (218, 221), (221, 224), (224, 239), (239, 243), (243, 245), (245, 248), (248, 251), (251, 254), (254, 258)]
def segsY0 : List (ℕ × ℕ) := [(258, 269), (269, 271), (271, 274), (274, 277), (277, 291), (291, 294), (294, 298), (298, 300), (300, 314), (314, 328), (328, 331), (331, 334), (334, 348), (348, 352), (352, 355), (355, 369), (369, 373), (373, 376), (376, 390), (390, 393), (393, 396), (396, 410), (410, 412), (412, 426), (426, 440), (440, 454)]
def rawP0 : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8]
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
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
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
  simp only [cv, cvC, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
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
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
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
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
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
def kz (Z : ℕ) : ℕ := (List.range 6).foldr (fun i x =>
  let a := I.rawP.getD i 0
  let b := Nat.shiftRight a I.NN
  let z0 := if Z.testBit i then Nat.land (Nat.lor a b) FULL else 0
  let z1 := if Z.testBit (i + 6) then Nat.lor (Nat.land (Nat.xor a FULL) FULL) (Nat.land (Nat.xor b FULL) I.AA) else 0
  Nat.lor x (Nat.lor z0 z1)) 0
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

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length t S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg hnot hT
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
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have go := ex_sol m gs (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hT
        obtain ⟨k, hk, t, S1, hS1, hl1⟩ := go.live
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) (t + 1) (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨t + 1, by omega, _, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))


section inst_data
def row3g0 : List (ℕ × ℕ) := [(14, 2), (21, 2), (22, 2), (25, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g0ok : row3g0.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g1 : List (ℕ × ℕ) := [(26, 2), (35, 2), (37, 2), (41, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g1ok : row3g1.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g2 : List (ℕ × ℕ) := [(42, 2), (52, 2), (70, 2), (74, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g2ok : row3g2.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g3 : List (ℕ × ℕ) := [(76, 1), (82, 2), (84, 2), (88, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g3ok : row3g3.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g4 : List (ℕ × ℕ) := [(98, 1), (100, 1), (104, 1), (112, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g4ok : row3g4.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g5 : List (ℕ × ℕ) := [(133, 2), (137, 2), (140, 2), (145, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g5ok : row3g5.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g6 : List (ℕ × ℕ) := [(148, 2), (152, 1), (161, 2), (164, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g6ok : row3g6.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g7 : List (ℕ × ℕ) := [(168, 1), (176, 1), (196, 2), (200, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g7ok : row3g7.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g8 : List (ℕ × ℕ) := [(208, 2), (224, 2), (259, 1), (265, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g8ok : row3g8.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g9 : List (ℕ × ℕ) := [(266, 2), (273, 1), (274, 1), (280, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g9ok : row3g9.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g10 : List (ℕ × ℕ) := [(289, 2), (290, 2), (296, 2), (304, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g10ok : row3g10.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g11 : List (ℕ × ℕ) := [(322, 1), (328, 1), (336, 2), (352, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g11ok : row3g11.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g12 : List (ℕ × ℕ) := [(385, 1), (392, 1), (400, 2), (416, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g12ok : row3g12.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g13 : List (ℕ × ℕ) := [(448, 2), (515, 1), (517, 2), (518, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g13ok : row3g13.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g14 : List (ℕ × ℕ) := [(529, 1), (530, 1), (532, 4), (545, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g14ok : row3g14.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g15 : List (ℕ × ℕ) := [(546, 1), (548, 2), (560, 1), (578, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g15ok : row3g15.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g16 : List (ℕ × ℕ) := [(580, 1), (592, 1), (608, 2), (641, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g16ok : row3g16.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g17 : List (ℕ × ℕ) := [(644, 2), (656, 1), (672, 1), (769, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g17ok : row3g17.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g18 : List (ℕ × ℕ) := [(770, 2), (784, 4), (800, 2), (832, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g18ok : row3g18.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g19 : List (ℕ × ℕ) := [(896, 2), (1027, 1), (1029, 1), (1030, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g19ok : row3g19.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g20 : List (ℕ × ℕ) := [(1033, 1), (1034, 2), (1036, 1), (1057, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g20ok : row3g20.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g21 : List (ℕ × ℕ) := [(1058, 2), (1060, 1), (1064, 2), (1090, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g21ok : row3g21.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g22 : List (ℕ × ℕ) := [(1092, 2), (1096, 1), (1120, 2), (1153, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g22ok : row3g22.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g23 : List (ℕ × ℕ) := [(1156, 2), (1160, 2), (1184, 1), (1216, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g23ok : row3g23.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g24 : List (ℕ × ℕ) := [(1281, 1), (1282, 1), (1288, 1), (1312, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g24ok : row3g24.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g25 : List (ℕ × ℕ) := [(1537, 1), (1538, 2), (1540, 2), (1568, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g25ok : row3g25.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g26 : List (ℕ × ℕ) := [(1600, 2), (2051, 2), (2053, 1), (2054, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g26ok : row3g26.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g27 : List (ℕ × ℕ) := [(2057, 1), (2058, 2), (2060, 1), (2065, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g27ok : row3g27.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g28 : List (ℕ × ℕ) := [(2066, 2), (2068, 2), (2072, 2), (2114, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g28ok : row3g28.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g29 : List (ℕ × ℕ) := [(2116, 1), (2120, 1), (2128, 1), (2177, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g29ok : row3g29.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g30 : List (ℕ × ℕ) := [(2180, 2), (2184, 2), (2192, 1), (2240, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g30ok : row3g30.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g31 : List (ℕ × ℕ) := [(2305, 2), (2306, 2), (2312, 1), (2320, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g31ok : row3g31.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g32 : List (ℕ × ℕ) := [(2561, 2), (2562, 2), (2564, 1), (2576, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g32ok : row3g32.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g33 : List (ℕ × ℕ) := [(2816, 2), (3073, 4), (3074, 2), (3076, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g33ok : row3g33.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g34 : List (ℕ × ℕ) := [(3080, 2), (3200, 2), (3328, 2), (3584, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g34ok : row3g34.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def rt3 : List (ℕ × ℕ) := row3g0 ++ row3g1 ++ row3g2 ++ row3g3 ++ row3g4 ++ row3g5 ++ row3g6 ++ row3g7 ++ row3g8 ++ row3g9 ++ row3g10 ++ row3g11 ++ row3g12 ++ row3g13 ++ row3g14 ++ row3g15 ++ row3g16 ++ row3g17 ++ row3g18 ++ row3g19 ++ row3g20 ++ row3g21 ++ row3g22 ++ row3g23 ++ row3g24 ++ row3g25 ++ row3g26 ++ row3g27 ++ row3g28 ++ row3g29 ++ row3g30 ++ row3g31 ++ row3g32 ++ row3g33 ++ row3g34
lemma r3 : rt3.all (fun e => okE [] (pr ([]) e.1) e) = true := by
  simp only [rt3, List.all_append, Bool.and_true, row3g0ok, row3g1ok, row3g2ok, row3g3ok, row3g4ok, row3g5ok, row3g6ok, row3g7ok, row3g8ok, row3g9ok, row3g10ok, row3g11ok, row3g12ok, row3g13ok, row3g14ok, row3g15ok, row3g16ok, row3g17ok, row3g18ok, row3g19ok, row3g20ok, row3g21ok, row3g22ok, row3g23ok, row3g24ok, row3g25ok, row3g26ok, row3g27ok, row3g28ok, row3g29ok, row3g30ok, row3g31ok, row3g32ok, row3g33ok, row3g34ok]
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll r3 (by simp)
def row2g0 : List (ℕ × ℕ) := [(3, 2), (5, 3), (6, 3), (9, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g0ok : row2g0.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g1 : List (ℕ × ℕ) := [(10, 5), (12, 2), (17, 3), (18, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g1ok : row2g1.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g2 : List (ℕ × ℕ) := [(20, 5), (24, 3), (33, 5), (34, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g2ok : row2g2.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g3 : List (ℕ × ℕ) := [(36, 3), (40, 3), (48, 2), (66, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g3ok : row2g3.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g4 : List (ℕ × ℕ) := [(68, 4), (72, 4), (80, 4), (96, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g4ok : row2g4.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g5 : List (ℕ × ℕ) := [(129, 3), (132, 6), (136, 5), (144, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g5ok : row2g5.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g6 : List (ℕ × ℕ) := [(160, 4), (192, 5), (257, 4), (258, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g6ok : row2g6.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g7 : List (ℕ × ℕ) := [(264, 3), (272, 5), (288, 6), (320, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g7ok : row2g7.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g8 : List (ℕ × ℕ) := [(384, 3), (513, 4), (514, 3), (516, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g8ok : row2g8.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g9 : List (ℕ × ℕ) := [(528, 4), (544, 4), (576, 3), (640, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g9ok : row2g9.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g10 : List (ℕ × ℕ) := [(768, 5), (1025, 4), (1026, 4), (1028, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g10ok : row2g10.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g11 : List (ℕ × ℕ) := [(1032, 4), (1056, 5), (1088, 3), (1152, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g11ok : row2g11.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g12 : List (ℕ × ℕ) := [(1280, 2), (1536, 3), (2049, 5), (2050, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g12ok : row2g12.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g13 : List (ℕ × ℕ) := [(2052, 4), (2056, 4), (2064, 3), (2112, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g13ok : row2g13.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g14 : List (ℕ × ℕ) := [(2176, 3), (2304, 3), (2560, 3), (3072, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g14ok : row2g14.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def rt2 : List (ℕ × ℕ) := row2g0 ++ row2g1 ++ row2g2 ++ row2g3 ++ row2g4 ++ row2g5 ++ row2g6 ++ row2g7 ++ row2g8 ++ row2g9 ++ row2g10 ++ row2g11 ++ row2g12 ++ row2g13 ++ row2g14
lemma r2 : rt2.all (fun e => okE [] (pr (rt3) e.1) e) = true := by
  simp only [rt2, List.all_append, Bool.and_true, row2g0ok, row2g1ok, row2g2ok, row2g3ok, row2g4ok, row2g5ok, row2g6ok, row2g7ok, row2g8ok, row2g9ok, row2g10ok, row2g11ok, row2g12ok, row2g13ok, row2g14ok]
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 (i3)
def row1g0 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g0ok : row1g0.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def row1g1 : List (ℕ × ℕ) := [(16, 7), (32, 7), (64, 7), (128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g1ok : row1g1.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def row1g2 : List (ℕ × ℕ) := [(256, 7), (512, 7), (1024, 7), (2048, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g2ok : row1g2.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def rt1 : List (ℕ × ℕ) := row1g0 ++ row1g1 ++ row1g2
lemma r1 : rt1.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by
  simp only [rt1, List.all_append, Bool.and_true, row1g0ok, row1g1ok, row1g2ok]
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := okAll r1 (apI i3 i2)
def rt : List (ℕ × ℕ) := (rt3 ++ rt2 ++ rt1).filter (fun e => Nat.ble 4 e.2)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := fun e he => (apI (apI i3 i2) i1) e (List.mem_of_mem_filter he)
def memoCell (width shift : ℕ) : ℕ := Nat.land FF (Nat.shiftLeft (2 ^ width - 1) shift)
noncomputable section memo_data
def memoIter {α : Type} (base : α) (step : α → α) (wrap : Nat → α → α) : Nat → α
  | 0 => base
  | n + 1 => wrap (n + 1) (step (memoIter base step wrap n))

lemma memoIter_eq {α : Type} (base : α) (step : α → α) (wrap : Nat → α → α)
    (hw : ∀ n, wrap n (Nat.rec base (fun _ => step) n) = Nat.rec base (fun _ => step) n) :
    ∀ n, memoIter base step wrap n = Nat.rec base (fun _ => step) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memoIter, ih]
    exact hw (n + 1)

lemma subtypeList_sound {α : Type} {p : α → Prop} (xs : List {x : α // p x}) :
    ∀ x ∈ xs.map Subtype.val, p x := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact a.property

lemma checkedChunks_sound {α : Type} (F : α → Bool)
    (chunks : List {xs : List α // xs.all (fun x => !(F x)) = true}) :
    ∀ x ∈ (chunks.map Subtype.val).flatten, F x = false := by
  intro x hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hxs
  have hf := List.all_eq_true.mp a.property x hx
  cases h : F x <;> simp_all


abbrev Runner := Nat → Nat → Nat → List W → Bool
abbrev WireKey := Nat × Nat × Nat × Nat × Nat
abbrev MemoKey := Nat × Nat × Nat × Nat × List WireKey

def packW (v : List W) : List WireKey := v.map (fun w => (w.s,w.a,w.b,w.c,w.r))
def unpackW (v : List WireKey) : List W := v.map (fun (s,a,b,c,r) => ⟨s,a,b,c,r⟩)
lemma unpack_pack (v : List W) : unpackW (packW v) = v := by
  induction v with
  | nil => rfl
  | cons w v ih => cases w; simpa only [packW,unpackW,List.map_cons] using congrArg (List.cons _) ih

def keyRun (run : Nat → Runner) (e : MemoKey) : Bool :=
  run e.1 e.2.1 e.2.2.1 e.2.2.2.1 (unpackW e.2.2.2.2)
def memoWrap (keys : List MemoKey) (fuel : Nat) (run : Runner) : Runner :=
  fun k t z v => if k = 10 then if keys.contains (fuel,k,t,z,packW v) then false else run k t z v else run k t z v
lemma memoWrap_eq (keys : List MemoKey) (run : Nat → Runner)
    (h : ∀ e ∈ keys, keyRun run e = false) (fuel : Nat) : memoWrap keys fuel (run fuel) = run fuel := by
  funext k t z v
  unfold memoWrap
  split_ifs with hk hm
  · have he := h (fuel,k,t,z,packW v) (List.contains_iff_mem.mp hm)
    simpa only [keyRun,unpack_pack] using he.symm
  · rfl
  · rfl

def memoStepC (NN AA HX HY l m g : Nat) (ih : Runner) : Runner := fun k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)

def memoStepS (NN AA HX HY l m g K : Nat) (baseRun : Nat → Runner) (ih : Runner) : Runner := fun k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (baseRun K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)

def memoLookC (NN AA HX HY l m g : Nat) (keys : List MemoKey) : Nat → Runner :=
  memoIter (fun _ _ _ _ => true) (memoStepC NN AA HX HY l m g) (memoWrap keys)
lemma memoLookC_eq (NN AA HX HY l m g : Nat) (keys : List MemoKey)
    (h : ∀ e ∈ keys, keyRun (lookC NN AA HX HY l m g) e = false) :
    memoLookC NN AA HX HY l m g keys = lookC NN AA HX HY l m g := by
  funext fuel
  apply memoIter_eq
  intro n
  exact memoWrap_eq keys (lookC NN AA HX HY l m g) h n

def memoLookS (NN AA HX HY l m g K : Nat) (keysC keysS : List MemoKey) : Nat → Runner :=
  memoIter (fun _ _ _ _ => true)
    (memoStepS NN AA HX HY l m g K (memoLookC NN AA HX HY l m g keysC)) (memoWrap keysS)
lemma memoLookS_eq (NN AA HX HY l m g K : Nat) (keysC keysS : List MemoKey)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoLookS NN AA HX HY l m g K keysC keysS = look1C NN AA HX HY l m g K := by
  unfold memoLookS
  rw [memoLookC_eq NN AA HX HY l m g keysC hC]
  funext fuel
  apply memoIter_eq
  intro n
  exact memoWrap_eq keysS (look1C NN AA HX HY l m g K) hS n
def memoNat (xs : List Nat) : Nat := xs.foldr (fun x a => x + 18446744073709551616 * a) 0
def mn6 : Nat := memoNat [18374966859414961920,18442240474082426879,17870283321430245339,13114482118577094143,11082914149963943115,3641555669850038387,3642508519614393358,59,16161783626622745600,2618923107099052332,9654177235507568,18443885343477334355,72052096479821821,8589279232,8191]
def mn7 : Nat := memoNat [36028798092705825,64,4398046642176,8]
def mn8 : Nat := memoNat [33792,2380222771809484800,4,8589934592]
def mn9 : Nat := mn8 + (memoNat [36028798092705825,64,4398046642176,8])
def mn10 : Nat := (memoNat [1085102592571150095,123144765421568,15762529973633020,4038884441047695360,17803816194499260475,2216969373980979492,1066855105601268760,2,941977747056272160,9899442786458450954,324576823625336070,16140690233121832972,30064773119,576390384096054272]) * 2 ^ 4
def mn11 : Nat := memoNat [1125934266582016,2251799813685250,4611686155866341376]
def mn12 : Nat := memoNat [32768,2269957324800,4,268435456]
def mn13 : Nat := mn11 + (memoNat [32768,2269957324800,4,268435456])
def mn14 : Nat := memoNat [14757395258967641292,18444210781739532287,252199380126269467,3514778037457517568,15610430215582927464,11151002641006243946,11117817006406609197,18,12904198494524631808,9923139069012231251,2560624184684979401,496978922307592,6917529061998231548,562881233952767]
def mn15 : Nat := memoNat [35185445830657,2147483648,144115192370827264]
def mn16 : Nat := memoNat [32,2164802,0,8388608]
def mn17 : Nat := mn15 + (memoNat [32,2164802,0,8388608])
def mn18 : Nat := memoNat [12297829382473034410,1688858449919999,18086457202970722328,438960218026541567,4276414916963030296,5052384779410179732,5058977056999892155,13,5982636339709990656,9325833172617088026,108638367416321977,18442271259898150913,1080855148831637505,8191]
def mn19 : Nat := memoNat [1099546230784,70368811286528,4503599761588352]
def mn20 : Nat := memoNat [1190111385904742433,2097152,0,262144]
def mn21 : Nat := mn19 + (memoNat [1190111385904742433,2097152,0,262144])
def mn22 : Nat := memoNat [18446744069414584320,0,18122483800960139264,13175139967468305919,283729146810605315,13897536704283149564,13906838555411090879,63,34903962266042368,4575796859515175408,7728036538742799873,474,7926335344172072960,9222809043951083519,8191]
def mn23 : Nat := memoNat [1099512676352,2305845208237015040,4194304,8192]
def mn24 : Nat := (memoNat [1,0,4329604,262144]) * 2 ^ 25
def mn25 : Nat := mn23 + ((memoNat [1,0,4329604,262144]) * 2 ^ 25)
def mn26 : Nat := mn22 - (memoNat [281466386841600,2533283380854784,18122483800936022052,3674209791,2441084192504221200,9569146561527598712,9515560896474664335,3,18304951125058666496,513426025032709152,36891127906835585,63,7854282732298633216,8589336575])
def mn27 : Nat := memoNat [1152921538966619136,72057662757406720,0,256]
def mn28 : Nat := memoNat [34603008,0,140737492684928,274877906944]
def mn29 : Nat := mn27 + (memoNat [34603008,0,140737492684928,274877906944])
def mn481 : Nat := memoNat [5429849789371633333,10713400762927719785,2975140555994516054,163454817292965]
def mn482 : Nat := mn481 - (memoNat [1099546230784,2305845208237015040,145277407199232,8796093030400])
def mn483 : Nat := memoNat [4276928250370411189,10641343100170313065,2974999818501831126,163179939385765]
def mn484 : Nat := mn483 - (memoNat [1099546230784,2305845208237015040,145277407199232,8796093030400])
def mn485 : Nat := memoNat [5357789994127280755,6027330583857898729,2974995420451134162,163721105248917]
def mn486 : Nat := mn484 + (memoNat [1116892740874894303,16064199202061682624,4333815,532575944952])
def mn487 : Nat := memoNat [5427595721779529397,6097206675892249957,12198371717913729746,163729426748068]
def mn488 : Nat := memoNat [5428722755525200565,8405301413985625447,16809912596381260494,154933065298596]
def mn489 : Nat := mn487 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn490 : Nat := mn488 + (memoNat [1090748820816831,2254138553331582,4467570830351527944,520093696])
def mn491 : Nat := memoNat [4239736204374429332,6101569608829019497,2965992619108948438,163729694921381]
def mn492 : Nat := memoNat [3049624818469686899,8407485185875223913,2970350941471726166,154933601645221]
def mn493 : Nat := memoNat [3051949115218380403,8261120259641349353,2974995562323462738,172242320380053]
def mn494 : Nat := mn486 + (memoNat [17293823634253545472,2130303842303,4681778454272,17042430238464])
def mn495 : Nat := memoNat [3121754911590106805,10564779636547687781,12198376120393484882,172250641879204]
def mn496 : Nat := memoNat [4275802316069193397,10639086829161454951,16809921538767141326,171975495537060]
def mn497 : Nat := mn495 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn498 : Nat := mn496 + (memoNat [1090748820784063,2256268857046910,4467570963495518216,520093696])
def mn499 : Nat := memoNat [3086814631048038036,10569144699788236137,2965997158893439446,172250910052517]
def mn500 : Nat := mn492 + (memoNat [1065151855616,2233787545479608320,9079690616704,17042430238464])
def mn501 : Nat := memoNat [5355540324652992115,8330923921347224805,12198508061792885454,172516929852052]
def mn502 : Nat := memoNat [5392695057012278932,5952950679394100519,16810198615705869006,172508071482012]
def mn503 : Nat := mn501 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn504 : Nat := mn502 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn505 : Nat := memoNat [4203707405207947891,8333107622237742313,2966129100292839890,172517198025365]
def mn506 : Nat := mn504 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn507 : Nat := memoNat [5427527549946775187,10708894891193376037,11910286473144515282,172525511398052]
def mn508 : Nat := memoNat [5428688669659155060,10711144423195055333,16666087821381683918,172525234573988]
def mn509 : Nat := memoNat [4238610235748075156,10708754155785463141,12189509658362993106,172525519524516]
def mn510 : Nat := mn500 + (memoNat [34570240,69801323096180734,13835339392828579960,549218943231])
def mn511 : Nat := mn509 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn512 : Nat := mn506 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn513 : Nat := mn505 + (memoNat [1162149498978304,68101137692672,9007199518982400,253696])
def mn514 : Nat := mn513 - (memoNat [1152922638512849920,2377902870994421760,140737492549632,8448])
def mn515 : Nat := mn504 + (memoNat [35185412310049,2377900605403435076,143974454882471936,16777216])
def mn516 : Nat := mn515 - (memoNat [1152922638512849920,2377902870994421760,140737492549632,8448])
def mn517 : Nat := mn509 + (memoNat [36065115330577441,16068984208015423488,9007199518982399,253696])
def mn518 : Nat := mn517 - (memoNat [1152922638512849920,2377902870994421760,140737492549632,8448])
def mn519 : Nat := mn508 + (memoNat [35185412309057,2267747061890,143974454882471936,16777216])
def mn520 : Nat := mn519 - (memoNat [1152922638512849920,2377902870994421760,140737492549632,8448])
def mn521 : Nat := mn511 + (memoNat [37155762145819680,16068981940339867648,9007199518982399,253696])
def mn522 : Nat := mn521 - (memoNat [1152922638512849920,2377902870994421760,140737492549632,8448])
def mn523 : Nat := mn508 + (memoNat [1125934233093120,2256337580918784,4611545418377986056,536870912])
def mn524 : Nat := Nat.xor mn521 (memoNat [246298187923687,2162231746,144396675937497088,8388608])
def mn525 : Nat := mn511 + (memoNat [36251706031137,16068841207012261954,288230384737460223,8380160])
def mn526 : Nat := Nat.xor mn499 (memoNat [0,13835062453329068032,12718080,274877923328])
def mn527 : Nat := mn511 + (memoNat [18409590478477459456,70373106321473,292593247014887552,8126464])
def mn528 : Nat := mn527 - (memoNat [1152922638512849920,2377902870994421760,140737492549632,8448])
def mn529 : Nat := mn482 - (memoNat [17365880130929426498,2322099838384255,4398050967556,8589934352])
def mn530 : Nat := memoNat [6546742530177321620,8330855891279850793,2974850001184180814,145845451379613]
def mn531 : Nat := memoNat [6580518360257776309,8475109546886671717,12198367177998944850,154658455827364]
def mn532 : Nat := memoNat [6581646493549678261,13089049493217062247,16810053333873674830,154658187408292]
def mn533 : Nat := mn532 - (memoNat [1099546230784,2305845208237015040,145277407199232,8796093030400])
def mn534 : Nat := mn531 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn535 : Nat := mn533 + (memoNat [1090748820816831,2254138553331582,4467570830351527944,520093696])
def mn536 : Nat := mn481 - (memoNat [37189846972726305,18374827148576815104,9007199393153279,261888])
def mn537 : Nat := mn482 - (memoNat [37189846972726305,18374827148576815104,9007199393153279,261888])
def mn538 : Nat := memoNat [4202547456947933811,10785388056869645673,2970346401556941270,145862630724517]
def mn539 : Nat := mn483 - (memoNat [72056496673783874,2319969534541952,8796093153284,8589926416])
def mn540 : Nat := mn486 + (memoNat [2199022240768,2377905001298264064,141863669376,7971459317760])
def mn541 : Nat := mn483 - ((memoNat [37153597481289727,4611686018492403712,4503462196805632]) * 2 ^ 40)
def mn542 : Nat := mn488 + (memoNat [2199022239744,4611688286170251264,4402471095936,7971459317760])
def mn543 : Nat := mn483 - (memoNat [69271380033570,16140898869769666626,288230384741650431,8380416])
def mn544 : Nat := mn490 + (memoNat [2199022206976,4611690416473966592,4535615086208,7971459317760])
def mn545 : Nat := mn525 - (memoNat [34603008,13835053657235521536,145277403275391,9345848819712])
def mn546 : Nat := mn538 + (memoNat [1065151855616,2233787545479608320,9079690616704,17042430238464])
def mn547 : Nat := memoNat [6508462963131239027,10708826792341646565,12198503521878100558,163445958931348]
def mn548 : Nat := memoNat [6545617695490525844,8330853550388522279,16810194075791084110,163437100561308]
def mn549 : Nat := mn547 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn550 : Nat := mn548 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn551 : Nat := mn536 - (memoNat [36029898712712225,74307194828292224,8796223307780,8589926416])
def mn552 : Nat := mn550 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn553 : Nat := memoNat [6580450188425022099,13086797762187797797,11910281933229730386,163454540477348]
def mn554 : Nat := memoNat [6581611308137401972,13089047294189477093,16666083281466899022,163454263653284]
def mn555 : Nat := memoNat [5391532874226322068,13086657026779884901,12189505118448208210,163454548603812]
def mn556 : Nat := mn546 + (memoNat [34570240,69801323096180734,13835339392828579960,549218943231])
def mn557 : Nat := mn536 - (memoNat [36286065803297,16140898869769668674,288230384871677951,8380416])
def mn558 : Nat := mn556 + (memoNat [33286063104,2256337513607038,4467570963495514120,520093696])
def mn559 : Nat := mn549 + (memoNat [70368744177664,4297132034,288234782788296704,8388608])
def mn560 : Nat := mn559 - (memoNat [34603008,0,145277407334528,9070970929152])
def mn561 : Nat := mn530 + (memoNat [1099545182208,2199023321088,145277403000704,8521215123456])
def mn562 : Nat := mn561 - (memoNat [34603008,0,145277407334528,9070970929152])
def mn563 : Nat := mn532 + (memoNat [33619968,2340891394048,145277403004936,8796629893120])
def mn564 : Nat := mn563 - (memoNat [34603008,0,145277407334528,9070970929152])
def mn565 : Nat := mn553 + (memoNat [70370891661346,2149648448,288230522180608000,8388608])
def mn566 : Nat := mn565 - (memoNat [34603008,0,145277407334528,9070970929152])
def mn567 : Nat := mn564 - (memoNat [65536,4539914649600,8,536870912])
def mn568 : Nat := mn532 - ((memoNat [17,2380152403066355712,69273668,4456448]) * 2 ^ 21)
def mn569 : Nat := mn557 + (memoNat [1190078400625115168,140737624670208,9007203818148096,262144])
def mn570 : Nat := Nat.xor mn534 (memoNat [6597072912384,13835062453329133568,13501312,824633737216])
def mn571 : Nat := Nat.xor mn570 (memoNat [246298120814823,2162637250,144115192370827264,8388608])
def mn572 : Nat := Nat.xor mn535 (memoNat [7696584540160,2305845208236949504,13374208,549755822080])
def mn573 : Nat := mn536 + ((memoNat [1099511627775,70370893758466,137438953472]) * 2 ^ 40)
def mn574 : Nat := mn573 - (memoNat [34603008,0,145277407334528,9070970929152])
def mn575 : Nat := mn484 - (memoNat [74378594330015810,13691008700536188928,4362862134820863,507392])
def mn576 : Nat := mn575 - (memoNat [34603008,0,145277407334528,9070970929152])
def mn577 : Nat := mn481 + (memoNat [2233785481747759038,18442099874032783232,8439,532575945200])
def mn578 : Nat := mn482 + (memoNat [2233785481747759038,18442099874032783232,8439,532575945200])
def mn579 : Nat := mn577 - (memoNat [36028798092739617,2380222771809484864,4398046642180,8589934600])
def mn580 : Nat := mn529 + (memoNat [1116892740874894303,16064199202061682624,4333815,532575944952])
def mn581 : Nat := mn501 - (memoNat [16140903194801667072,2163981682535952383,4437438336,8521215131136])
def mn582 : Nat := memoNat [7662508237306547827,8475036976904647911,16810048935822977866,155199353271444]
def mn583 : Nat := mn581 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn584 : Nat := mn582 + (memoNat [1090748820816831,2254138553331582,4467570830351527944,520093696])
def mn585 : Nat := memoNat [6473521686155776594,6171305171748041961,2966128958550665810,163995982894229]
def mn586 : Nat := memoNat [5283410300251034161,8477220748794246377,2970487280913443538,155199889618069]
def mn587 : Nat := mn515 - (memoNat [108086394245611619,192,18446612132318674944,23])
def mn588 : Nat := mn493 - (memoNat [15024008254903516193,2238429546133055551,4325384,17179868424])
def mn589 : Nat := mn501 + (memoNat [68718461952,2303591278119485440,4398042316800])
def mn590 : Nat := mn519 - (memoNat [17365880130930475074,2324298861639807,4398055297156,283467841296])
def mn591 : Nat := Nat.xor mn503 (memoNat [2148532258,16140901064495872064,30786329800704])
def mn592 : Nat := mn590 + (memoNat [1090748820784063,2256268857046910,4467570963495518216,520093696])
def mn593 : Nat := mn505 + (memoNat [1116892707621437407,2305772640469516288,4398042316928])
def mn594 : Nat := mn527 - (memoNat [17365880130929426498,2322099838384255,4398055297028,283467841296])
def mn595 : Nat := memoNat [7589325806434339377,8400659484266247269,12198644401234602826,172783217824900]
def mn596 : Nat := Nat.xor mn579 ((memoNat [7696682058759,68719620228,962102034588,262192]) * 2 ^ 25)
def mn597 : Nat := mn595 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn598 : Nat := memoNat [7627571287614376497,6022690780075959397,2831161844933548874,172774879548557]
def mn599 : Nat := memoNat [6437492886989295153,8402843185156764777,2966265439734557262,172783485998213]
def mn600 : Nat := mn598 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn601 : Nat := memoNat [7661313031728122449,10778630454112398501,11910422812586232654,172791799370900]
def mn602 : Nat := memoNat [7662474151440502322,10780879986114077797,16666224160823401290,172791522546836]
def mn603 : Nat := memoNat [6472395717529422418,10778489718704485605,12189645997804710478,172791807497364]
def mn604 : Nat := mn510 + (memoNat [2233785481781347262,69735562919022464,136339441717372,266287972848])
def mn605 : Nat := mn603 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn606 : Nat := mn600 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn607 : Nat := mn513 + (memoNat [1116892740873879519,68719478720,0,248])
def mn608 : Nat := mn607 - (memoNat [36029897605382177,2305845208237015104,4398050836480,8200])
def mn609 : Nat := mn493 + (memoNat [3458764616899823616,2449958403447986176,4398046511104,768])
def mn610 : Nat := mn588 + (memoNat [18446742974197957632,2382542741344026623,8,17179860992])
def mn611 : Nat := mn595 + (memoNat [36027698580062241,72127962782040128,4398042447876,8589926408])
def mn612 : Nat := mn611 - (memoNat [36029897605382177,2305845208237015104,4398050836480,8200])
def mn613 : Nat := mn602 + (memoNat [35185445830721,2199027585154,144115192370827264,16777216])
def mn614 : Nat := mn613 - (memoNat [36029897605382177,2305845208237015104,4398050836480,8200])
def mn615 : Nat := mn597 + (memoNat [36027698580063265,74377563572535360,4398042447876,8589926408])
def mn616 : Nat := mn615 - (memoNat [36029897605382177,2305845208237015104,4398050836480,8200])
def mn617 : Nat := mn606 + (memoNat [2380188686983626785,70368811352128,4503599761588352,524288])
def mn618 : Nat := Nat.xor mn584 (memoNat [252201582555299843,0,849661301489664,17592186044440])
def mn619 : Nat := mn599 + (memoNat [36029897605415969,74307194828292160,4398042447876,8589926408])
def mn620 : Nat := Nat.xor mn599 (memoNat [236544,2393667599994322944,8388636,8589950976])
def mn621 : Nat := mn606 + (memoNat [36028798092705825,2147618948,144115192370827264,16777216])
def mn622 : Nat := Nat.xor mn586 (memoNat [1107296256,64,849656335433728,17592186044440])
def mn623 : Nat := memoNat [7697411101132670612,6092564675238802725,12198367178003278666,155191031772316]
def mn624 : Nat := mn533 + (memoNat [1116892740874894303,16064199202061682624,4333815,532575944952])
def mn625 : Nat := mn623 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn626 : Nat := mn535 + (memoNat [1116892740874894303,16064199202061682624,4333815,532575944952])
def mn627 : Nat := mn578 - (memoNat [1154082587845591040,2305983746838364096,9007199388827904,262136])
def mn628 : Nat := memoNat [5319440197822828114,8402843185221776681,2970346401561275086,146395206669469]
def mn629 : Nat := mn485 - (memoNat [36025499555759137,16217596398579548224,4398038122503,17179844616])
def mn630 : Nat := mn559 - (memoNat [68225024,4762767712176832512,281474980904972,25769803776])
def mn631 : Nat := mn487 - (memoNat [36025430836281377,13983813113707561024,137430695943,17179844616])
def mn632 : Nat := mn548 - (memoNat [68191232,16143152795590066176,277076934393863])
def mn633 : Nat := mn631 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn634 : Nat := mn550 - (memoNat [68157472,16140901064495855680,277076934389759])
def mn635 : Nat := mn485 - (memoNat [1159983726101504,13909571958432661440,9002801468145795,8590172152])
def mn636 : Nat := mn552 - (memoNat [17329851366155223073,16140971433240035327,277076934393727])
def mn637 : Nat := mn579 - (memoNat [2250769020519424,2251870747688964,9223376709774999556,268427264])
def mn638 : Nat := mn582 + (memoNat [2199058872320,15920015775545556992,145139972440059,8770323234816])
def mn639 : Nat := mn579 - (memoNat [69269231501312,18446741878983362562,288234782783971327,8380416])
def mn640 : Nat := mn638 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn641 : Nat := mn619 - (memoNat [33622016,148684758400761856,145277394616328,8813272875008])
def mn642 : Nat := mn640 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn643 : Nat := memoNat [7697342929299916402,10704252890539928805,11910281933234064202,163987116422300]
def mn644 : Nat := memoNat [7698504049012296275,10706502422541608101,16666083281471232838,163986839598236]
def mn645 : Nat := mn577 - (memoNat [1155209656018176000,4644408118935492,9232379511251534084,268689400])
def mn646 : Nat := mn556 + (memoNat [1116892740874894303,16064199202061682624,4333815,532575944952])
def mn647 : Nat := mn577 - (memoNat [1154118873911394337,138542898481154,297237584260505856,8642552])
def mn648 : Nat := mn577 - (memoNat [2344193974824075297,68171939778628,148618792128090240,17293304])
def mn649 : Nat := mn635 + (memoNat [37192080355787809,72198331662598144,9007199523176576,262144])
def mn650 : Nat := mn649 - (memoNat [33588224,2380222771809484800,145277403004932,8804682956800])
def mn651 : Nat := mn561 + (memoNat [0,18444421905151688704,4219,266287972352])
def mn652 : Nat := mn562 + (memoNat [1014784,16064199133342203904,4333815,532575944704])
def mn653 : Nat := mn643 + (memoNat [70370891662370,2251801963333696,288230522180608000,8388608])
def mn654 : Nat := mn653 - (memoNat [33588224,2380222771809484800,145277403004932,8804682956800])
def mn655 : Nat := mn624 + (memoNat [1099546263552,18374616110927511552,145277407199235,8787503095808])
def mn656 : Nat := Nat.xor mn638 (memoNat [36028804602265831,448,286019320676352,17592186044424])
def mn657 : Nat := mn647 + (memoNat [1190078400625115168,140737624670208,9007203818144000,262144])
def mn658 : Nat := Nat.xor mn625 (memoNat [6597076091904,2812994946549088256,25165828,25769820160])
def mn659 : Nat := Nat.xor mn658 (memoNat [246291678363681,2162624578,144115192370827264,8388608])
def mn660 : Nat := Nat.xor mn640 (memoNat [36028798159814657,0,286702220476416,17592186044424])
def mn661 : Nat := mn647 + (memoNat [35186553126945,70373041309762,288230384875872256,8388608])
def mn662 : Nat := Nat.xor mn641 (memoNat [252201585575198753,384,146110493229056,26388279066640])
def mn663 : Nat := mn658 + (memoNat [16066590573279051744,4225828929,283726780819316608,7864320])
def mn664 : Nat := Nat.xor mn628 ((memoNat [536871457,73396834634039328,14336,8388612]) * 2 ^ 11)
def mn665 : Nat := mn481 + ((memoNat [18446707789859357695,2216624189,4499201585049600]) * 2 ^ 51)
def mn666 : Nat := mn482 + ((memoNat [18446707789859357695,2216624189,4499201585049600]) * 2 ^ 51)
def mn667 : Nat := mn665 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn668 : Nat := mn666 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn669 : Nat := memoNat [7733368428854660755,6241321997109996835,11910282074955533138,164004296266916]
def mn670 : Nat := mn666 + (memoNat [18446708888263753663,68782321531,18302628748194738180,251658239])
def mn671 : Nat := memoNat [6543327413808025236,6241181263782393189,12189505256013261394,164004304393380]
def mn672 : Nat := memoNat [5353216027903282803,8547096840828597605,12193863578376039122,155208211117220]
def mn673 : Nat := Nat.xor mn501 ((memoNat [35,15462083592192,29360284]) * 2 ^ 15)
def mn674 : Nat := memoNat [6544490661676664468,6092566805542645029,12198371859781732938,172233462010780]
def mn675 : Nat := mn517 + (memoNat [1151796704211664896,2375651071180736510,13835058055282163712,8447])
def mn676 : Nat := mn519 - (memoNat [3377734047761408,6755399441055750,13834917592675909632])
def mn677 : Nat := memoNat [6579393525502789301,10778698484114828643,7586690101961902666,172250105009060]
def mn678 : Nat := Nat.xor mn507 (memoNat [1048576,6612102166534,962076897280])
def mn679 : Nat := mn677 + (memoNat [1090748820784063,2256268857046910,4467570963495518216,520093696])
def mn680 : Nat := mn509 + (memoNat [1151795604733558784,2198956146688,137434759296])
def mn681 : Nat := mn495 - (memoNat [16215281892244520002,18230639323949033471,4503462326829055,523520])
def mn682 : Nat := mn613 - (memoNat [3377802799745024,2310346608841064454,13835062728206581760])
def mn683 : Nat := memoNat [7696286266445874836,6092562334347474211,7586967178900630346,172782680954012]
def mn684 : Nat := Nat.xor mn601 (memoNat [2147483682,16140907676598009926,31748398252032])
def mn685 : Nat := mn683 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn686 : Nat := mn603 - (memoNat [18411841176597430239,2305770441513369599,4260607557632])
def mn687 : Nat := mn685 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn688 : Nat := mn605 + (memoNat [1257632259744167010,65510962221809786,9011185253089532,8053325839])
def mn689 : Nat := memoNat [7732279879092750964,10850756078148429025,7442856384576445258,172799844045988]
def mn690 : Nat := memoNat [6542201445181671060,10848365810738836833,2966278221557754446,172800128996516]
def mn691 : Nat := mn681 + (memoNat [34570240,69801323096180734,13835339392828579960,549218943231])
def mn692 : Nat := mn690 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn693 : Nat := mn687 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn694 : Nat := mn517 + ((memoNat [33522687,62,4190208]) * 2 ^ 50)
def mn695 : Nat := Nat.xor mn676 (memoNat [2199026401280,13835060256520404992,12582940,268451840])
def mn696 : Nat := mn679 + (memoNat [35185446879297,2151811204,144115192375017472,16777216])
def mn697 : Nat := mn677 + (memoNat [18446742974197956608,16140903336667709439,7,536862720])
def mn698 : Nat := mn611 + (memoNat [34902863826124833,62,13835058055282294784,7])
def mn699 : Nat := Nat.xor mn682 (memoNat [2199025385472,2305845691488272384,8388612,268451840])
def mn700 : Nat := mn595 + (memoNat [108086394278117475,2199023255744,8933532368896,24])
def mn701 : Nat := Nat.xor mn683 (memoNat [1099512676352,2624628129792,4194304,536895488])
def mn702 : Nat := memoNat [7732243594134309523,8544915405533326627,7298741192201423698,172800389297316]
def mn703 : Nat := Nat.xor mn688 (memoNat [2199025582080,13835060735408930816,8388636,268451840])
def mn704 : Nat := mn689 + (memoNat [1125934266647552,2256337580916738,4611686155866341384,536870912])
def mn705 : Nat := Nat.xor mn689 (memoNat [1099512872960,16140903691271012352,4194328,536895488])
def mn706 : Nat := mn692 + (memoNat [36251672509473,16138647069955983424,14123288302580670463,8380415])
def mn707 : Nat := Nat.xor mn690 (memoNat [229376,13835060737489633280,8388636,268451840])
def mn708 : Nat := mn692 + (memoNat [17257794873777455104,70373106321473,292733984503242880,8126464])
def mn709 : Nat := Nat.xor mn691 (memoNat [3298538225664,16140903689191096320,4194328,536895488])
def mn710 : Nat := memoNat [7734495462600331923,8549416735203372325,16521822953423063886,155207934817444]
def mn711 : Nat := memoNat [7734531747525284468,10855261945585706211,16665792868395080526,146411833414820]
def mn712 : Nat := memoNat [6544454447553696404,8549276001875768679,16801046134480792142,155207942943908]
def mn713 : Nat := memoNat [5354343061648953971,10855191578921973095,16805404456843569870,146411849667748]
def mn714 : Nat := mn635 + (memoNat [37347996468224,144323953553309630,13844056458712318076,8053325815])
def mn715 : Nat := mn548 - ((memoNat [2081,4501469256482816,8585740412]) * 2 ^ 15)
def mn716 : Nat := memoNat [5426473154769373877,13012486029594436963,7586685562055776970,163728889901732]
def mn717 : Nat := mn565 - (memoNat [68222976,4542129242112,281474980904972,805306368])
def mn718 : Nat := mn716 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn719 : Nat := Nat.xor mn554 (memoNat [68157440,6612102166534,282437053607936])
def mn720 : Nat := mn555 + (memoNat [983040,18376938139764652034,4611545555817074939,274609471232])
def mn721 : Nat := Nat.xor mn556 (memoNat [8078331831696490496,6597539528704,282437053580160])
def mn722 : Nat := mn667 - (memoNat [72056496672768066,72127962782040192,8933528043524,8589926416])
def mn723 : Nat := mn653 - ((memoNat [1,2322168698574848,134217728,24576]) * 2 ^ 15)
def mn724 : Nat := memoNat [7662440067621277299,10780884379867852005,16521959430446205770,163995437921428]
def mn725 : Nat := Nat.xor mn644 (memoNat [32,16140907676598009926,31748398252032])
def mn726 : Nat := mn645 + (memoNat [33285998592,76701860152475586,4611677497212141568,8321499128])
def mn727 : Nat := mn725 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn728 : Nat := mn667 - (memoNat [69271378984994,16140901066645440576,288230522176413695,8380416])
def mn729 : Nat := mn665 - (memoNat [34085933219905,16140905604414771330,144115329805586439,553639936])
def mn730 : Nat := mn706 - (memoNat [33619968,13835058197083062272,145277394616327,8796629876736])
def mn731 : Nat := mn672 + (memoNat [1128098932097024,4611683606669164544,145277277175796,8795287732224])
def mn732 : Nat := memoNat [6544419261034123891,13160966414052666661,16512961027016313422,164004027593892]
def mn733 : Nat := mn727 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn734 : Nat := mn542 + ((memoNat [17,3570228604599009280,67174404,393216]) * 2 ^ 21)
def mn735 : Nat := Nat.xor mn488 (memoNat [6597070815232,13835060269807960064,4194308,805322752])
def mn736 : Nat := mn532 - ((memoNat [1,70368746276928,4,256]) * 2 ^ 20)
def mn737 : Nat := Nat.xor mn533 (memoNat [7696581492736,2305845427683000320,8,536879104])
def mn738 : Nat := mn638 + ((memoNat [17,38388453125128192,67108864,12582912]) * 2 ^ 11)
def mn739 : Nat := mn738 - (memoNat [33587200,2269957324800,145277403004932,8796361457664])
def mn740 : Nat := Nat.xor mn653 ((memoNat [1099545189377,481036546444,137444065668,786448]) * 2 ^ 25)
def mn741 : Nat := mn656 + (memoNat [1024,2452348393700196352,0,16642998272])
def mn742 : Nat := mn732 + (memoNat [1190078400625115168,140739772153856,9007203818144000,262144])
def mn743 : Nat := mn742 - (memoNat [33587200,2269957324800,145277403004932,8796361457664])
def mn744 : Nat := Nat.xor mn743 (memoNat [246298120814823,2162624966,144115192370827264,8388608])
def mn745 : Nat := Nat.xor mn711 (memoNat [7696588800000,2305845348226039808,29360136,536879104])
def mn746 : Nat := mn732 + (memoNat [35186553126945,4364240962,288230384875872256,8388608])
def mn747 : Nat := Nat.xor mn712 (memoNat [32768,13835060338057674752,25165828,805322752])
def mn748 : Nat := mn713 + (memoNat [1099546198016,2305842938346799104,145277407199228,8795824594944])
def mn749 : Nat := mn748 - (memoNat [33587200,2269957324800,145277403004932,8796361457664])
def mn750 : Nat := mn583 + (memoNat [72059795210798114,4686070179067721790,4402350129156,8581562384])
def mn751 : Nat := mn625 + (memoNat [36028798092773377,2454602534403176446,4295098376,17171480584])
def mn752 : Nat := mn665 + (memoNat [2146312195737501,4503735046694718,8791026468332228616,511705088])
def mn753 : Nat := mn751 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn754 : Nat := mn605 + (memoNat [72023511359587393,16215278628068393088,4402471763971,8589926416])
def mn755 : Nat := mn754 - (memoNat [1099546230784,2305845208237015040,145277407199232,8796093030400])
def mn756 : Nat := mn672 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn757 : Nat := Nat.xor mn591 (memoNat [33792,16645304222761826304,30799211425792])
def mn758 : Nat := mn674 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn759 : Nat := mn507 + (memoNat [68718462976,66572058622,4290772992])
def mn760 : Nat := mn677 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn761 : Nat := mn523 - (memoNat [105556304986115,6442450944,432204835333349376])
def mn762 : Nat := mn679 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn763 : Nat := mn511 + (memoNat [1152886320268312575,65536,4290773120])
def mn764 : Nat := mn756 + (memoNat [1065151855616,2233787545479608320,9079690616704,17042430238464])
def mn765 : Nat := mn684 - (memoNat [2147482658,18444494472919056448,133143986175])
def mn766 : Nat := mn683 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn767 : Nat := mn618 + (memoNat [35924343415373856,2192580870208,18014398500896362496,8199])
def mn768 : Nat := mn766 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn769 : Nat := mn605 - (memoNat [18410750461062676448,2305772640469450751,4393751543808])
def mn770 : Nat := mn768 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn771 : Nat := mn704 - (memoNat [105556337491971,2203318222848,432345710256467968])
def mn772 : Nat := mn689 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn773 : Nat := mn692 - (memoNat [18445653358174797825,2198956081151,133143986176])
def mn774 : Nat := mn691 + (memoNat [2181497641535454,4503666264373186,8935141793847042052,260046848])
def mn775 : Nat := mn754 - (memoNat [36286065803297,16140898869769668674,288230384871677951,8380416])
def mn776 : Nat := mn764 + (memoNat [33320633344,72057660609787772,18302910356324094080,549739036927])
def mn777 : Nat := mn761 + (memoNat [34085934202913,16140898867622182978,144115192370827263,8380416])
def mn778 : Nat := Nat.xor mn761 (memoNat [2199026401504,13835062453343420866,12582912,8404992])
def mn779 : Nat := mn497 + (memoNat [3458764616899857408,216172988272283648,4294967296,768])
def mn780 : Nat := Nat.xor mn762 (memoNat [1099511627968,16140907661578287492,0,16801792])
def mn781 : Nat := mn615 + ((memoNat [18445618173802710015,66571993087,4190208]) * 2 ^ 45)
def mn782 : Nat := Nat.xor mn583 ((memoNat [2097159,13510798882111872,8619298972,262144]) * 2 ^ 25)
def mn783 : Nat := mn597 + (memoNat [108086392130633793,65664,8800388382720,24])
def mn784 : Nat := Nat.xor mn768 (memoNat [1099512676384,6597082427460,4194304,16801792])
def mn785 : Nat := mn702 + (memoNat [1090748820751359,2251799813685248,4467570830351527936])
def mn786 : Nat := Nat.xor mn771 (memoNat [2199025352928,13835060254320167360,8388608,8404992])
def mn787 : Nat := mn688 + (memoNat [3377802799746048,6755399441121284,13835058334455037952])
def mn788 : Nat := Nat.xor mn710 (memoNat [35185647157249,0,433217344609742848,17592186044416])
def mn789 : Nat := mn754 - (memoNat [1107296256,2147483648,144115192505044992])
def mn790 : Nat := mn754 - (memoNat [36286065803265,2305845212531982336,288230384880066560,8192])
def mn791 : Nat := mn764 + (memoNat [35218766464001,72057662757406720,281474985369728,549755814144])
def mn792 : Nat := Nat.xor mn756 ((memoNat [33,15762598695797184,12910878852,524288]) * 2 ^ 25)
def mn793 : Nat := mn751 - (memoNat [1190076200492466208,140735477252096,18311636085022650624,262143])
def mn794 : Nat := mn713 + (memoNat [1090748820816831,2254138553331582,4467570830351527944,520093696])
def mn795 : Nat := mn485 - (memoNat [31886908816449,13762993866326020228,144119586113851391,16752640])
def mn796 : Nat := mn550 - (memoNat [68123680,18374686479671558208,281470685806591])
def mn797 : Nat := mn487 - (memoNat [31818189338689,11529210581454033028,144115325506424831,16752640])
def mn798 : Nat := Nat.xor mn719 (memoNat [32768,6665789716480,974957604864])
def mn799 : Nat := mn489 - (memoNat [31886908850241,11529208451150317700,144115192362434559,16752640])
def mn800 : Nat := Nat.xor mn570 (memoNat [100663456,10891590,453965293425536,27212937953280])
def mn801 : Nat := memoNat [5392623623048121939,13019105231388316901,2821877430907259478,163729678168741]
def mn802 : Nat := mn794 + (memoNat [1065151855616,2233787545479608320,9079690616704,17042430238464])
def mn803 : Nat := mn738 + (memoNat [18445582953997172671,68782321529,13690938194281885700,251658239])
def mn804 : Nat := Nat.xor mn725 (memoNat [66592,2258396883910720,974957576200])
def mn805 : Nat := mn752 - (memoNat [72056494525285408,74377563572535360,8800384057348,8589926416])
def mn806 : Nat := mn658 + (memoNat [33588160,74379762589362042,140879356493828,8804657790976])
def mn807 : Nat := mn647 + (memoNat [33760,74450133485352830,144106400572641284,8581545976])
def mn808 : Nat := mn648 - (memoNat [18410750461062676512,2305772640473645055,4393751543808])
def mn809 : Nat := mn669 - (memoNat [31886907801665,11529210648026091650,144115329797197823,16752640])
def mn810 : Nat := mn742 - (memoNat [96,2199029684420,137438953472,25165824])
def mn811 : Nat := memoNat [6544419227748159059,13158714687385543905,12045389930376813138,164004287640740]
def mn812 : Nat := mn742 - (memoNat [2379062786003042401,72567773726786,18307132618539266176,8912895])
def mn813 : Nat := mn732 + (memoNat [1090748820816831,2254138553331582,4467570830351527944,520093696])
def mn814 : Nat := memoNat [5355470094388090451,13163290925714349219,2826521768161532630,164004547425445]
def mn815 : Nat := mn814 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn816 : Nat := mn544 + (memoNat [35651584,65536,140741792113024,824633720832])
def mn817 : Nat := Nat.xor mn544 (memoNat [2097184,2099270,31748541801344,27212937953280])
def mn818 : Nat := mn570 + (memoNat [35185445830593,2143221628,144115192370958464,274861129728])
def mn819 : Nat := Nat.xor mn535 (memoNat [7696581394496,2305845208241211524,0,16785408])
def mn820 : Nat := mn640 + (memoNat [101376,4834825306214825984,4294967308,25769803776])
def mn821 : Nat := Nat.xor mn584 (memoNat [6597076058112,16140905462544545798,25165824,25182208])
def mn822 : Nat := mn740 + (memoNat [1090748820784063,2256408508491644,4467570830351527940,780140544])
def mn823 : Nat := mn624 + (memoNat [1091848333493151,2256337572323130,4467570830355722248,503324672])
def mn824 : Nat := mn729 + (memoNat [98304,4608701300736,4294967308,805306368])
def mn825 : Nat := mn729 - (memoNat [33456160,18446739465010415682,145273108037619,8795296104448])
def mn826 : Nat := mn745 + (memoNat [33619936,2338741811136,145277403004936,8796621504512])
def mn827 : Nat := mn745 + (memoNat [65472,2338739646334,8,520093696])
def mn828 : Nat := mn813 + (memoNat [35186553126945,4297132098,288230384875872256,8388608])
def mn829 : Nat := mn828 - (memoNat [33554464,2164802,145277403004928,8796101410816])
def mn830 : Nat := mn814 - (memoNat [35184372088833,0,145277268787200,8796093022208])
def mn831 : Nat := mn830 - (memoNat [33554464,2164802,145277403004928,8796101410816])
def mn832 : Nat := mn814 + (memoNat [1107296288,16140828498810968262,139611588578512767,25157632])
def mn833 : Nat := mn756 + (memoNat [71470404337698,18446673709195331650,283726780819316607,8388608])
def mn834 : Nat := mn832 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn835 : Nat := mn833 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn836 : Nat := mn505 + (memoNat [18410717475748479967,71987225293750271,130154496])
def mn837 : Nat := mn635 + (memoNat [1133870385152,13979171113054177280,141993963263,8521215107328])
def mn838 : Nat := mn509 + (memoNat [18445620441580079104,68652367871,130023424])
def mn839 : Nat := mn720 + (memoNat [1133870384128,16212954397926164480,4402601389823,8521215107328])
def mn840 : Nat := mn511 + (memoNat [18446711088395321343,2047,130027520])
def mn841 : Nat := mn801 + (memoNat [1133870351360,16212956528229879808,4535745380095,8521215107328])
def mn842 : Nat := mn527 - (memoNat [1099546230784,211106433859584,13370061666386176])
def mn843 : Nat := mn499 - (memoNat [17368201129107551298,18230641454252812287,4503599631564927,523520])
def mn844 : Nat := mn603 - (memoNat [1123700847934464,2303591209467117568,4397912293376])
def mn845 : Nat := memoNat [6508426749040774771,6096925267284243751,16801332153805400654,172782949127324]
def mn846 : Nat := mn769 - (memoNat [36026595812573183,70368744243136,4160749568])
def mn847 : Nat := memoNat [6509517497861525074,6096929805047080165,2822159043591363150,172783469221021]
def mn848 : Nat := mn619 - (memoNat [1154083687358267392,68169857171392,9007199384633600,253944])
def mn849 : Nat := mn847 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn850 : Nat := mn692 - (memoNat [32985313181697,2196875771902,137304735744])
def mn851 : Nat := memoNat [6544420361687650899,10855119011085198565,16657221359481215566,172800112219300]
def mn852 : Nat := mn708 - (memoNat [1099579785216,213305390006272,13510936589500800])
def mn853 : Nat := mn688 + (memoNat [14880982890013789119,6542096194406469,14109777915751177856,7602176])
def mn854 : Nat := mn792 + (memoNat [35185378721793,2305634103950573568,130604388929506944,8192])
def mn855 : Nat := Nat.xor mn834 (memoNat [1073741824,6442848652,1009796014434955264,8796143353856])
def mn856 : Nat := mn525 + (memoNat [34359772160,71987293946120192,18442240474082181120,255])
def mn857 : Nat := Nat.xor mn491 ((memoNat [17592189190147,68191267,65536]) * 2 ^ 91)
def mn858 : Nat := mn536 + (memoNat [0,0,18446607876135846016,8796093022207])
def mn859 : Nat := Nat.xor mn537 ((memoNat [7340039,201732230,262144]) * 2 ^ 90)
def mn860 : Nat := Nat.xor mn619 (memoNat [1073741824,469762112,13510798883029888,24])
def mn861 : Nat := Nat.xor mn585 ((memoNat [3,422212467163148,297799820,262144]) * 2 ^ 25)
def mn862 : Nat := mn599 + (memoNat [72059796318060610,192,8796227633152,24])
def mn863 : Nat := Nat.xor mn849 (memoNat [7176697112447418401,6597082808320,4194304,548864])
def mn864 : Nat := mn706 + (memoNat [34359739392,2181431069507586,4607182418800017280])
def mn865 : Nat := Nat.xor mn671 ((memoNat [3,422212477648898,297926796,262144]) * 2 ^ 25)
def mn866 : Nat := mn690 + (memoNat [2254101951810560,6755399441055750,13835058330294288384])
def mn867 : Nat := Nat.xor mn712 ((memoNat [3,492581223923712,428634380,524288]) * 2 ^ 25)
def mn868 : Nat := mn754 - ((memoNat [1,70368746274818,134217860]) * 2 ^ 25)
def mn869 : Nat := mn754 - (memoNat [1099579785216,2305985945859588096,9007203822338304,8192])
def mn870 : Nat := mn754 + (memoNat [71470404337666,2305845212531982336,288230380450881536,8192])
def mn871 : Nat := mn754 + (memoNat [70370858106882,18446673709193232384,283726780685098879])
def mn872 : Nat := mn692 + (memoNat [2254068665845728,4503672706824130,9367487366798774276,260046848])
def mn873 : Nat := mn872 - (memoNat [1099546230784,2305915577048301568,4503599765782656,8192])
def mn874 : Nat := mn485 - (memoNat [2380220572785146946,13763064232989753344,4507997665362047,499712])
def mn875 : Nat := mn552 - (memoNat [36028797053533217,18374756848415801344,281474846556159])
def mn876 : Nat := mn487 - (memoNat [2380220504065669186,11529280948117766144,4503737057935487,499712])
def mn877 : Nat := Nat.xor mn556 ((memoNat [240518171745,2111488,8589938816]) * 2 ^ 15)
def mn878 : Nat := mn489 - (memoNat [2380220572785180738,11529278817814050816,4503603913945215,499712])
def mn879 : Nat := mn802 - (memoNat [1152921504607895552,63488,4160745600])
def mn880 : Nat := mn491 - (memoNat [1227301267202637890,11529278817813987328,4503599753199615,499712])
def mn881 : Nat := mn573 - (memoNat [2417412653141983331,6291456,281474980904960,786432])
def mn882 : Nat := mn731 - (memoNat [73183496058634306,2377966361214189696,8933398020088,7784628240])
def mn883 : Nat := mn727 - (memoNat [36028796985343009,18444564841663299584,137304735735])
def mn884 : Nat := mn882 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn885 : Nat := mn648 - (memoNat [35184338534433,2305843009217888192,4397912293376])
def mn886 : Nat := mn834 - (memoNat [36029898712712225,74307194828292224,8796223307780,8589926416])
def mn887 : Nat := mn577 - (memoNat [4688389048053530690,2305911179077156800,9011597431144704,1040376])
def mn888 : Nat := mn811 + (memoNat [17255472702031921150,70368744179779,18307132476939563136,8126463])
def mn889 : Nat := Nat.xor mn812 ((memoNat [252204877902512129,462,388]) * 2 ^ 25)
def mn890 : Nat := mn671 - (memoNat [2379096871936196674,11529281016770134016,4503737187958911,499712])
def mn891 : Nat := mn746 - (memoNat [3569208257807384675,2199029547008,137438953472,786432])
def mn892 : Nat := mn834 - (memoNat [36286065803297,16140898869769668674,288230384871677951,8380416])
def mn893 : Nat := mn828 - (memoNat [3570298973342138402,2162688,4294967296,786432])
def mn894 : Nat := Nat.xor mn546 (memoNat [1099615436800,0,422212608619264,824633720832])
def mn895 : Nat := Nat.xor mn880 ((memoNat [123145305456643,70491235,196608]) * 2 ^ 91)
def mn896 : Nat := Nat.xor mn575 (memoNat [260118062852735009,2097152,946176,824634507264])
def mn897 : Nat := Nat.xor mn538 (memoNat [1375920054905864258,2305845208241209344,0,532480])
def mn898 : Nat := memoNat [5319440196816228946,10783068156054582505,2970632558324837074,163995982656661]
def mn899 : Nat := mn898 - (memoNat [1190112485450973217,2097152,145277403004928,8796093284352])
def mn900 : Nat := mn578 - (memoNat [3498275463089881121,65970770935744,4503599618850944,770040])
def mn901 : Nat := Nat.xor mn887 ((memoNat [3,70368744177666,142762252,524288]) * 2 ^ 25)
def mn902 : Nat := mn708 - (memoNat [0,16140901064495792128,145277264592895,8796093014016])
def mn903 : Nat := Nat.xor mn890 ((memoNat [3,422212477648910,273547660,786432]) * 2 ^ 25)
def mn904 : Nat := mn748 + (memoNat [17257758587711684575,70864863231,4,268173312])
def mn905 : Nat := mn749 + (memoNat [16067646102294298558,2340820090879,8,536346624])
def mn906 : Nat := Nat.xor mn815 (memoNat [1099546230880,6699334,134217728,25165824])
def mn907 : Nat := mn906 - (memoNat [1190112485450973217,2097152,145277403004928,8796093284352])
def mn908 : Nat := mn830 + ((memoNat [34634719,0,133143986176]) * 2 ^ 50)
def mn909 : Nat := mn831 + (memoNat [16066555386759479295,69763,0,16252928])
def mn910 : Nat := mn577 + (memoNat [16140903194799636480,4260607684607,283736268544,17042430246400])
def mn911 : Nat := mn539 + (memoNat [1099511627776,18444424104175009792,9079829430267,17583596118016])
def mn912 : Nat := mn607 + (memoNat [3298535931904,18442106333663789056,141872328567,8504035270656])
def mn913 : Nat := mn911 - (memoNat [36028798092739617,2380222771809484864,4398046642180,8589934600])
def mn914 : Nat := memoNat [3049699514462553715,12868304875250160869,12198512601707530830,181038144983188]
def mn915 : Nat := memoNat [4203746918941640307,12942612067863928039,16810058020081187274,180762998641044]
def mn916 : Nat := mn914 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn917 : Nat := mn915 + (memoNat [1090748820784063,2256268857046910,4467570963495518216,520093696])
def mn918 : Nat := memoNat [3014759233920484946,12872669938490709225,2966133640207485394,181038413156501]
def mn919 : Nat := mn874 + (memoNat [1065151855616,2233787545479608320,9079690616704,17042430238464])
def mn920 : Nat := memoNat [5283484927525439025,10634449160049697893,12198644543106931402,181304432956036]
def mn921 : Nat := memoNat [5320639659884725842,8256475918096573607,16810335097019914954,181295574585996]
def mn922 : Nat := mn920 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn923 : Nat := mn921 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn924 : Nat := memoNat [4131652008080394801,10636632860940215401,2966265581606885838,181304701129349]
def mn925 : Nat := mn923 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn926 : Nat := memoNat [5355472152819222097,13012420129895849125,11910422954458561230,181313014502036]
def mn927 : Nat := memoNat [5356633272531601970,13014669661897528421,16666224302695729866,181312737677972]
def mn928 : Nat := memoNat [4166554838620522066,13012279394487936229,12189646139677039054,181313022628500]
def mn929 : Nat := memoNat [2977570486528559665,13014599293153486055,16805835895304968778,181312753930900]
def mn930 : Nat := mn928 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn931 : Nat := mn925 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn932 : Nat := mn607 + (memoNat [17293823634254594048,2130303842303,0,7936])
def mn933 : Nat := Nat.xor mn493 (memoNat [216172784294821954,128,145135535001728,274877906960])
def mn934 : Nat := mn485 + ((memoNat [3221227553,4573974813999296,8320,24]) * 2 ^ 10)
def mn935 : Nat := Nat.xor mn539 (memoNat [252201580207538209,64,4350720,549755813912])
def mn936 : Nat := mn928 + (memoNat [37416750547968,18374827217229182912,9002801476534527,261880])
def mn937 : Nat := mn920 + ((memoNat [17870845721603702783,32,68719472640]) * 2 ^ 61)
def mn938 : Nat := mn927 + (memoNat [35185445863489,68723806338,144115192370827264,16777216])
def mn939 : Nat := mn921 + (memoNat [17293822534742966272,4686136149767354367,0,17179868928])
def mn940 : Nat := mn930 + (memoNat [1128065713273889,18374827148576817152,9002801476534527,261880])
def mn941 : Nat := mn922 + (memoNat [16140900995776347136,2236107446294673407,4,8589934080])
def mn942 : Nat := mn923 + (memoNat [36028798092773409,4760445543618971712,4398046642184,17179869192])
def mn943 : Nat := mn923 + (memoNat [17293822534743000064,4688387880861564927,8,17179868928])
def mn944 : Nat := mn930 + (memoNat [35151086058529,18374686415249276930,288225986695012351,8388344])
def mn945 : Nat := mn924 + (memoNat [17293822500383194112,2236037077550493695,4,8589934080])
def mn946 : Nat := mn930 + (memoNat [18445619275496423457,70373106321473,292733984503242880,8126464])
def mn947 : Nat := Nat.xor mn919 (memoNat [1108344832,64,875211281032064,549755813912])
def mn948 : Nat := mn631 + (memoNat [17293823634253545472,2130303842303,4681778454272,17042430238464])
def mn949 : Nat := mn632 + (memoNat [17293823634253545472,2130303842303,4681778454272,17042430238464])
def mn950 : Nat := mn948 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn951 : Nat := mn634 + (memoNat [17293823634253545472,2130303842303,4681778454272,17042430238464])
def mn952 : Nat := mn911 - (memoNat [1163282263081984,72198331662598080,9002801476665472,262136])
def mn953 : Nat := mn911 - (memoNat [38352029689577505,70300096001984,4639939207762048,274878430968])
def mn954 : Nat := memoNat [6472435264550127186,8326284050997619877,12198508203660888646,181020965114764]
def mn955 : Nat := mn914 - ((memoNat [594473500958244863,2248182815,6989586415453470718]) * 2 ^ 36)
def mn956 : Nat := mn954 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn957 : Nat := mn955 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn958 : Nat := mn641 + (memoNat [17293823634253545472,2130303842303,4681778454272,17042430238464])
def mn959 : Nat := mn957 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn960 : Nat := mn643 + (memoNat [17293823634253545472,2130303842303,4681778454272,17042430238464])
def mn961 : Nat := memoNat [6545583609556290131,10706504552845450405,16666087963249687110,181029269836700]
def mn962 : Nat := mn910 - (memoNat [2289216564267008,4646538422777796,9232375113209348356,268697336])
def mn963 : Nat := mn910 - (memoNat [1191273568656229409,2326639757227970,4616185357581418632,537394936])
def mn964 : Nat := mn910 - (memoNat [1198434457485345,140673202323458,297233186218320128,8650488])
def mn965 : Nat := mn910 - (memoNat [1191273535370166305,70302243620932,148614394085904512,17301240])
def mn966 : Nat := mn530 + ((memoNat [32801,70368744177664,146444517504,25769803776]) * 2 ^ 10)
def mn967 : Nat := Nat.xor mn530 ((memoNat [3,520238327345971200,26096268,25976832]) * 2 ^ 20)
def mn968 : Nat := mn651 + (memoNat [0,0,141868134272,8521215115264])
def mn969 : Nat := Nat.xor mn562 (memoNat [101376,2382826415344058368,5231538601992,17609365913600])
def mn970 : Nat := mn960 + (memoNat [70370891662370,2251801963333696,288230384741654528,8388608])
def mn971 : Nat := mn948 - ((memoNat [17870845721603702783,32,68719472640]) * 2 ^ 61)
def mn972 : Nat := memoNat [6545618794967550612,8328533580853980455,16810062418127829450,180745818772380]
def mn973 : Nat := mn949 - (memoNat [17293822534742966272,4686136149767354367,0,17179868928])
def mn974 : Nat := mn956 + (memoNat [72057594037961760,2380222771809484864,8796093288452,8589934608])
def mn975 : Nat := Nat.xor mn956 (memoNat [216172782148386848,64,167125771748224,824633720848])
def mn976 : Nat := Nat.xor mn975 (memoNat [246291678363681,2162243650,144115192370827264,8388608])
def mn977 : Nat := Nat.xor mn957 (memoNat [36028798161911809,0,285873031746304,549755813896])
def mn978 : Nat := mn910 - (memoNat [1163247903309824,70300161013696,9002801476665472,261880])
def mn979 : Nat := Nat.xor mn837 (memoNat [33792,2812511161432539136,4840441671684,62423054729216])
def mn980 : Nat := mn975 + (memoNat [16066590573280100320,4225828929,283726784980062208,7864320])
def mn981 : Nat := mn664 + (memoNat [17293823634252496896,2130303842303,13761464876672,34084860468992])
def mn982 : Nat := mn914 + (memoNat [2377900674118649922,2452278302048522368,8796093153280,8321499664])
def mn983 : Nat := mn541 + (memoNat [1099511627776,2305843006999166976,9079829299196,17591917617152])
def mn984 : Nat := mn982 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn985 : Nat := mn983 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn986 : Nat := memoNat [3121686739756304019,15176470048724587811,11910291013059033682,181046726529188]
def mn987 : Nat := Nat.xor mn983 (memoNat [35185445830849,2199103080836,1008806346595762204,318767104])
def mn988 : Nat := memoNat [3084565030292211348,15176329315397047653,12189514198277507538,181046734655652]
def mn989 : Nat := memoNat [3047376282865715827,15248457346963643749,12193877060546410962,180771856486820]
def mn990 : Nat := mn938 - (memoNat [3377734080300032,76561193665298438,13835058467599155200])
def mn991 : Nat := memoNat [5391571390523067028,10562389364773922085,12198657737246726862,181304164520604]
def mn992 : Nat := mn991 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn993 : Nat := Nat.xor mn926 (memoNat [70866963490,504403242017357894,917504])
def mn994 : Nat := mn920 - (memoNat [18338692796157788094,74309327283949443,144101998231031808,16777192])
def mn995 : Nat := mn928 - (memoNat [18411841107877952479,71987156641382399,131072])
def mn996 : Nat := mn994 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn997 : Nat := mn922 + (memoNat [139611521876491362,4679376281278611642,17042430623744,16642998303])
def mn998 : Nat := memoNat [5426439068903328372,15318329038803866849,7442860787056200394,181321059177124]
def mn999 : Nat := memoNat [4236360634992248468,15315938771394274657,2966282624037509582,181321344127652]
def mn1000 : Nat := memoNat [3047376282900286067,15318258670059824483,7582472379665439306,181321075430052]
def mn1001 : Nat := mn999 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn1002 : Nat := mn996 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1003 : Nat := mn675 - (memoNat [1152921504606879744,72059861780662272,0,256])
def mn1004 : Nat := mn676 + (memoNat [16140901064495824896,18302628819128807423,3,268434944])
def mn1005 : Nat := mn517 + (memoNat [1152924837503599616,6989591088445196288,137447342080,24832])
def mn1006 : Nat := mn694 + (memoNat [17293825867639685120,6845475831649859583,8388608,24320])
def mn1007 : Nat := mn487 + ((memoNat [1644168209,3377701901566048,4096,12]) * 2 ^ 11)
def mn1008 : Nat := mn716 + (memoNat [17293822569102737408,18374688751843538943,7,536870656])
def mn1009 : Nat := mn936 + (memoNat [34902898185863201,62,13835062315889721344,7])
def mn1010 : Nat := mn990 + ((memoNat [17870300381553065983,31,2147479552]) * 2 ^ 61)
def mn1011 : Nat := Nat.xor mn991 ((memoNat [1100585403425,0,4]) * 2 ^ 90)
def mn1012 : Nat := mn992 + ((memoNat [71539122733055,0,8589930496]) * 2 ^ 60)
def mn1013 : Nat := memoNat [4273482378850683539,15246275911668309283,7298745594685373138,181321604436388]
def mn1014 : Nat := mn997 + (memoNat [16140901064495824896,18302631016004581375,3,268434944])
def mn1015 : Nat := mn997 + (memoNat [2287053979027425,4505869582532546,9367487504103510020,260046848])
def mn1016 : Nat := mn998 + (memoNat [17293822569102737408,18374690948719312895,7,536870656])
def mn1017 : Nat := mn1001 + (memoNat [35152159800353,18372434615435591744,14123288302584864767,8388351])
def mn1018 : Nat := mn999 + (memoNat [17293822569102671872,18302631018084954111,3,268434944])
def mn1019 : Nat := mn1001 + (memoNat [18410716378384302080,70373106321473,292733984503242880,8126464])
def mn1020 : Nat := mn1000 + (memoNat [32768,18374690950799685632,7,536870656])
def mn1021 : Nat := memoNat [4275734144235390611,15250777241338354981,16521836431432690126,180771580187044]
def mn1022 : Nat := memoNat [5428690868613237364,15322834906241080547,16665810886310832462,180496693891748]
def mn1023 : Nat := mn983 - (memoNat [36066214808683553,18444633080240013310,13844065117366386815,262143])
def mn1024 : Nat := memoNat [4201423687344802419,15322764539577410919,16805422478920067406,180496710144676]
def mn1025 : Nat := mn914 - ((memoNat [71004261797884929,2251801961299840,8796080443392]) * 2 ^ 50)
def mn1026 : Nat := mn970 - (memoNat [33792,72064335190425600,131076,805306368])
def mn1027 : Nat := mn1025 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn1028 : Nat := mn961 - (memoNat [992,72057527465934786,131072])
def mn1029 : Nat := mn938 - (memoNat [1163249046257664,70300161013760,9147937015992704,274878168832])
def mn1030 : Nat := mn1028 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn1031 : Nat := memoNat [6579325353670035091,15390386699415954723,7298604857192688202,181046189659044]
def mn1032 : Nat := memoNat [6580486473382414964,15392636231417634019,12054406205429856838,181045912834980]
def mn1033 : Nat := mn984 - (memoNat [36066214843253793,18374827217229182976,9007199523176703,261888])
def mn1034 : Nat := mn1024 + (memoNat [34570240,69801323096180734,13835339392828579960,549218943231])
def mn1035 : Nat := memoNat [5391498821578116723,15394751829228496165,16512969969402194254,181046457832356]
def mn1036 : Nat := mn1034 + (memoNat [33286063104,2256337513607038,4467570963495514120,520093696])
def mn1037 : Nat := mn696 - ((memoNat [36065080902647807,65534,4398046507008]) * 2 ^ 50)
def mn1038 : Nat := mn496 - (memoNat [16140901064495824896,18302628819128807423,3,268434944])
def mn1039 : Nat := mn736 + (memoNat [0,0,4402475560832,8521215115264])
def mn1040 : Nat := Nat.xor mn737 (memoNat [34362885120,0,26534589784832,18141941858304])
def mn1041 : Nat := Nat.xor mn955 (memoNat [34359839744,16578242878279516160,12,25769803776])
def mn1042 : Nat := mn915 - ((memoNat [17870300381553065983,31,2147479552]) * 2 ^ 61)
def mn1043 : Nat := mn972 + ((memoNat [34360754143,0,124]) * 2 ^ 90)
def mn1044 : Nat := mn949 - ((memoNat [71539122733055,0,8589930496]) * 2 ^ 60)
def mn1045 : Nat := mn1035 + (memoNat [1190078366265375776,140739772153856,9007199523180800,262144])
def mn1046 : Nat := mn1021 - (memoNat [16140901064495824896,18302631016004581375,3,268434944])
def mn1047 : Nat := Nat.xor mn1046 (memoNat [246366840293607,2162244038,144115192370827264,8388608])
def mn1048 : Nat := mn1022 - (memoNat [17293822569102737408,18374690948719312895,7,536870656])
def mn1049 : Nat := mn1035 + (memoNat [35152194436129,4364240962,288230384741654656,8388608])
def mn1050 : Nat := mn1049 - (memoNat [34394375168,2269957324800,140737492684932,275146342400])
def mn1051 : Nat := mn1024 + (memoNat [34394342400,72055392867190784,140737492684924,274609471744])
def mn1052 : Nat := mn1024 - (memoNat [32768,18374690950799685632,7,536870656])
def mn1053 : Nat := mn982 + (memoNat [2181428922023870,4507997803773824,8935141926991036424,520093696])
def mn1054 : Nat := mn543 + (memoNat [1099511627744,2305845208234852286,9079829303296,17592177664000])
def mn1055 : Nat := mn1053 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1056 : Nat := mn1054 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1057 : Nat := mn988 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn1058 : Nat := mn989 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn1059 : Nat := mn926 - (memoNat [32768,69805796371724290,126976])
def mn1060 : Nat := mn992 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn1061 : Nat := mn942 - (memoNat [105554190042113,72057600480378880,432345577112608768])
def mn1062 : Nat := mn1060 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn1063 : Nat := mn930 - (memoNat [18410750461062710240,71987225293748223,126976])
def mn1064 : Nat := mn922 - (memoNat [2236108682206151648,72057594109228928,4490405621788800,524264])
def mn1065 : Nat := mn1016 + (memoNat [1153941813816458237,74309389556647938,4179340578753863680,256])
def mn1066 : Nat := mn998 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn1067 : Nat := Nat.xor mn1001 (memoNat [7916552439498753,69189253120,28672])
def mn1068 : Nat := mn1000 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn1069 : Nat := mn1001 + (memoNat [2181428922023902,4505796568088514,8935141926991032324,260046848])
def mn1070 : Nat := mn1064 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1071 : Nat := memoNat [4276822694066473618,10641343093725699367,2542799523087596246,172525779833253]
def mn1072 : Nat := Nat.xor mn761 (memoNat [6917529096360626400,432345701681203650,0,8389120])
def mn1073 : Nat := mn489 + (memoNat [3298536980480,6917535624710981632,8392704,24576])
def mn1074 : Nat := Nat.xor mn799 (memoNat [8070450566607701184,504403226998016388,0,16777984])
def mn1075 : Nat := Nat.xor mn940 (memoNat [252236763504836608,15032385536,432376363438047232,24])
def mn1076 : Nat := Nat.xor mn941 (memoNat [216243150857961568,12884902080,288256773020848128,16])
def mn1077 : Nat := mn922 + (memoNat [108086392130633793,2176,13194139799552,24])
def mn1078 : Nat := mn922 - (memoNat [1044870332281816000,72057664904888192,144101998231027712,232])
def mn1079 : Nat := mn1013 + (memoNat [1090714461011967,2251799813685248,4467570963495518208])
def mn1080 : Nat := Nat.xor mn1065 (memoNat [6917529027641180384,432345770400745920,0,8389120])
def mn1081 : Nat := mn997 + (memoNat [3377734080267264,6755399441057796,13835058467599028224])
def mn1082 : Nat := Nat.xor mn1021 (memoNat [35185653448705,0,433190002068558592,549755813888])
def mn1083 : Nat := mn1069 + (memoNat [35151086058529,18374686413101793346,144115192370827263,8388352])
def mn1084 : Nat := Nat.xor mn1069 (memoNat [1152921573326391328,432345701668686274,0,8389120])
def mn1085 : Nat := mn1069 + (memoNat [18409625662849548289,70373106321473,292733984503242880,8126464])
def mn1086 : Nat := Nat.xor mn1058 (memoNat [1108344832,15032385536,433190002068558720,549755813888])
def mn1087 : Nat := mn1054 - (memoNat [37156894909923360,140735477188608,18311636080861905024,262143])
def mn1088 : Nat := mn1024 + (memoNat [1090748820784063,2256268857046910,4467570963495518216,520093696])
def mn1089 : Nat := mn1041 + (memoNat [18445582988356878271,2199086036857,13690942725472256004,251658239])
def mn1090 : Nat := mn1028 + (memoNat [33760,2251731094210496,4104])
def mn1091 : Nat := mn1027 + (memoNat [1090748820784063,2256268857046910,4467570963495518216,520093696])
def mn1092 : Nat := mn974 - (memoNat [33856,72057594044420230,131072,25165824])
def mn1093 : Nat := memoNat [5356595957751991858,13016855699317367909,2822018447836531026,181038396380053]
def mn1094 : Nat := mn910 - (memoNat [1155279922723324993,72057527541563460,148614394086031488,17301240])
def mn1095 : Nat := Nat.xor mn1032 (memoNat [211112675049510,6737128521794,288230384741650452,830472192])
def mn1096 : Nat := Nat.xor mn1045 (memoNat [34359772320,68730433860,0,25165824])
def mn1097 : Nat := Nat.xor mn1035 (memoNat [41875932192,15764811008770500,4755801348237189148,276824064])
def mn1098 : Nat := Nat.xor mn1036 (memoNat [7916483720020033,69193447424,28672])
def mn1099 : Nat := memoNat [5392589570398900786,15397008098085543075,2533796859188160854,181046977926053]
def mn1100 : Nat := mn1088 + (memoNat [33320633344,72057660609787772,18302910356324094080,549739036927])
def mn1101 : Nat := mn535 + (memoNat [33554432,2048,154352937340928,26388279066624])
def mn1102 : Nat := Nat.xor mn535 (memoNat [3145760,2162758,31757672776576,27212937953280])
def mn1103 : Nat := mn535 + (memoNat [1099545182176,2305845208234852286,149813022556032,17317299757056])
def mn1104 : Nat := Nat.xor mn544 (memoNat [1152921745125252160,72058075078527108,0,16777472])
def mn1105 : Nat := mn957 + (memoNat [67584,7068610721390528512,4108,25769803776])
def mn1106 : Nat := Nat.xor mn917 (memoNat [6917529233799545856,504403570584913926,0,25166336])
def mn1107 : Nat := mn975 + (memoNat [35185445830625,2308165179914713020,144115192370827268,8573157376])
def mn1108 : Nat := mn634 + (memoNat [1099510579168,2199018991548,4681778454272,17042413461504])
def mn1109 : Nat := mn1032 + (memoNat [65536,6739005016064,4108,805306368])
def mn1110 : Nat := mn1109 - (memoNat [34603040,2164802,140737492684928,274886295552])
def mn1111 : Nat := Nat.xor mn1047 (memoNat [32,6597542084672,4,830472192])
def mn1112 : Nat := mn1048 + (memoNat [34359772096,4469043361662,8,520093696])
def mn1113 : Nat := mn1099 + (memoNat [35186554175521,4297132098,288230384741654656,8388608])
def mn1114 : Nat := mn1113 - (memoNat [34603040,2164802,140737492684928,274886295552])
def mn1115 : Nat := mn1088 + (memoNat [34394375200,72057662759436222,140737492684928,274869518592])
def mn1116 : Nat := mn1115 - (memoNat [34603040,2164802,140737492684928,274886295552])
def mn1117 : Nat := memoNat [5355470026775842419,15324950441774982505,2966142436300638806,181047002829477]
def mn1118 : Nat := mn1115 + (memoNat [34017214658593,18302558381533233350,139611592609234943,25165312])
def mn1119 : Nat := mn1117 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn1120 : Nat := mn880 + (memoNat [1065151855616,2233787545479608320,9079690616704,17042430238464])
def mn1121 : Nat := mn995 + (memoNat [1116892638902975455,2181362350030848,128])
def mn1122 : Nat := mn991 - (memoNat [36066214808683553,18444633080240013310,13844065117366386815,262143])
def mn1123 : Nat := mn1063 - (memoNat [17329851363939581951,70368744179647,3968])
def mn1124 : Nat := mn1077 - (memoNat [37156894909957152,72198329517281282,18311636080861905024,8650751])
def mn1125 : Nat := mn946 - (memoNat [3298604123136,72198331727609856,13510799284896000])
def mn1126 : Nat := mn924 - (memoNat [1119215972436181983,72127962853408576,4490405621792768,524264])
def mn1127 : Nat := Nat.xor mn1001 (memoNat [8070485785374132225,83751862278,896])
def mn1128 : Nat := mn1097 + (memoNat [69140480,18376935942888878084,4611826893359022331,274609471232])
def mn1129 : Nat := mn1019 - (memoNat [3367323600896,211175086227456,13510799284764928])
def mn1130 : Nat := mn997 + (memoNat [16033902126876820415,6544226498185285,14109778053055913728,7602176])
def mn1131 : Nat := mn1086 + (memoNat [1152953425808360449,71846558471028736,130604393086058240,256])
def mn1132 : Nat := mn1126 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1133 : Nat := mn525 + ((memoNat [35183331900417,2305842940494217216]) * 2 ^ 80)
def mn1134 : Nat := Nat.xor mn499 ((memoNat [18594940652093443,68157443,2048]) * 2 ^ 91)
def mn1135 : Nat := mn491 + (memoNat [1152922604153077760,6917535624711045120,8388736,24576])
def mn1136 : Nat := Nat.xor mn880 (memoNat [1376060826753991878,504403226997569536,0,525056])
def mn1137 : Nat := Nat.xor mn944 (memoNat [1100585369600,469762112,13541585341906944,24])
def mn1138 : Nat := mn944 - (memoNat [1152923736950735872,72128031635802048,9002801476665472,248])
def mn1139 : Nat := mn924 + (memoNat [1224979101900603458,192,13194139795584,24])
def mn1140 : Nat := Nat.xor mn1126 (memoNat [1412089623772921889,68732073984,0,525056])
def mn1141 : Nat := mn1017 + ((memoNat [33554431,2303591209400010688,4190208]) * 2 ^ 40)
def mn1142 : Nat := mn1018 + (memoNat [1123700848984064,4362862071906308,9214365112209506176])
def mn1143 : Nat := mn999 + (memoNat [1155173338814874624,6755399441055750,13835058467599024256])
def mn1144 : Nat := mn1143 - (memoNat [1152922638512849920,72128031568693248,4503599761588352,256])
def mn1145 : Nat := mn1069 + (memoNat [34052648172577,18374616046437990466,283726784980062207,8388352])
def mn1146 : Nat := Nat.xor mn1057 ((memoNat [2097251,2308094809430032768,9529458972,262144]) * 2 ^ 20)
def mn1147 : Nat := mn1069 + (memoNat [1152991876606853122,6442450944,432345577112477824])
def mn1148 : Nat := Nat.xor mn1132 (memoNat [1375884904893547521,504403226984972288,0,525056])
def mn1149 : Nat := mn914 - (memoNat [16215281892243504194,18300447317196531711,4503599761719295,523520])
def mn1150 : Nat := mn1030 + (memoNat [1116892707622519775,2181362350030848,136])
def mn1151 : Nat := Nat.xor mn1093 (memoNat [217376748489146371,2214658178,148618792937743104,8650752])
def mn1152 : Nat := mn910 - (memoNat [38387215100838978,72127896285743108,148614394086035456,17301240])
def mn1153 : Nat := mn1119 - (memoNat [36028764841312289,2308094740307900544,8796093284484,8589934352])
def mn1154 : Nat := mn910 - (memoNat [2382547103991759938,72127894205233088,9002801476796544,1048312])
def mn1155 : Nat := mn986 - (memoNat [16215281892243471426,18230641520824807421,4503599761592319,523520])
def mn1156 : Nat := Nat.xor mn1036 (memoNat [8070485716654653505,83756056582,896])
def mn1157 : Nat := mn988 - (memoNat [17367077496978078786,18230641522905180159,4503599761588351,523520])
def mn1158 : Nat := mn1049 - (memoNat [2416286718840831075,68725768192,0,786432])
def mn1159 : Nat := mn1119 - (memoNat [35152194403361,18374686415249276994,288230384741654655,8388352])
def mn1160 : Nat := mn1113 - (memoNat [2417377468735291426,2099200,4096,786432])
def mn1161 : Nat := mn764 + (memoNat [70370892709922,4297066562,288230380450881536,8388608])
def mn1162 : Nat := Nat.xor mn843 ((memoNat [130059031429513219,70254593,6144]) * 2 ^ 91)
def mn1163 : Nat := Nat.xor mn575 (memoNat [260118062852735009,2097152,31761283153920,26388279853056])
def mn1164 : Nat := mn897 + (memoNat [1099511627776,0,9079690616704,17042430230528])
def mn1165 : Nat := mn1151 + (memoNat [36099165763141665,4297132034,288230384741785600,8388608])
def mn1166 : Nat := Nat.xor mn919 (memoNat [1160838194485298176,504403570584465408,0,786944])
def mn1167 : Nat := mn911 - (memoNat [39513079574167585,70231378620352,4499201715077120,785912])
def mn1168 : Nat := mn981 + (memoNat [17255471603525911519,4688317580832669695,8,17179344896])
def mn1169 : Nat := mn1034 + (memoNat [1152921504641515520,6741085388800,140,805306368])
def mn1170 : Nat := Nat.xor mn989 (memoNat [1405158268111716385,432345632949153792,0,786944])
def mn1171 : Nat := mn1051 + (memoNat [18410680092318498783,2201168642047,4,268173312])
def mn1172 : Nat := mn1052 + (memoNat [17220568740773528510,4471123869695,8,536346624])
def mn1173 : Nat := mn1100 + (memoNat [1152921504641450016,2298054,128,25165824])
def mn1174 : Nat := Nat.xor mn1058 (memoNat [1413004589246126176,432345976550733824,0,786944])
def mn1175 : Nat := mn1115 + (memoNat [18409589376783745024,65601,0,8126464])
def mn1176 : Nat := Nat.xor mn1088 (memoNat [1375955479796358147,72058075074265088,0,524544])
def mn1177 : Nat := mn920 + (memoNat [2377900674153252930,74307261333246080,149533585838212,274609472016])
def mn1178 : Nat := mn1177 - (memoNat [36028798092739617,2380222771809484864,4398046642180,8589934600])
def mn1179 : Nat := mn1177 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn1180 : Nat := mn1179 - (memoNat [36028798092739617,2380222771809484864,4398046642180,8589934600])
def mn1181 : Nat := mn1179 + (memoNat [18375742043046543294,4535617517439,4323446975031402496,528482288])
def mn1182 : Nat := memoNat [7625321618140087857,8326284117565285473,12054674486275300166,181570704151692]
def mn1183 : Nat := memoNat [6435243217515006513,10706436522646090853,12189778081076308554,181579310601348]
def mn1184 : Nat := mn1182 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn1185 : Nat := memoNat [7659063362253833809,13082223791601724577,2687191380218432330,181587623974036]
def mn1186 : Nat := memoNat [7660224481966213682,13084473323603403873,7442992728455600966,181587347149972]
def mn1187 : Nat := memoNat [6470146048055133778,13082083056193811681,2966414565436910154,181587632100500]
def mn1188 : Nat := memoNat [5281161695963171377,13084402954859361507,7582604321064839878,181587363402900]
def mn1189 : Nat := mn1187 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn1190 : Nat := mn1184 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1191 : Nat := mn698 + (memoNat [18410716375129522143,65471,4063232,8184])
def mn1192 : Nat := Nat.xor mn682 (memoNat [216172784261267522,483250929792,4398047297536,268435472])
def mn1193 : Nat := mn581 + (memoNat [3298537997312,4613942216287780864,12582908,24576])
def mn1194 : Nat := mn1193 - (memoNat [37154732359320609,2251799813685314,4611690553912983556,8])
def mn1195 : Nat := mn936 + ((memoNat [33522687,18444492273895866368,4190207]) * 2 ^ 50)
def mn1196 : Nat := mn937 + ((memoNat [562949986943999,18444492273895833631,4190207]) * 2 ^ 51)
def mn1197 : Nat := Nat.xor mn914 (memoNat [8070450635327245312,434597501480220672,4,768])
def mn1198 : Nat := mn1197 - (memoNat [37154732359320609,2251799813685314,4611690553912983556,8])
def mn1199 : Nat := memoNat [7624160500575226450,13084477859225250979,7298873138038131534,181587892409484]
def mn1200 : Nat := mn1199 - (memoNat [37154732359320609,2251799813685314,4611690553912983556,8])
def mn1201 : Nat := mn1190 + (memoNat [2380188686983594017,70368811286594,4503599761588348,524288])
def mn1202 : Nat := Nat.xor mn1199 (memoNat [246293825912931,15047133378,144115192370827272,8388608])
def mn1203 : Nat := mn1187 + (memoNat [1125933192872960,2254069703901122,4611681757819699204,268435448])
def mn1204 : Nat := mn1203 - (memoNat [37154732359320609,2251799813685314,4611690553912983556,8])
def mn1205 : Nat := mn1190 + (memoNat [37154697999515681,2147618948,144115192370827260,16777216])
def mn1206 : Nat := Nat.xor mn1188 (memoNat [1073741824,4823718035520,30786326495232,536870936])
def mn1207 : Nat := mn1178 - (memoNat [18445688508187148288,4297132031,14123288302584864768,8388607])
def mn1208 : Nat := memoNat [7662476350499374674,5948310875612161187,16666365040188283718,181561845781652]
def mn1209 : Nat := mn1178 - (memoNat [1152958853711659008,70368880492542,13844065117366386944,262143])
def mn1210 : Nat := mn1208 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn1211 : Nat := mn1179 - (memoNat [18410785646508508161,2251801963333631,288225986695012352,8388600])
def mn1212 : Nat := mn1208 + (memoNat [36028798092740609,4760443275809128450,4398046642180,16911433736])
def mn1213 : Nat := mn1212 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn1214 : Nat := mn1179 - (memoNat [1152958886997656576,2392537371246528,9002801476534528,262136])
def mn1215 : Nat := mn1184 + (memoNat [37154699073291297,2380145593260441728,8796093284352,7784628240])
def mn1216 : Nat := mn1177 - (memoNat [1152994039157489697,140741921802240,14132291104061399296,8650743])
def mn1217 : Nat := mn1210 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1218 : Nat := mn624 + (memoNat [100729856,2251799813685248,431296723550216,26388279066624])
def mn1219 : Nat := mn700 - ((memoNat [2377900602177847295,69208196,4899916394444881920]) * 2 ^ 35)
def mn1220 : Nat := Nat.xor mn740 ((memoNat [1,15047065600,4194692,787200]) * 2 ^ 25)
def mn1221 : Nat := Nat.xor mn656 ((memoNat [1,35014,4262020,262152]) * 2 ^ 26)
def mn1222 : Nat := mn991 + ((memoNat [1073774591,2162688,134217732]) * 2 ^ 35)
def mn1223 : Nat := mn1222 - (memoNat [33792,2380225041766809600,4,8858370048])
def mn1224 : Nat := mn972 + ((memoNat [33,74309393849513920,134217732,261888]) * 2 ^ 20)
def mn1225 : Nat := mn1224 - (memoNat [33792,2380225041766809600,4,8858370048])
def mn1226 : Nat := mn1212 + (memoNat [32832,2269961654402,4,285212672])
def mn1227 : Nat := mn1212 - (memoNat [960,2380222771805155198,0,8573157376])
def mn1228 : Nat := mn1226 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1229 : Nat := mn1227 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1230 : Nat := mn1227 - (memoNat [64,4329604,0,16777216])
def mn1231 : Nat := mn1226 - (memoNat [67648,4760450083537948804,8,17733517312])
def mn1232 : Nat := mn845 + (memoNat [0,4611760785285316608,145277277175808,8796093038592])
def mn1233 : Nat := mn1232 - (memoNat [33792,2380225041766809600,4,8858370048])
def mn1234 : Nat := mn1210 + (memoNat [1073775616,2380220501919268928,4398046642180,8321499144])
def mn1235 : Nat := mn1234 - (memoNat [33792,2380225041766809600,4,8858370048])
def mn1236 : Nat := mn1177 + (memoNat [2181499788984320,4535615352832,8935141926991028224,520093696])
def mn1237 : Nat := mn956 + (memoNat [1152921539035791360,68717314046,281474985238784,549747425536])
def mn1238 : Nat := mn1236 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1239 : Nat := mn1237 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1240 : Nat := mn1183 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn1241 : Nat := Nat.xor mn1237 (memoNat [2344195074336751715,203491330,31525197525811584,9961472])
def mn1242 : Nat := mn1199 + (memoNat [37119546913456160,66,4467575361542156288,8])
def mn1243 : Nat := mn1242 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1244 : Nat := mn1186 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn1245 : Nat := mn1189 - (memoNat [18445653356027315167,2251799746576319])
def mn1246 : Nat := mn1188 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn1247 : Nat := mn1189 + (memoNat [2181499789018112,2254065473878018,8935141926991028228,260046848])
def mn1248 : Nat := mn1246 + (memoNat [35218731893793,2256339663255488,4611686155866341384,528482304])
def mn1249 : Nat := mn1248 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1250 : Nat := Nat.xor mn615 (memoNat [36283884765184,6612102152192,432345564231790592,24576])
def mn1251 : Nat := mn615 + (memoNat [18410646006385344479,2194728288191,18158509295220416512,8183])
def mn1252 : Nat := mn583 + (memoNat [3300685512738,4611692615497285696,12582912,24576])
def mn1253 : Nat := mn752 - (memoNat [108085291544249344,74377563568271356,8800384188420,8573149208])
def mn1254 : Nat := mn940 + (memoNat [1152886354594496512,66571993088,18302628881338728448,255])
def mn1255 : Nat := mn940 + (memoNat [1116822372129701855,64424509376,18158509290921259008,247])
def mn1256 : Nat := mn916 + (memoNat [3458764619047307298,144115394234290240,0,768])
def mn1257 : Nat := mn1256 - (memoNat [36063982464794657,2147483712,144119590417469440,8])
def mn1258 : Nat := mn1242 - (memoNat [36028797018964000,66,4398046642176,8])
def mn1259 : Nat := mn1258 - (memoNat [36063982464794657,2147483712,144119590417469440,8])
def mn1260 : Nat := mn1236 + (memoNat [1024,2380220504001808386,0,8329887744])
def mn1261 : Nat := mn1258 + (memoNat [2251868533164032,4503599627370500,9223372311732682752])
def mn1262 : Nat := mn1244 + (memoNat [35185445830721,2151813250,144115192370827264,16777216])
def mn1263 : Nat := mn1262 - (memoNat [36063982464794657,2147483712,144119590417469440,8])
def mn1264 : Nat := mn1247 + (memoNat [35185445830689,2149648386,144110794324185088,8388600])
def mn1265 : Nat := mn1247 + ((memoNat [1108313087,18442240473947963392,4294959103]) * 2 ^ 55)
def mn1266 : Nat := Nat.xor mn1248 ((memoNat [1108378625,0,4294967296]) * 2 ^ 55)
def mn1267 : Nat := mn1246 + (memoNat [33286063104,2256337513742274,4467566565448871944,536870904])
def mn1268 : Nat := mn1237 - (memoNat [1154049604679893025,70366733008960,18311636080861901056,262143])
def mn1269 : Nat := mn1210 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn1270 : Nat := mn1183 - (memoNat [17184678447790687200,2181435234654147,423325183449378560,24903656])
def mn1271 : Nat := mn1226 - (memoNat [35185445897313,2251801969828038,144115192370827272,33554432])
def mn1272 : Nat := Nat.xor mn1216 (memoNat [241591945216,4506292976683012,4755801348237168644,276824064])
def mn1273 : Nat := mn1217 - (memoNat [18445653358174864417,2251799750770623,8])
def mn1274 : Nat := mn1216 + (memoNat [1090748820750303,4537762836414,4467570963495514112,520093696])
def mn1275 : Nat := mn1269 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1276 : Nat := Nat.xor mn783 ((memoNat [1133838081196039,2147483648,4398046515200]) * 2 ^ 45)
def mn1277 : Nat := Nat.xor mn598 (memoNat [216172782113783904,2111686,30786326364160,25165840])
def mn1278 : Nat := mn640 + (memoNat [36028798092739585,2380222771807385598,131076,8581545992])
def mn1279 : Nat := Nat.xor mn640 (memoNat [36028797018964064,4272324,131072,16777224])
def mn1280 : Nat := Nat.xor mn1077 (memoNat [246290604621824,2162243586,144115192370823168,8388608])
def mn1281 : Nat := Nat.xor mn923 (memoNat [216172782113783904,2556102,26388279984128,25165840])
def mn1282 : Nat := mn975 + (memoNat [35185480433633,2143156156,144255929863377024,274861129728])
def mn1283 : Nat := Nat.xor mn957 (memoNat [36028797018964064,4589764,4398046511104,16777224])
def mn1284 : Nat := Nat.xor mn1213 (memoNat [1073840161,6954021814336,12,805306368])
def mn1285 : Nat := Nat.xor mn1182 (memoNat [216172782113783904,2570432,26388279853056,25165840])
def mn1286 : Nat := Nat.xor mn1227 (memoNat [192,6666274023812,0,847249408])
def mn1287 : Nat := mn1227 - (memoNat [1073775713,2380220504008302790,4,8355053568])
def mn1288 : Nat := mn1216 + (memoNat [1125934266580992,74910804146176,4755801348237168640,528482304])
def mn1289 : Nat := mn1237 - (memoNat [1118020807660929057,70366735173634,18311627284768616704,8650735])
def mn1290 : Nat := mn1269 + (memoNat [1073775649,2380222771811514366,4398046642180,8581545992])
def mn1291 : Nat := Nat.xor mn1269 (memoNat [0,405700,4398046642176,16777224])
def mn1292 : Nat := mn1236 + (memoNat [16138647065589710848,4160884739,279223185218477824,16252928])
def mn1293 : Nat := mn1237 + (memoNat [16138647065589710848,4160884739,279223185218477824,16252928])
def mn1294 : Nat := mn1240 + (memoNat [16174676964302389281,4225828993,283735581073350528,7864336])
def mn1295 : Nat := mn1153 + (memoNat [33320565760,13758426561592166336,277076938727543,532575944952])
def mn1296 : Nat := mn1245 + (memoNat [34902894964637695,70370824552386])
def mn1297 : Nat := Nat.xor mn1216 (memoNat [32864,2378322828603754624,144119590417469444,8598323208])
def mn1298 : Nat := mn1206 + (memoNat [37151433720660001,18446603336086978626,4598179754628218503,8])
def mn1299 : Nat := memoNat [4129328776518127153,13086586655749879015,16796969433274345930,181587631576212]
def mn1300 : Nat := mn1267 + ((memoNat [34390145949,2371145203676350272,140862046604928]) * 2 ^ 20)
def mn1301 : Nat := mn1248 - (memoNat [1154049604679893025,70366733008960,18311636080861901056,262143])
def mn1302 : Nat := mn619 + (memoNat [0,2198956212224,18442240474086375296,8191])
def mn1303 : Nat := mn1302 - (memoNat [36029897638936609,70368811286592,4507997808230528,8])
def mn1304 : Nat := mn585 + (memoNat [36029896531640353,4611762984241528832,12582912,24576])
def mn1305 : Nat := mn1304 - (memoNat [36029897638936609,70368811286592,4507997808230528,8])
def mn1306 : Nat := Nat.xor mn944 (memoNat [1133871366144,69189253120,13510799016329216,768])
def mn1307 : Nat := Nat.xor mn924 ((memoNat [2097251,2746595145679232,8589934848,8192]) * 2 ^ 20)
def mn1308 : Nat := mn918 + (memoNat [2341871909311940641,144185762978469888,0,768])
def mn1309 : Nat := mn1308 - (memoNat [36029897638936609,70368811286592,4507997808230528,8])
def mn1310 : Nat := mn1203 + (memoNat [18446743008523059200,1,4607182556104753024])
def mn1311 : Nat := mn1310 - (memoNat [36029897638936609,70368811286592,4507997808230528,8])
def mn1312 : Nat := mn1187 + (memoNat [38280699911866401,4573968371548166,13835058467599024128])
def mn1313 : Nat := mn1312 - (memoNat [36029897638936609,70368811286592,4507997808230528,8])
def mn1314 : Nat := mn1247 + (memoNat [34085899599905,4230023170,283722386933424000,8388600])
def mn1315 : Nat := memoNat [6437422518211596849,13088772622306880615,2669168734834608466,181588160582789]
def mn1316 : Nat := mn1247 + (memoNat [36099166836883489,70375186628608,432345577112481792])
def mn1317 : Nat := Nat.xor mn1247 (memoNat [71468290408448,15502147776,445887162455323520,24])
def mn1318 : Nat := mn1270 + (memoNat [16102584184818630656,2080510019,139611592609238912,16252928])
def mn1319 : Nat := mn1217 - (memoNat [18410750461062743072,2181428926218237,8])
def mn1320 : Nat := mn1183 - (memoNat [2271011577170756575,2322168562057024,4490405621661824,524264])
def mn1321 : Nat := mn1232 - (memoNat [3533179460788487234,2251799819976704,8,786432])
def mn1322 : Nat := mn1294 - (memoNat [35185445830689,70373041309698,288225986695012352,8388600])
def mn1323 : Nat := mn1294 - (memoNat [1190110286358511649,2082607172,139607194562596736,17039352])
def mn1324 : Nat := mn628 + (memoNat [36028797086072865,70368744177664,431434028285952,26388279066624])
def mn1325 : Nat := mn1324 - (memoNat [1190111385904776225,2380222771811581952,4,8590196736])
def mn1326 : Nat := Nat.xor mn641 (memoNat [6924496639370461184,70368823869824,4507998077321344,524304])
def mn1327 : Nat := mn640 + (memoNat [13758390211101851615,2076315779,139611592609369984,15728648])
def mn1328 : Nat := mn1126 + (memoNat [1190113584962634785,72198331662598144,9007199523176576,262144])
def mn1329 : Nat := mn1328 - (memoNat [1190111385904776225,2380222771811581952,4,8590196736])
def mn1330 : Nat := mn956 + (memoNat [16137487083004493824,4223731841,283735581073219456,7602192])
def mn1331 : Nat := mn1330 - (memoNat [1190111385904776225,2380222771811581952,4,8590196736])
def mn1332 : Nat := mn1215 + (memoNat [36028797018996769,77178549043200,4,805306368])
def mn1333 : Nat := mn1215 - (memoNat [1154082588885779456,2380145593262538752,0,7784890368])
def mn1334 : Nat := mn1234 + (memoNat [17293787384730615808,2269888118783,0,268173312])
def mn1335 : Nat := mn1234 - (memoNat [2343068074883712033,2380220501923463168,4,8322023424])
def mn1336 : Nat := Nat.xor mn1236 (memoNat [2308131094019440673,203491330,31529595572453760,9961480])
def mn1337 : Nat := Nat.xor mn1237 (memoNat [5770308490858856547,205588546,31551585805664640,9699344])
def mn1338 : Nat := Nat.xor mn1237 (memoNat [5770273307560509440,2350907392,175666778176491904,1310736])
def mn1339 : Nat := Nat.xor mn1269 (memoNat [6960418778291109888,0,4398046642176,524296])
def mn1340 : Nat := memoNat [7733372826972442227,15464698365370213605,11910572488044399438,181596205520036]
def mn1341 : Nat := mn1340 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn1342 : Nat := mn1340 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1343 : Nat := mn1341 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1344 : Nat := memoNat [6542133273348916850,15460054026039962913,2678192976788539982,181596213646500]
def mn1345 : Nat := memoNat [5353148921256954449,15462373924705512739,7294382732416469706,181595944948900]
def mn1346 : Nat := mn1344 + (memoNat [1090782106781663,4505865220454338,8935141926991028228,260046848])
def mn1347 : Nat := mn1318 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1348 : Nat := mn688 + (memoNat [1090748820784127,2251868600270850,4467570967790481412,268435456])
def mn1349 : Nat := Nat.xor mn688 (memoNat [70370891890690,483250929664,288230380446703644,268435456])
def mn1350 : Nat := mn669 + (memoNat [3298538029056,6917533427835207682,12582912,24576])
def mn1351 : Nat := mn1350 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1352 : Nat := mn1079 + ((memoNat [1023,18444492273895866430,4190207]) * 2 ^ 50)
def mn1353 : Nat := mn1352 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1354 : Nat := mn986 + (memoNat [3458764548180345856,216172921700225026,0,768])
def mn1355 : Nat := mn1354 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1356 : Nat := mn1242 - (memoNat [1125934266581024,66,4611686155866341376])
def mn1357 : Nat := mn1356 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1358 : Nat := mn643 + ((memoNat [1073808385,2201170739264,279449964544,17179869192]) * 2 ^ 10)
def mn1359 : Nat := mn1358 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1360 : Nat := mn1344 + (memoNat [1125933192872960,2254067556417538,4467570963495514116,268435456])
def mn1361 : Nat := mn1360 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1362 : Nat := mn1346 + (memoNat [17257830058149543937,70373106321473,292733984503242880,8126464])
def mn1363 : Nat := mn1362 - (memoNat [1161119712412673,2251801961168898,4755801348237168640])
def mn1364 : Nat := Nat.xor mn1360 (memoNat [35190814736417,4810432645570,288230384741670936,545259520])
def mn1365 : Nat := Nat.xor mn1362 (memoNat [7516356704,6953961064902,144115192370827284,813694976])
def mn1366 : Nat := memoNat [6544385175168078386,15466809423262096547,16369136252016736846,181596196869284]
def mn1367 : Nat := mn1345 + (memoNat [1161152998442977,4505869515286334,9223372311732682756,243269632])
def mn1368 : Nat := mn711 + ((memoNat [1099511627779,64,12984588,786432]) * 2 ^ 25)
def mn1369 : Nat := mn1368 - (memoNat [32800,2269959489602,4,276824064])
def mn1370 : Nat := mn745 + (memoNat [67141600,2269955225536,290413072089092,17592446091264])
def mn1371 : Nat := Nat.xor mn745 (memoNat [67108928,4272258,308005258133504,17592202821632])
def mn1372 : Nat := mn1022 + (memoNat [103809024,2147483650,422212478050688,824633720832])
def mn1373 : Nat := mn1372 - (memoNat [32800,2269959489602,4,276824064])
def mn1374 : Nat := Nat.xor mn1047 (memoNat [34603040,2555968,140737493468032,824658886656])
def mn1375 : Nat := Nat.xor mn1048 (memoNat [34428945472,4589698,281474985890560,549772591104])
def mn1376 : Nat := mn1208 + (memoNat [34816,7138416517762252802,4,25769803776])
def mn1377 : Nat := mn1376 - (memoNat [32800,2269959489602,4,276824064])
def mn1378 : Nat := mn1212 - (memoNat [1024,2251799815849986,0,8388608])
def mn1379 : Nat := mn1378 - (memoNat [32800,2269959489602,4,276824064])
def mn1380 : Nat := mn851 + (memoNat [0,4611690416541138944,145277277175808,8796093038592])
def mn1381 : Nat := mn1380 - (memoNat [32800,2269959489602,4,276824064])
def mn1382 : Nat := Nat.xor mn1367 (memoNat [7516225632,6665795602626,144115192370827268,813694976])
def mn1383 : Nat := mn1382 - (memoNat [32800,2269959489602,4,276824064])
def mn1384 : Nat := mn1117 + (memoNat [0,139607186107011068,9223653236962238456,549218943487])
def mn1385 : Nat := mn1364 + (memoNat [17257793773157482528,69341313,144115192370827264,16515072])
def mn1386 : Nat := mn1119 + (memoNat [0,139607186107011068,9223653236962238456,549218943487])
def mn1387 : Nat := mn1386 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn1388 : Nat := mn1362 - (memoNat [3298638692352,211108514234370,13510799284765056])
def mn1389 : Nat := mn1320 + (memoNat [67584,4760375172727173052,18302633279385366536,17163091975])
def mn1390 : Nat := mn706 + (memoNat [0,2305772640469581824,18442240474086375296,8191])
def mn1391 : Nat := Nat.xor mn690 (memoNat [100892672,422695715995648,9007199657394972,268435456])
def mn1392 : Nat := mn671 + (memoNat [1126999419518976,6917533425754898432,12582912,24576])
def mn1393 : Nat := mn1392 - (memoNat [1127033812812800,2322168624971778,4616189755627929728])
def mn1394 : Nat := mn1017 + ((memoNat [34359738367,18444492273895931840,4294963199]) * 2 ^ 40)
def mn1395 : Nat := Nat.xor mn999 ((memoNat [2097251,2744381427681344,8589934848,256]) * 2 ^ 20)
def mn1396 : Nat := mn988 + (memoNat [2306968943480341504,216172919619852288,0,768])
def mn1397 : Nat := mn1396 - (memoNat [1127033812812800,2322168624971778,4616189755627929728])
def mn1398 : Nat := Nat.xor mn1203 (memoNat [1100619972608,64,13541585342825344,24])
def mn1399 : Nat := mn1398 - (memoNat [1127033812812800,2322168624971778,4616189755627929728])
def mn1400 : Nat := mn1183 + (memoNat [73183497165996098,67109056,13194139926528,24])
def mn1401 : Nat := mn1400 - (memoNat [1127033812812800,2322168624971778,4616189755627929728])
def mn1402 : Nat := mn1361 + (memoNat [1160021239923713,2181433216991234,4895412940846407552])
def mn1403 : Nat := mn1360 - (memoNat [1128132285301760,2392537369149442,4476578163018690816])
def mn1404 : Nat := mn1346 + (memoNat [1196271872245762,4362076160,432345577112481792])
def mn1405 : Nat := mn1404 - (memoNat [1127033812812800,2322168624971778,4616189755627929728])
def mn1406 : Nat := mn1386 - (memoNat [35152159833121,18444492278260107328,14123288302584864767,8388607])
def mn1407 : Nat := mn1380 - (memoNat [3569173073435295778,2149580802,0,786432])
def mn1408 : Nat := mn713 + ((memoNat [16777217,1,6492356,393216]) * 2 ^ 26)
def mn1409 : Nat := mn1408 - (memoNat [1190111385904775201,2269959421952,4,268697600])
def mn1410 : Nat := Nat.xor mn904 (memoNat [32768,83751862272,171536698834948,26389084372992])
def mn1411 : Nat := Nat.xor mn891 ((memoNat [16777233,38280597942240256,68719476736,8192]) * 2 ^ 16)
def mn1412 : Nat := mn1024 + (memoNat [1125899976048640,67108864,422212478054656,824633720832])
def mn1413 : Nat := mn1412 - (memoNat [1190111385904775201,2269959421952,4,268697600])
def mn1414 : Nat := Nat.xor mn1171 (memoNat [0,6612102152192,140737493495812,825439027200])
def mn1415 : Nat := mn1172 + ((memoNat [1055,4679240012701497344,8589934856,16760832]) * 2 ^ 15)
def mn1416 : Nat := mn1210 + (memoNat [1125899906877440,7138346146937700352,4,25769803776])
def mn1417 : Nat := mn1416 - (memoNat [1190111385904775201,2269959421952,4,268697600])
def mn1418 : Nat := mn1234 + (memoNat [17293787384730615808,2377900603249524735,0,8589672448])
def mn1419 : Nat := mn1215 - (memoNat [2343068040523939873,4194302,13835057917843210240,524287])
def mn1420 : Nat := mn1367 + (memoNat [1125899906842656,69408964,0,25165824])
def mn1421 : Nat := mn1367 - (memoNat [1188985485997932545,2269890012988,4,243531776])
def mn1422 : Nat := mn1382 + ((memoNat [34635743,0,4160749568]) * 2 ^ 55)
def mn1423 : Nat := mn1382 - (memoNat [2379061687530586145,2269959354304,4,260571136])
def mn1424 : Nat := mn1362 + (memoNat [1160053452212257,4435498627954624,9218868711971094404,260046848])
def mn1425 : Nat := mn1362 + (memoNat [1124868006381568,4435496478306174,9074753519600267140,251658240])
def mn1426 : Nat := mn1294 + (memoNat [67584,4760304801835511804,18158522485061181448,17163091983])
def mn1427 : Nat := mn1159 + (memoNat [33320633344,72057660609787772,18302910356324094080,549739036927])
def mn1428 : Nat := Nat.xor mn754 ((memoNat [33,2322098670169948622,13510812169666948]) * 2 ^ 25)
def mn1429 : Nat := mn792 + ((memoNat [17733517295,1151690085940363229,74309391502802876]) * 2 ^ 26)
def mn1430 : Nat := Nat.xor mn828 (memoNat [7516192768,2147486146,144115200960761856,8388608])
def mn1431 : Nat := Nat.xor mn813 (memoNat [3298538029056,492581679477124,13510798882112384,16777216])
def mn1432 : Nat := mn1069 + (memoNat [34085934202913,18446673707047911490,139611592609239039,8388608])
def mn1433 : Nat := Nat.xor mn1069 (memoNat [2199127064576,422212867785154,9007199523176576,8388608])
def mn1434 : Nat := mn1057 + (memoNat [2305878296665099233,216172988270120960,0,768])
def mn1435 : Nat := mn1434 - (memoNat [36284992061473,70370960867328,148618792132415616])
def mn1436 : Nat := mn1247 + (memoNat [34085899599905,2082539522,139611592609238912,8388608])
def mn1437 : Nat := Nat.xor mn1315 (memoNat [36134350135230464,12886999232,288256773021523968,16])
def mn1438 : Nat := Nat.xor mn1240 (memoNat [216207969707098211,2097280,30786326495232,24])
def mn1439 : Nat := mn1438 - (memoNat [36284992061473,70370960867328,148618792132415616])
def mn1440 : Nat := mn1361 + (memoNat [1160054525921281,4433233030676482,9362983904341921664])
def mn1441 : Nat := mn1361 + (memoNat [1123769533859808,4362862069809154,9214365112209506048])
def mn1442 : Nat := mn1344 + (memoNat [2287087264992225,6755399438958596,13835058467599024128])
def mn1443 : Nat := mn1442 - (memoNat [36284992061473,70370960867328,148618792132415616])
def mn1444 : Nat := mn814 + (memoNat [67108896,2164802,290550511042560,17592194433024])
def mn1445 : Nat := mn1444 - (memoNat [1190111385904742433,2164802,0,8650752])
def mn1446 : Nat := mn794 + (memoNat [35184439197761,4194304,435827779829760,26388279066624])
def mn1447 : Nat := mn1446 - (memoNat [1190111385904742433,2164802,0,8650752])
def mn1448 : Nat := mn1445 - ((memoNat [1,0,4329604,262144]) * 2 ^ 26)
def mn1449 : Nat := mn814 - (memoNat [2380222771809484834,2164802,4294967296,8912896])
def mn1450 : Nat := mn1088 + (memoNat [35184441294913,4194304,422212478050560,824633720832])
def mn1451 : Nat := mn1450 - (memoNat [1190111385904742433,2164802,0,8650752])
def mn1452 : Nat := Nat.xor mn1115 (memoNat [260082878480646144,0,140737493467136,824634507264])
def mn1453 : Nat := Nat.xor mn1176 (memoNat [103809024,395396,281474985889920,549772591104])
def mn1454 : Nat := mn1248 + ((memoNat [33587199,70368744177666,134217732]) * 2 ^ 30)
def mn1455 : Nat := mn1269 + (memoNat [17256667872176999424,7140597946686306237,12,25761153024])
def mn1456 : Nat := mn1217 + ((memoNat [2376738419427507201,132,283586039170203652]) * 2 ^ 35)
def mn1457 : Nat := mn1294 - (memoNat [1190109186812280865,2015633544,135103594801008384,33816568])
def mn1458 : Nat := Nat.xor mn1362 (memoNat [35191888281633,2165190,144115192370827264,8388608])
def mn1459 : Nat := mn1362 - (memoNat [1190076200458911744,135300,18302628881338724352,17039359])
def mn1460 : Nat := mn1382 + (memoNat [17257793772083773440,2267742732287,4,268173312])
def mn1461 : Nat := mn1382 + (memoNat [16067682386179031007,2267740567485,4,259522560])
def mn1462 : Nat := mn832 + ((memoNat [35184373137409,69273664,131072]) * 2 ^ 90)
def mn1463 : Nat := mn834 + ((memoNat [35184373137409,69273664,131072]) * 2 ^ 90)
def mn1464 : Nat := mn832 + (memoNat [1190111385904742433,2305845208239112192,4194304,270336])
def mn1465 : Nat := mn834 + (memoNat [1190111385904742433,2305845208239112192,4194304,270336])
def mn1466 : Nat := mn1117 + (memoNat [1099511627776,70368811286528,4644337254273024,274877906944])
def mn1467 : Nat := mn1119 + (memoNat [1099511627776,70368811286528,4644337254273024,274877906944])
def mn1468 : Nat := mn1117 + (memoNat [37189915657667617,72057662759503872,0,262400])
def mn1469 : Nat := mn1119 + (memoNat [37189915657667617,72057662759503872,0,262400])
def mn1470 : Nat := mn1267 + (memoNat [72127963855847490,6444615746,432349975159123968,8388616])
def mn1471 : Nat := mn1247 + (memoNat [16138684451201744929,8590069827,576460769483309056,16252928])
def mn1472 : Nat := mn862 + (memoNat [0,2305917776004513792,145277277175808,8796093038592])
def mn1473 : Nat := mn1294 + (memoNat [1154082589959520256,2097216,4398046642176,262152])
def mn1474 : Nat := mn1362 + (memoNat [1161086426415137,2149648448,288230384741654528,8388608])
def mn1475 : Nat := mn1384 + (memoNat [17256632687804841951,2269821009919,4,268173312])
def mn1476 : Nat := mn866 + (memoNat [0,4611688217517883392,145277277175808,8796093038592])
def mn1477 : Nat := mn1384 + (memoNat [18445617108616217600,2181431002398721,4607182556104753024])
def mn1478 : Nat := mn1420 + (memoNat [35218731893793,2256337515839490,4611686155866341384,536870912])
def mn1479 : Nat := mn1344 + (memoNat [16069969507803795424,9011736952700933,549755813896,536346625])
def mn1480 : Nat := mn872 + (memoNat [32,4611690416476061696,145277277175808,8796093038592])
def mn1481 : Nat := Nat.xor mn1444 (memoNat [36284086091809,6917966633673687040,9007200064242432,57344])
def mn1482 : Nat := mn1462 - (memoNat [2380224970901946434,140737626767360,9007199523176704,524288])
def mn1483 : Nat := mn1464 - (memoNat [2380224970901946434,140737626767360,9007199523176704,524288])
def mn1484 : Nat := mn1467 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn1485 : Nat := mn1469 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn1486 : Nat := mn1294 + (memoNat [17256632687804842975,2380082034319032319,4,8589672448])
def mn1487 : Nat := Nat.xor mn1294 (memoNat [36032103173849187,70368811286976,4507998076665984,8])
def mn1488 : Nat := mn1386 + (memoNat [17256632687804841951,2269821009919,4,268173312])
def mn1489 : Nat := mn1386 + (memoNat [18445617108616217600,2181431002398721,4607182556104753024])
def mn1490 : Nat := mn1479 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn1491 : Nat := mn1481 - (memoNat [1190112485450973217,70368813383680,4503599761588352,262144])
def mn1492 : Nat := mn1446 + (memoNat [2380188686983626753,70368811352064,4503599761588352,524288])
def mn1493 : Nat := mn752 + (memoNat [35185479385089,2147483648,144260461183897600,8796093022208])
def mn1494 : Nat := mn906 + (memoNat [2380189786462748737,70368815480832,4503603922337920,524288])
def mn1495 : Nat := mn752 + (memoNat [1099512676384,2305845208239048770,4194304,8396800])
def mn1496 : Nat := mn1053 + (memoNat [35185480433665,2147483648,144255929863504000,274877906944])
def mn1497 : Nat := mn997 + (memoNat [4503668346881984,9011668298104706,549755813896,520093697])
def mn1498 : Nat := mn1053 + (memoNat [1152921538966619168,72057662759567426,0,8388864])
def mn1499 : Nat := mn762 + (memoNat [2199058907168,4611690416476127298,145273116430336,8796101427200])
def mn1500 : Nat := mn1248 + (memoNat [2380223871355715617,70370958770240,148618792132415616,524288])
def mn1501 : Nat := Nat.xor mn1236 (memoNat [1073978401,2393733570694166598,28,8615100416])
def mn1502 : Nat := mn1236 + (memoNat [36028797018963968,2164738,4398046642176,8388616])
def mn1503 : Nat := Nat.xor mn1236 (memoNat [36063982464794657,15032385600,432349975159140352,8])
def mn1504 : Nat := mn1340 + (memoNat [35185445863425,2267809841152,144115192370827268,268435456])
def mn1505 : Nat := mn1340 + (memoNat [32736,2265660192702,4,260046848])
def mn1506 : Nat := mn1420 + (memoNat [2379062787076784193,70370895855616,4503599761588352,524288])
def mn1507 : Nat := mn1340 + (memoNat [1090748820751359,2251797666201598,4467570963495514112])
def mn1508 : Nat := mn1479 - ((memoNat [1108376543,0,133143986176]) * 2 ^ 51)
def mn1509 : Nat := Nat.xor mn1481 (memoNat [6603719835648,422225752621056,297237584801719040])
def mn1510 : Nat := Nat.xor mn752 (memoNat [234881120,6359234,989703138443264,8796101410816])
def mn1511 : Nat := mn814 + (memoNat [2380083130646134782,70362368770048,18018902100653625472,524287])
def mn1512 : Nat := mn1066 + (memoNat [1125934266647520,2256337578688446,4611686155866337288,528482304])
def mn1513 : Nat := mn1099 + (memoNat [1190043215179284511,140735477184512,18311636080861905152,262143])
def mn1514 : Nat := mn1244 + (memoNat [1125933192905727,2256337578686462,4611686155866341384,528482304])
def mn1515 : Nat := mn1236 - (memoNat [18410785647582249026,4297132161,288225986695012352,8388600])
def mn1516 : Nat := mn1342 + (memoNat [32736,2265660192702,4,260046848])
def mn1517 : Nat := mn1507 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1518 : Nat := mn1508 - (memoNat [35185445830689,2149648450,144115192370827264,8388608])
def mn1519 : Nat := mn1444 - (memoNat [69272452726850,16140898871919315010,432345577108287487,8380416])
def mn1520 : Nat := mn1368 + (memoNat [35185445830721,2199027519618,144115192370827264,16777216])
def mn1521 : Nat := mn665 + ((memoNat [1023,18444492273826592768,4425125887,268427264]) * 2 ^ 15)
def mn1522 : Nat := mn665 + (memoNat [1099512709120,2305843080147828736,4194308,268443648])
def mn1523 : Nat := mn667 + (memoNat [1099512709120,2305843080147828736,4194308,268443648])
def mn1524 : Nat := mn1372 + (memoNat [35219805602881,68723804290,144115192370827264,16777216])
def mn1525 : Nat := mn998 + (memoNat [1161085352706113,2251868537491588,4755801348237168640,16777216])
def mn1526 : Nat := mn982 + ((memoNat [1152956724412448769,64,4294971392]) * 2 ^ 60)
def mn1527 : Nat := mn984 + ((memoNat [1152956724412448769,64,4294971392]) * 2 ^ 60)
def mn1528 : Nat := mn1376 + (memoNat [35185445863457,4329538,144115192370827268,16777216])
def mn1529 : Nat := Nat.xor mn1177 (memoNat [33792,2380229453100875776,4,9395240960])
def mn1530 : Nat := mn1177 + (memoNat [36028798092705825,2269957324864,4398046642176,268435464])
def mn1531 : Nat := mn1226 - (memoNat [2216683087365119,2251799813685252,9079257119361855492])
def mn1532 : Nat := mn1505 - (memoNat [65472,4535615352704,8,520093696])
def mn1533 : Nat := mn1340 - (memoNat [1090748820751359,2251801961168898,4467570963495514112])
def mn1534 : Nat := mn1475 - (memoNat [16068773101713817534,4539776237567,8,536346624])
def mn1535 : Nat := mn1384 - (memoNat [1124834720351232,2181431136616450,4607182556104753024])
def mn1536 : Nat := mn667 + ((memoNat [1023,18444492273826592768,4425125887,268427264]) * 2 ^ 15)
def mn1537 : Nat := mn1522 - (memoNat [2251868533229568,4508139542020100,9223372311732682760,536870912])
def mn1538 : Nat := Nat.xor mn984 (memoNat [103321537536,2407396278272,985162447982732,275146342400])
def mn1539 : Nat := mn984 + (memoNat [1151795570340232192,69805725504767998,13835057917843210240,255])
def mn1540 : Nat := Nat.xor mn1179 (memoNat [101376,2384728778833133568,12,8858370048])
def mn1541 : Nat := mn1179 + (memoNat [34902863826091041,18444492273895866430,13835062315889852411,7])
def mn1542 : Nat := mn1341 - (memoNat [32736,2269955160002,4,260046848])
def mn1543 : Nat := mn1341 - (memoNat [1090748820751359,2251801961168898,4467570963495514112])
def mn1544 : Nat := mn1476 - (memoNat [2251868533229568,4508139542020100,9223372311732682760,536870912])
def mn1545 : Nat := mn1535 - (memoNat [1125934266614784,2254069771010050,4611686155866341380,268435456])
def mn1546 : Nat := mn577 + (memoNat [36028798126260257,64,140879356624896,8796093022216])
def mn1547 : Nat := mn579 + (memoNat [36028798126260257,64,140879356624896,8796093022216])
def mn1548 : Nat := mn577 + (memoNat [1099512710144,74381961619111936,4194308,8589942784])
def mn1549 : Nat := mn579 + (memoNat [1099512710144,74381961619111936,4194308,8589942784])
def mn1550 : Nat := mn1139 + (memoNat [37192080355787809,72127962918420480,9007199523176576,262144])
def mn1551 : Nat := mn910 + (memoNat [34569216,16066521301900066816,140737492422779,266287972352])
def mn1552 : Nat := mn910 + (memoNat [1152921538966585344,2308165246491035648,4,8589934848])
def mn1553 : Nat := mn956 + ((memoNat [1126467379920897,2251836321988641,2253998836944896]) * 2 ^ 46)
def mn1554 : Nat := mn1529 - ((memoNat [35434494943,0,124]) * 2 ^ 91)
def mn1555 : Nat := mn1178 + ((memoNat [1073774593,69208064,4611686018561605636]) * 2 ^ 35)
def mn1556 : Nat := mn1236 - (memoNat [1073775649,2380222771807320126,4,8581545984])
def mn1557 : Nat := Nat.xor mn1236 (memoNat [252447870811111457,2147483712,144145978697322496,24])
def mn1558 : Nat := mn641 + (memoNat [1100653527040,72567767498816,290554810335232,17592186052616])
def mn1559 : Nat := mn1294 + (memoNat [1154084786904498176,136314816,9002801476534528,262136])
def mn1560 : Nat := mn579 + (memoNat [33520640,16066521301900066816,136481309982715,8787503087616])
def mn1561 : Nat := Nat.xor mn579 (memoNat [36036496828924003,2305845208237015232,4398076002304,8200])
def mn1562 : Nat := mn1550 - (memoNat [72057596185479234,4760445543618969728,8796093284360,17179869200])
def mn1563 : Nat := mn1553 - (memoNat [36028798092739617,2380222771809484864,4398046642180,8589934600])
def mn1564 : Nat := mn1178 - (memoNat [33792,2380220501852160000,4,8321499136])
def mn1565 : Nat := mn1178 - (memoNat [34902863826158625,2251799813685310,13835062315889852420,7])
def mn1566 : Nat := mn1237 - (memoNat [1073775649,2380222771807320126,4,8581545984])
def mn1567 : Nat := Nat.xor mn1237 (memoNat [36275090844811363,2147483840,144119590417469440,8])
def mn1568 : Nat := mn1269 + (memoNat [1118087876692672512,2086801412,139607194562596736,17039352])
def mn1569 : Nat := mn600 + (memoNat [2197985165312,2305777038516158400,136481318240256,8796093038584])
def mn1570 : Nat := mn779 + (memoNat [70370926264354,4297066562,288371117939232768,8388608])
def mn1571 : Nat := Nat.xor mn481 (memoNat [34603008,0,145278213452672,9620726743040])
def mn1572 : Nat := mn481 + (memoNat [1099511627776,2305845208237015040,135296,274877915136])
def mn1573 : Nat := mn483 + (memoNat [1099511627776,2305845208237015040,135296,274877915136])
def mn1574 : Nat := mn911 + (memoNat [1152921538966585344,2308165246491035648,4,8589934848])
def mn1575 : Nat := mn911 + (memoNat [36028798127308833,64,145135539064960,274877906952])
def mn1576 : Nat := mn983 + ((memoNat [1152956724412448769,64,4294971392]) * 2 ^ 60)
def mn1577 : Nat := mn982 - (memoNat [1151795639059776512,69805862943721470,13835057917843210240,255])
def mn1578 : Nat := mn1054 + (memoNat [1152921538966619168,72057662759567426,0,8388864])
def mn1579 : Nat := mn1054 + (memoNat [35185480433665,2147483648,144255929863504000,274877906944])
def mn1580 : Nat := mn1120 + (memoNat [1227302401108640834,72128031572887552,4503599761588352,524544])
def mn1581 : Nat := Nat.xor mn1469 (memoNat [6803228399616,432768189412159488,9007200060047360,512])
def mn1582 : Nat := Nat.xor mn483 (memoNat [103809024,0,426753197740160,9070970929152])
def mn1583 : Nat := memoNat [3124007810880816821,12875130645649921385,2974859081009281494,163179939393701]
def mn1584 : Nat := mn911 - (memoNat [34636800,16210636489975922688,140737492684923,266287972352])
def mn1585 : Nat := Nat.xor mn911 (memoNat [1188950412221320423,72057800196360640,4398046642176,264])
def mn1586 : Nat := mn983 - (memoNat [34394375168,18446741941191180288,140737492684923,274609471488])
def mn1587 : Nat := mn983 - (memoNat [1151795639059776512,69805862943721470,13835057917843210240,255])
def mn1588 : Nat := Nat.xor mn1054 (memoNat [103809248,14748098,422212477784192,274886295552])
def mn1589 : Nat := mn1054 - (memoNat [1152886353520788479,72057660609923072,18302628881338732544,255])
def mn1590 : Nat := memoNat [3086816864431065748,15252892779019672937,2965860961315268950,180497247277477]
def mn1591 : Nat := mn1120 + (memoNat [37192045961378849,18374827148576815104,9007199523176447,261888])
def mn1592 : Nat := mn1571 - (memoNat [0,0,9079829028608,17042430230528])
def mn1593 : Nat := mn1573 - (memoNat [16140903194799568896,4467575090959216639,0,15872])
def mn1594 : Nat := mn578 + (memoNat [1099512710144,74381961619111936,4194308,8589942784])
def mn1595 : Nat := mn578 + (memoNat [36028798126260257,64,140879356624896,8796093022216])
def mn1596 : Nat := mn666 + (memoNat [1099512709120,2305843080147828736,4194308,268443648])
def mn1597 : Nat := mn742 + (memoNat [68171866308642,13835055858408425538,288230242999345151,8372224])
def mn1598 : Nat := mn751 + (memoNat [1099512676384,2305845208239048770,4194304,8396800])
def mn1599 : Nat := mn751 + (memoNat [35185479385089,2147483648,144260461183897600,8796093022208])
def mn1600 : Nat := mn833 + (memoNat [1190111385904742433,2305845208239112192,4194304,270336])
def mn1601 : Nat := mn833 + ((memoNat [35184373137409,69273664,131072]) * 2 ^ 90)
def mn1602 : Nat := mn482 - (memoNat [34603008,0,145277407063936,8521215115264])
def mn1603 : Nat := mn484 + (memoNat [2305841978421610496,16285014190987350016,135295,274877899264])
def mn1604 : Nat := mn578 - (memoNat [33520640,2231463246617903104,145277403004924,8787503087616])
def mn1605 : Nat := mn578 - (memoNat [18410716375129522143,2305845208237014975,4398050574336,8184])
def mn1606 : Nat := mn666 - (memoNat [33521664,2128089186304,145277403004924,8795824586752])
def mn1607 : Nat := mn710 + (memoNat [69271378984994,16140901068792858690,288230243003539455,8380416])
def mn1608 : Nat := Nat.xor mn751 (memoNat [100663520,14748098,426752648151040,8796101410816])
def mn1609 : Nat := mn584 + (memoNat [72056496672769090,16215278628068393088,4393747611651,8589926416])
def mn1610 : Nat := Nat.xor mn833 (memoNat [1190325790775967975,14680064,426752648151040,8796093284352])
def mn1611 : Nat := mn833 - (memoNat [1099546230784,2305774839425728512,18442240474220593024,8191])
def mw2 : WireKey := (mn6,mn7,mn8,mn9,3)
def mw3 : WireKey := (mn10,mn11,mn12,mn13,3)
def mw4 : WireKey := (mn14,mn15,mn16,mn17,3)
def mw5 : WireKey := (mn18,mn19,mn20,mn21,3)
def mw6 : WireKey := (mn22,mn23,mn24,mn25,3)
def mw7 : WireKey := (mn26,mn27,mn28,mn29,3)
def memoOp (d : Bool) (x y : WireKey) : WireKey :=
  let (s,a,b,c,r) := x
  let (ss,aa,bb,cc,rr) := y
  let w := opW d ⟨s,a,b,c,r⟩ ⟨ss,aa,bb,cc,rr⟩
  (w.s,w.a,w.b,w.c,w.r)
def memoNot (x : WireKey) : WireKey :=
  let (s,a,b,c,r) := x
  (s ^^^ mz 0,b,a,c,0)
def mw230 : WireKey := memoNot mw2
def mw219 : WireKey := memoNot mw3
def mw208 : WireKey := memoNot mw4
def mw197 : WireKey := memoNot mw5
def mw252 : WireKey := memoNot mw6
def mw241 : WireKey := memoNot mw7
def mw24 : WireKey := memoOp false mw2 mw3
def mw25 : WireKey := memoOp true mw2 mw3
def mw26 : WireKey := memoOp false mw2 mw4
def mw27 : WireKey := memoOp true mw2 mw4
def mw28 : WireKey := memoOp false mw2 mw5
def mw29 : WireKey := memoOp true mw2 mw5
def mw8 : WireKey := memoOp false mw2 mw6
def mw9 : WireKey := memoOp true mw2 mw6
def mw16 : WireKey := memoOp false mw2 mw7
def mw17 : WireKey := memoOp true mw2 mw7
def mw30 : WireKey := memoOp false mw3 mw4
def mw31 : WireKey := memoOp true mw3 mw4
def mw32 : WireKey := memoOp false mw3 mw5
def mw33 : WireKey := memoOp true mw3 mw5
def mw10 : WireKey := memoOp false mw3 mw6
def mw11 : WireKey := memoOp true mw3 mw6
def mw18 : WireKey := memoOp false mw3 mw7
def mw19 : WireKey := memoOp true mw3 mw7
def mw34 : WireKey := memoOp false mw4 mw5
def mw35 : WireKey := memoOp true mw4 mw5
def mw12 : WireKey := memoOp false mw4 mw6
def mw13 : WireKey := memoOp true mw4 mw6
def mw20 : WireKey := memoOp false mw4 mw7
def mw21 : WireKey := memoOp true mw4 mw7
def mw14 : WireKey := memoOp false mw5 mw6
def mw15 : WireKey := memoOp true mw5 mw6
def mw22 : WireKey := memoOp false mw5 mw7
def mw23 : WireKey := memoOp true mw5 mw7
def mw1 : WireKey := memoOp false mw6 mw7
def mw0 : WireKey := memoOp true mw6 mw7
def mw110 : WireKey := memoOp false mw0 mw11
def mw47 : WireKey := memoOp true mw0 mw11
def mw122 : WireKey := memoOp false mw0 mw13
def mw49 : WireKey := memoOp true mw0 mw13
def mw132 : WireKey := memoOp false mw0 mw15
def mw51 : WireKey := memoOp true mw0 mw15
def mw52 : WireKey := memoOp false mw0 mw17
def mw45 : WireKey := memoOp true mw0 mw17
def mw66 : WireKey := memoOp false mw0 mw19
def mw44 : WireKey := memoOp false mw0 mw2
def mw78 : WireKey := memoOp false mw0 mw21
def mw88 : WireKey := memoOp false mw0 mw23
def mw46 : WireKey := memoOp false mw0 mw3
def mw48 : WireKey := memoOp false mw0 mw4
def mw50 : WireKey := memoOp false mw0 mw5
def mw96 : WireKey := memoOp false mw0 mw9
def mw38 : WireKey := memoOp false mw1 mw10
def mw116 : WireKey := memoOp true mw1 mw10
def mw40 : WireKey := memoOp false mw1 mw12
def mw127 : WireKey := memoOp true mw1 mw12
def mw42 : WireKey := memoOp false mw1 mw14
def mw136 : WireKey := memoOp true mw1 mw14
def mw36 : WireKey := memoOp false mw1 mw16
def mw59 : WireKey := memoOp true mw1 mw16
def mw72 : WireKey := memoOp true mw1 mw18
def mw37 : WireKey := memoOp true mw1 mw2
def mw83 : WireKey := memoOp true mw1 mw20
def mw92 : WireKey := memoOp true mw1 mw22
def mw39 : WireKey := memoOp true mw1 mw3
def mw41 : WireKey := memoOp true mw1 mw4
def mw43 : WireKey := memoOp true mw1 mw5
def mw103 : WireKey := memoOp true mw1 mw8
def mw68 : WireKey := memoOp false mw10 mw12
def mw175 : WireKey := memoOp true mw10 mw12
def mw70 : WireKey := memoOp false mw10 mw14
def mw184 : WireKey := memoOp true mw10 mw14
def mw53 : WireKey := memoOp false mw10 mw2
def mw67 : WireKey := memoOp true mw10 mw2
def mw60 : WireKey := memoOp true mw10 mw24
def mw85 : WireKey := memoOp true mw10 mw30
def mw94 : WireKey := memoOp true mw10 mw32
def mw69 : WireKey := memoOp true mw10 mw4
def mw71 : WireKey := memoOp true mw10 mw5
def mw146 : WireKey := memoOp true mw10 mw8
def mw170 : WireKey := memoOp false mw11 mw13
def mw75 : WireKey := memoOp true mw11 mw13
def mw180 : WireKey := memoOp false mw11 mw15
def mw77 : WireKey := memoOp true mw11 mw15
def mw73 : WireKey := memoOp false mw11 mw2
def mw61 : WireKey := memoOp true mw11 mw2
def mw54 : WireKey := memoOp false mw11 mw25
def mw80 : WireKey := memoOp false mw11 mw31
def mw90 : WireKey := memoOp false mw11 mw33
def mw74 : WireKey := memoOp false mw11 mw4
def mw76 : WireKey := memoOp false mw11 mw5
def mw140 : WireKey := memoOp false mw11 mw9
def mw81 : WireKey := memoOp false mw12 mw14
def mw192 : WireKey := memoOp true mw12 mw14
def mw55 : WireKey := memoOp false mw12 mw2
def mw79 : WireKey := memoOp true mw12 mw2
def mw62 : WireKey := memoOp true mw12 mw26
def mw95 : WireKey := memoOp true mw12 mw34
def mw82 : WireKey := memoOp true mw12 mw5
def mw157 : WireKey := memoOp true mw12 mw8
def mw188 : WireKey := memoOp false mw13 mw15
def mw87 : WireKey := memoOp true mw13 mw15
def mw84 : WireKey := memoOp false mw13 mw2
def mw63 : WireKey := memoOp true mw13 mw2
def mw56 : WireKey := memoOp false mw13 mw27
def mw91 : WireKey := memoOp false mw13 mw35
def mw86 : WireKey := memoOp false mw13 mw5
def mw152 : WireKey := memoOp false mw13 mw9
def mw57 : WireKey := memoOp false mw14 mw2
def mw89 : WireKey := memoOp true mw14 mw2
def mw64 : WireKey := memoOp true mw14 mw28
def mw166 : WireKey := memoOp true mw14 mw8
def mw93 : WireKey := memoOp false mw15 mw2
def mw65 : WireKey := memoOp true mw15 mw2
def mw58 : WireKey := memoOp false mw15 mw29
def mw162 : WireKey := memoOp false mw15 mw9
def mw97 : WireKey := memoOp false mw16 mw18
def mw147 : WireKey := memoOp true mw16 mw18
def mw99 : WireKey := memoOp false mw16 mw20
def mw158 : WireKey := memoOp true mw16 mw20
def mw101 : WireKey := memoOp false mw16 mw22
def mw167 : WireKey := memoOp true mw16 mw22
def mw117 : WireKey := memoOp true mw16 mw24
def mw128 : WireKey := memoOp true mw16 mw26
def mw137 : WireKey := memoOp true mw16 mw28
def mw98 : WireKey := memoOp true mw16 mw3
def mw100 : WireKey := memoOp true mw16 mw4
def mw102 : WireKey := memoOp true mw16 mw5
def mw141 : WireKey := memoOp false mw17 mw19
def mw105 : WireKey := memoOp true mw17 mw19
def mw153 : WireKey := memoOp false mw17 mw21
def mw107 : WireKey := memoOp true mw17 mw21
def mw163 : WireKey := memoOp false mw17 mw23
def mw109 : WireKey := memoOp true mw17 mw23
def mw111 : WireKey := memoOp false mw17 mw25
def mw123 : WireKey := memoOp false mw17 mw27
def mw133 : WireKey := memoOp false mw17 mw29
def mw104 : WireKey := memoOp false mw17 mw3
def mw106 : WireKey := memoOp false mw17 mw4
def mw108 : WireKey := memoOp false mw17 mw5
def mw112 : WireKey := memoOp false mw18 mw20
def mw176 : WireKey := memoOp true mw18 mw20
def mw114 : WireKey := memoOp false mw18 mw22
def mw185 : WireKey := memoOp true mw18 mw22
def mw129 : WireKey := memoOp true mw18 mw30
def mw138 : WireKey := memoOp true mw18 mw32
def mw113 : WireKey := memoOp true mw18 mw4
def mw115 : WireKey := memoOp true mw18 mw5
def mw171 : WireKey := memoOp false mw19 mw21
def mw119 : WireKey := memoOp true mw19 mw21
def mw181 : WireKey := memoOp false mw19 mw23
def mw121 : WireKey := memoOp true mw19 mw23
def mw124 : WireKey := memoOp false mw19 mw31
def mw134 : WireKey := memoOp false mw19 mw33
def mw118 : WireKey := memoOp false mw19 mw4
def mw120 : WireKey := memoOp false mw19 mw5
def mw201 : WireKey := memoOp false mw197 mw2
def mw202 : WireKey := memoOp true mw197 mw2
def mw203 : WireKey := memoOp false mw197 mw3
def mw204 : WireKey := memoOp true mw197 mw3
def mw205 : WireKey := memoOp false mw197 mw4
def mw206 : WireKey := memoOp true mw197 mw4
def mw196 : WireKey := memoOp false mw197 mw6
def mw198 : WireKey := memoOp true mw197 mw6
def mw199 : WireKey := memoOp false mw197 mw7
def mw200 : WireKey := memoOp true mw197 mw7
def mw212 : WireKey := memoOp false mw2 mw208
def mw213 : WireKey := memoOp true mw2 mw208
def mw223 : WireKey := memoOp false mw2 mw219
def mw224 : WireKey := memoOp true mw2 mw219
def mw243 : WireKey := memoOp false mw2 mw241
def mw244 : WireKey := memoOp true mw2 mw241
def mw254 : WireKey := memoOp false mw2 mw252
def mw255 : WireKey := memoOp true mw2 mw252
def mw142 : WireKey := memoOp false mw2 mw30
def mw172 : WireKey := memoOp true mw2 mw30
def mw177 : WireKey := memoOp false mw2 mw31
def mw149 : WireKey := memoOp true mw2 mw31
def mw144 : WireKey := memoOp false mw2 mw32
def mw182 : WireKey := memoOp true mw2 mw32
def mw186 : WireKey := memoOp false mw2 mw33
def mw151 : WireKey := memoOp true mw2 mw33
def mw155 : WireKey := memoOp false mw2 mw34
def mw190 : WireKey := memoOp true mw2 mw34
def mw194 : WireKey := memoOp false mw2 mw35
def mw161 : WireKey := memoOp true mw2 mw35
def mw125 : WireKey := memoOp false mw20 mw22
def mw193 : WireKey := memoOp true mw20 mw22
def mw139 : WireKey := memoOp true mw20 mw34
def mw126 : WireKey := memoOp true mw20 mw5
def mw214 : WireKey := memoOp false mw208 mw3
def mw215 : WireKey := memoOp true mw208 mw3
def mw216 : WireKey := memoOp false mw208 mw5
def mw217 : WireKey := memoOp true mw208 mw5
def mw207 : WireKey := memoOp false mw208 mw6
def mw209 : WireKey := memoOp true mw208 mw6
def mw210 : WireKey := memoOp false mw208 mw7
def mw211 : WireKey := memoOp true mw208 mw7
def mw189 : WireKey := memoOp false mw21 mw23
def mw131 : WireKey := memoOp true mw21 mw23
def mw135 : WireKey := memoOp false mw21 mw35
def mw130 : WireKey := memoOp false mw21 mw5
def mw225 : WireKey := memoOp false mw219 mw4
def mw226 : WireKey := memoOp true mw219 mw4
def mw227 : WireKey := memoOp false mw219 mw5
def mw228 : WireKey := memoOp true mw219 mw5
def mw218 : WireKey := memoOp false mw219 mw6
def mw220 : WireKey := memoOp true mw219 mw6
def mw221 : WireKey := memoOp false mw219 mw7
def mw222 : WireKey := memoOp true mw219 mw7
def mw234 : WireKey := memoOp false mw230 mw3
def mw235 : WireKey := memoOp true mw230 mw3
def mw236 : WireKey := memoOp false mw230 mw4
def mw237 : WireKey := memoOp true mw230 mw4
def mw238 : WireKey := memoOp false mw230 mw5
def mw239 : WireKey := memoOp true mw230 mw5
def mw229 : WireKey := memoOp false mw230 mw6
def mw231 : WireKey := memoOp true mw230 mw6
def mw232 : WireKey := memoOp false mw230 mw7
def mw233 : WireKey := memoOp true mw230 mw7
def mw159 : WireKey := memoOp true mw24 mw30
def mw168 : WireKey := memoOp true mw24 mw32
def mw143 : WireKey := memoOp true mw24 mw4
def mw145 : WireKey := memoOp true mw24 mw5
def mw245 : WireKey := memoOp false mw241 mw3
def mw246 : WireKey := memoOp true mw241 mw3
def mw247 : WireKey := memoOp false mw241 mw4
def mw248 : WireKey := memoOp true mw241 mw4
def mw249 : WireKey := memoOp false mw241 mw5
def mw250 : WireKey := memoOp true mw241 mw5
def mw240 : WireKey := memoOp false mw241 mw6
def mw242 : WireKey := memoOp true mw241 mw6
def mw154 : WireKey := memoOp false mw25 mw31
def mw164 : WireKey := memoOp false mw25 mw33
def mw148 : WireKey := memoOp false mw25 mw4
def mw150 : WireKey := memoOp false mw25 mw5
def mw256 : WireKey := memoOp false mw252 mw3
def mw257 : WireKey := memoOp true mw252 mw3
def mw258 : WireKey := memoOp false mw252 mw4
def mw259 : WireKey := memoOp true mw252 mw4
def mw260 : WireKey := memoOp false mw252 mw5
def mw261 : WireKey := memoOp true mw252 mw5
def mw251 : WireKey := memoOp false mw252 mw7
def mw253 : WireKey := memoOp true mw252 mw7
def mw169 : WireKey := memoOp true mw26 mw34
def mw156 : WireKey := memoOp true mw26 mw5
def mw165 : WireKey := memoOp false mw27 mw35
def mw160 : WireKey := memoOp false mw27 mw5
def mw173 : WireKey := memoOp false mw3 mw34
def mw191 : WireKey := memoOp true mw3 mw34
def mw195 : WireKey := memoOp false mw3 mw35
def mw179 : WireKey := memoOp true mw3 mw35
def mw187 : WireKey := memoOp true mw30 mw34
def mw174 : WireKey := memoOp true mw30 mw5
def mw183 : WireKey := memoOp false mw31 mw35
def mw178 : WireKey := memoOp false mw31 mw5
def originalC : Nat → Runner := lookC I.NN I.AA I.HX I.HY (lz 0) (mz 0) (pL (rt.map (fun _ => 16)))
def originalS : Nat → Runner := look1C I.NN I.AA I.HX I.HY (lz 0) (mz 0) (pL (rt.map (fun _ => 16))) 12
def mcC0 : List MemoKey := [(12,10,1,mn513,[mw6,mw7,mw2,mw36,mw3,mw4,mw5]),(12,10,1,mn514,[mw6,mw7,mw1,mw2,mw36,mw3,mw4,mw5]),(12,10,1,mn515,[mw6,mw37,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn516,[mw6,mw37,mw7,mw1,mw2,mw3,mw4,mw5]),(12,10,1,mn517,[mw6,mw7,mw2,mw3,mw38,mw4,mw5]),(12,10,1,mn518,[mw6,mw7,mw1,mw2,mw3,mw38,mw4,mw5]),(12,10,1,mn519,[mw6,mw39,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn520,[mw6,mw39,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC0p : mcC0.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC1 : List MemoKey := [(12,10,1,mn521,[mw6,mw7,mw2,mw3,mw4,mw40,mw5]),(12,10,1,mn522,[mw6,mw7,mw1,mw2,mw3,mw4,mw40,mw5]),(12,10,1,mn523,[mw6,mw41,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn524,[mw6,mw41,mw7,mw1,mw2,mw3,mw4,mw5]),(12,10,1,mn525,[mw6,mw7,mw2,mw3,mw4,mw5,mw42]),(12,10,1,mn526,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw42]),(12,10,1,mn527,[mw6,mw43,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn528,[mw6,mw43,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC1p : mcC1.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC2 : List MemoKey := [(12,10,1,mn559,[mw6,mw7,mw2,mw44,mw3,mw4,mw5]),(12,10,1,mn560,[mw0,mw6,mw7,mw2,mw44,mw3,mw4,mw5]),(12,10,1,mn561,[mw45,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn562,[mw45,mw0,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn563,[mw6,mw7,mw2,mw46,mw4,mw5]),(12,10,1,mn564,[mw0,mw6,mw7,mw2,mw46,mw4,mw5]),(12,10,1,mn565,[mw6,mw7,mw2,mw3,mw46,mw4,mw5]),(12,10,1,mn566,[mw0,mw6,mw7,mw2,mw3,mw46,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC2p : mcC2.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC3 : List MemoKey := [(12,10,1,mn567,[mw47,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn568,[mw47,mw0,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn569,[mw6,mw7,mw2,mw3,mw4,mw48,mw5]),(12,10,1,mn570,[mw0,mw6,mw7,mw2,mw3,mw4,mw48,mw5]),(12,10,1,mn571,[mw49,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn572,[mw49,mw0,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn573,[mw6,mw7,mw2,mw3,mw4,mw5,mw50]),(12,10,1,mn574,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw50])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC3p : mcC3.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC4 : List MemoKey := [(12,10,1,mn575,[mw51,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn576,[mw51,mw0,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn607,[mw6,mw7,mw2,mw36,mw3,mw4,mw5]),(12,10,1,mn608,[mw6,mw7,mw2,mw8,mw36,mw3,mw4,mw5]),(12,10,1,mn609,[mw6,mw52,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn610,[mw6,mw52,mw7,mw2,mw8,mw3,mw4,mw5]),(12,10,1,mn611,[mw6,mw7,mw2,mw3,mw4,mw53,mw5]),(12,10,1,mn612,[mw6,mw7,mw2,mw8,mw3,mw4,mw53,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC4p : mcC4.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC5 : List MemoKey := [(12,10,1,mn613,[mw6,mw7,mw54,mw2,mw3,mw4,mw5]),(12,10,1,mn614,[mw6,mw7,mw54,mw2,mw8,mw3,mw4,mw5]),(12,10,1,mn615,[mw6,mw7,mw2,mw3,mw4,mw5,mw55]),(12,10,1,mn616,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw55]),(12,10,1,mn617,[mw6,mw7,mw56,mw2,mw3,mw4,mw5]),(12,10,1,mn618,[mw6,mw7,mw56,mw2,mw8,mw3,mw4,mw5]),(12,10,1,mn619,[mw6,mw7,mw2,mw3,mw4,mw5,mw57]),(12,10,1,mn620,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw57])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC5p : mcC5.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC6 : List MemoKey := [(12,10,1,mn621,[mw6,mw7,mw58,mw2,mw3,mw4,mw5]),(12,10,1,mn622,[mw6,mw7,mw58,mw2,mw8,mw3,mw4,mw5]),(12,10,1,mn649,[mw6,mw7,mw59,mw2,mw3,mw4,mw5]),(12,10,1,mn650,[mw9,mw6,mw7,mw59,mw2,mw3,mw4,mw5]),(12,10,1,mn651,[mw45,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn652,[mw45,mw9,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn653,[mw6,mw7,mw2,mw3,mw60,mw4,mw5]),(12,10,1,mn654,[mw9,mw6,mw7,mw2,mw3,mw60,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC6p : mcC6.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC7 : List MemoKey := [(12,10,1,mn655,[mw61,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn656,[mw61,mw9,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn657,[mw6,mw7,mw2,mw3,mw4,mw62,mw5]),(12,10,1,mn658,[mw9,mw6,mw7,mw2,mw3,mw4,mw62,mw5]),(12,10,1,mn659,[mw63,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn660,[mw63,mw9,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn661,[mw6,mw7,mw2,mw3,mw4,mw5,mw64]),(12,10,1,mn662,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw64])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC7p : mcC7.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC8 : List MemoKey := [(12,10,1,mn663,[mw65,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn664,[mw65,mw9,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn694,[mw6,mw7,mw2,mw3,mw38,mw4,mw5]),(12,10,1,mn695,[mw6,mw7,mw2,mw3,mw10,mw38,mw4,mw5]),(12,10,1,mn696,[mw6,mw66,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn697,[mw6,mw66,mw7,mw2,mw3,mw10,mw4,mw5]),(12,10,1,mn698,[mw6,mw7,mw2,mw3,mw4,mw53,mw5]),(12,10,1,mn699,[mw6,mw7,mw2,mw3,mw10,mw4,mw53,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC8p : mcC8.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC9 : List MemoKey := [(12,10,1,mn700,[mw6,mw7,mw67,mw2,mw3,mw4,mw5]),(12,10,1,mn701,[mw6,mw7,mw67,mw2,mw3,mw10,mw4,mw5]),(12,10,1,mn702,[mw6,mw7,mw2,mw3,mw4,mw5,mw68]),(12,10,1,mn703,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw68]),(12,10,1,mn704,[mw6,mw7,mw2,mw69,mw3,mw4,mw5]),(12,10,1,mn705,[mw6,mw7,mw2,mw69,mw3,mw10,mw4,mw5]),(12,10,1,mn706,[mw6,mw7,mw2,mw3,mw4,mw5,mw70]),(12,10,1,mn707,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw70])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC9p : mcC9.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC10 : List MemoKey := [(12,10,1,mn708,[mw6,mw7,mw2,mw71,mw3,mw4,mw5]),(12,10,1,mn709,[mw6,mw7,mw2,mw71,mw3,mw10,mw4,mw5]),(12,10,1,mn734,[mw6,mw7,mw72,mw2,mw3,mw4,mw5]),(12,10,1,mn735,[mw11,mw6,mw7,mw72,mw2,mw3,mw4,mw5]),(12,10,1,mn736,[mw47,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn737,[mw47,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn738,[mw6,mw7,mw2,mw73,mw3,mw4,mw5]),(12,10,1,mn739,[mw11,mw6,mw7,mw2,mw73,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC10p : mcC10.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC11 : List MemoKey := [(12,10,1,mn740,[mw61,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn741,[mw61,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn742,[mw6,mw7,mw2,mw3,mw4,mw74,mw5]),(12,10,1,mn743,[mw11,mw6,mw7,mw2,mw3,mw4,mw74,mw5]),(12,10,1,mn744,[mw75,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn745,[mw75,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn746,[mw6,mw7,mw2,mw3,mw4,mw5,mw76]),(12,10,1,mn747,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw76])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC11p : mcC11.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC12 : List MemoKey := [(12,10,1,mn748,[mw77,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn749,[mw77,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn777,[mw6,mw7,mw2,mw3,mw4,mw40,mw5]),(12,10,1,mn778,[mw6,mw7,mw2,mw3,mw4,mw12,mw40,mw5]),(12,10,1,mn779,[mw6,mw78,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn780,[mw6,mw78,mw7,mw2,mw3,mw4,mw12,mw5]),(12,10,1,mn781,[mw6,mw7,mw2,mw3,mw4,mw5,mw55]),(12,10,1,mn782,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw55])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC12p : mcC12.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC13 : List MemoKey := [(12,10,1,mn783,[mw6,mw7,mw79,mw2,mw3,mw4,mw5]),(12,10,1,mn784,[mw6,mw7,mw79,mw2,mw3,mw4,mw12,mw5]),(12,10,1,mn785,[mw6,mw7,mw2,mw3,mw4,mw5,mw68]),(12,10,1,mn786,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw68]),(12,10,1,mn787,[mw6,mw7,mw2,mw80,mw3,mw4,mw5]),(12,10,1,mn788,[mw6,mw7,mw2,mw80,mw3,mw4,mw12,mw5]),(12,10,1,mn789,[mw6,mw7,mw2,mw3,mw4,mw5,mw81]),(12,10,1,mn790,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw81])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC13p : mcC13.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC14 : List MemoKey := [(12,10,1,mn791,[mw6,mw7,mw2,mw3,mw82,mw4,mw5]),(12,10,1,mn792,[mw6,mw7,mw2,mw3,mw82,mw4,mw12,mw5]),(12,10,1,mn816,[mw6,mw7,mw83,mw2,mw3,mw4,mw5]),(12,10,1,mn817,[mw13,mw6,mw7,mw83,mw2,mw3,mw4,mw5]),(12,10,1,mn818,[mw49,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn819,[mw49,mw13,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn820,[mw6,mw7,mw2,mw84,mw3,mw4,mw5]),(12,10,1,mn821,[mw13,mw6,mw7,mw2,mw84,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC14p : mcC14.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC15 : List MemoKey := [(12,10,1,mn822,[mw63,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn823,[mw63,mw13,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn824,[mw6,mw7,mw2,mw3,mw85,mw4,mw5]),(12,10,1,mn825,[mw13,mw6,mw7,mw2,mw3,mw85,mw4,mw5]),(12,10,1,mn826,[mw75,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn827,[mw75,mw13,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn828,[mw6,mw7,mw2,mw3,mw4,mw5,mw86]),(12,10,1,mn829,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw86])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC15p : mcC15.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC16 : List MemoKey := [(12,10,1,mn830,[mw87,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn831,[mw87,mw13,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn856,[mw6,mw7,mw2,mw3,mw4,mw5,mw42]),(12,10,1,mn857,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw42]),(12,10,1,mn858,[mw6,mw88,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn859,[mw6,mw88,mw7,mw2,mw3,mw4,mw5,mw14]),(12,10,1,mn860,[mw6,mw7,mw2,mw3,mw4,mw5,mw57]),(12,10,1,mn861,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw57])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC16p : mcC16.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC17 : List MemoKey := [(12,10,1,mn862,[mw6,mw7,mw89,mw2,mw3,mw4,mw5]),(12,10,1,mn863,[mw6,mw7,mw89,mw2,mw3,mw4,mw5,mw14]),(12,10,1,mn864,[mw6,mw7,mw2,mw3,mw4,mw5,mw70]),(12,10,1,mn865,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw70]),(12,10,1,mn866,[mw6,mw7,mw2,mw90,mw3,mw4,mw5]),(12,10,1,mn867,[mw6,mw7,mw2,mw90,mw3,mw4,mw5,mw14]),(12,10,1,mn868,[mw6,mw7,mw2,mw3,mw4,mw5,mw81]),(12,10,1,mn869,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw81])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC17p : mcC17.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC18 : List MemoKey := [(12,10,1,mn870,[mw6,mw7,mw2,mw3,mw91,mw5]),(12,10,1,mn871,[mw6,mw7,mw2,mw3,mw91,mw5,mw14]),(12,10,1,mn872,[mw6,mw7,mw2,mw3,mw91,mw4,mw5]),(12,10,1,mn873,[mw6,mw7,mw2,mw3,mw91,mw4,mw5,mw14]),(12,10,1,mn894,[mw6,mw7,mw92,mw2,mw3,mw4,mw5]),(12,10,1,mn895,[mw15,mw6,mw7,mw92,mw2,mw3,mw4,mw5]),(12,10,1,mn896,[mw51,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn897,[mw51,mw15,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC18p : mcC18.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC19 : List MemoKey := [(12,10,1,mn898,[mw6,mw7,mw2,mw93,mw3,mw4,mw5]),(12,10,1,mn899,[mw15,mw6,mw7,mw2,mw93,mw3,mw4,mw5]),(12,10,1,mn900,[mw65,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn901,[mw65,mw15,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn902,[mw6,mw7,mw2,mw3,mw94,mw4,mw5]),(12,10,1,mn903,[mw15,mw6,mw7,mw2,mw3,mw94,mw4,mw5]),(12,10,1,mn904,[mw77,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn905,[mw77,mw15,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC19p : mcC19.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC20 : List MemoKey := [(12,10,1,mn906,[mw6,mw7,mw2,mw3,mw4,mw95,mw5]),(12,10,1,mn907,[mw15,mw6,mw7,mw2,mw3,mw4,mw95,mw5]),(12,10,1,mn908,[mw87,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn909,[mw87,mw15,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn932,[mw6,mw7,mw2,mw36,mw3,mw4,mw5]),(12,10,1,mn933,[mw6,mw7,mw2,mw16,mw36,mw3,mw4,mw5]),(12,10,1,mn934,[mw96,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn935,[mw96,mw6,mw7,mw2,mw16,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC20p : mcC20.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC21 : List MemoKey := [(12,10,1,mn936,[mw6,mw7,mw2,mw3,mw4,mw5,mw97]),(12,10,1,mn937,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw97]),(12,10,1,mn938,[mw6,mw7,mw98,mw2,mw3,mw4,mw5]),(12,10,1,mn939,[mw6,mw7,mw98,mw2,mw16,mw3,mw4,mw5]),(12,10,1,mn940,[mw6,mw7,mw2,mw3,mw4,mw5,mw99]),(12,10,1,mn941,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw99]),(12,10,1,mn942,[mw6,mw7,mw100,mw2,mw3,mw4,mw5]),(12,10,1,mn943,[mw6,mw7,mw100,mw2,mw16,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC21p : mcC21.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC22 : List MemoKey := [(12,10,1,mn944,[mw6,mw7,mw2,mw3,mw4,mw5,mw101]),(12,10,1,mn945,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw101]),(12,10,1,mn946,[mw6,mw7,mw2,mw102,mw3,mw4,mw5]),(12,10,1,mn947,[mw6,mw7,mw2,mw102,mw16,mw3,mw4,mw5]),(12,10,1,mn966,[mw6,mw103,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn967,[mw6,mw17,mw103,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn968,[mw45,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn969,[mw45,mw6,mw17,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC22p : mcC22.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC23 : List MemoKey := [(12,10,1,mn970,[mw6,mw7,mw2,mw3,mw104,mw4,mw5]),(12,10,1,mn971,[mw6,mw17,mw7,mw2,mw3,mw104,mw4,mw5]),(12,10,1,mn972,[mw6,mw105,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn973,[mw6,mw105,mw17,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn974,[mw6,mw7,mw2,mw3,mw4,mw106,mw5]),(12,10,1,mn975,[mw6,mw17,mw7,mw2,mw3,mw4,mw106,mw5]),(12,10,1,mn976,[mw6,mw107,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn977,[mw6,mw107,mw17,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC23p : mcC23.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC24 : List MemoKey := [(12,10,1,mn978,[mw6,mw7,mw2,mw3,mw4,mw5,mw108]),(12,10,1,mn979,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw108]),(12,10,1,mn980,[mw6,mw109,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn981,[mw6,mw109,mw17,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1003,[mw6,mw7,mw2,mw3,mw38,mw4,mw5]),(12,10,1,mn1004,[mw6,mw7,mw2,mw3,mw18,mw38,mw4,mw5]),(12,10,1,mn1005,[mw110,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1006,[mw110,mw7,mw2,mw3,mw18,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC24p : mcC24.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC25 : List MemoKey := [(12,10,1,mn1007,[mw110,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1008,[mw110,mw6,mw7,mw2,mw3,mw18,mw4,mw5]),(12,10,1,mn1009,[mw6,mw7,mw2,mw3,mw4,mw5,mw97]),(12,10,1,mn1010,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw97]),(12,10,1,mn1011,[mw6,mw7,mw111,mw2,mw3,mw4,mw5]),(12,10,1,mn1012,[mw6,mw7,mw111,mw2,mw3,mw18,mw4,mw5]),(12,10,1,mn1013,[mw6,mw7,mw2,mw3,mw4,mw5,mw112]),(12,10,1,mn1014,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw112])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC25p : mcC25.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC26 : List MemoKey := [(12,10,1,mn1015,[mw6,mw7,mw2,mw113,mw3,mw4,mw5]),(12,10,1,mn1016,[mw6,mw7,mw2,mw113,mw3,mw18,mw4,mw5]),(12,10,1,mn1017,[mw6,mw7,mw2,mw3,mw4,mw5,mw114]),(12,10,1,mn1018,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw114]),(12,10,1,mn1019,[mw6,mw7,mw2,mw3,mw115,mw4,mw5]),(12,10,1,mn1020,[mw6,mw7,mw2,mw3,mw115,mw18,mw4,mw5]),(12,10,1,mn1037,[mw6,mw116,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1038,[mw6,mw19,mw116,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC26p : mcC26.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC27 : List MemoKey := [(12,10,1,mn1039,[mw47,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1040,[mw47,mw6,mw19,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1041,[mw6,mw7,mw2,mw117,mw3,mw4,mw5]),(12,10,1,mn1042,[mw6,mw19,mw7,mw2,mw117,mw3,mw4,mw5]),(12,10,1,mn1043,[mw6,mw105,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1044,[mw6,mw105,mw19,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1045,[mw6,mw7,mw2,mw3,mw4,mw118,mw5]),(12,10,1,mn1046,[mw6,mw19,mw7,mw2,mw3,mw4,mw118,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC27p : mcC27.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC28 : List MemoKey := [(12,10,1,mn1047,[mw6,mw119,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1048,[mw6,mw119,mw19,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1049,[mw6,mw7,mw2,mw3,mw4,mw5,mw120]),(12,10,1,mn1050,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw120]),(12,10,1,mn1051,[mw6,mw121,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1052,[mw6,mw121,mw19,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1071,[mw6,mw7,mw2,mw3,mw4,mw40,mw5]),(12,10,1,mn1072,[mw6,mw7,mw2,mw3,mw4,mw20,mw40,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC28p : mcC28.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC29 : List MemoKey := [(12,10,1,mn1073,[mw122,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1074,[mw122,mw6,mw7,mw2,mw3,mw4,mw20,mw5]),(12,10,1,mn1075,[mw6,mw7,mw2,mw3,mw4,mw5,mw99]),(12,10,1,mn1076,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw99]),(12,10,1,mn1077,[mw6,mw7,mw123,mw2,mw3,mw4,mw5]),(12,10,1,mn1078,[mw6,mw7,mw123,mw2,mw3,mw4,mw20,mw5]),(12,10,1,mn1079,[mw6,mw7,mw2,mw3,mw4,mw5,mw112]),(12,10,1,mn1080,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw112])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC29p : mcC29.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC30 : List MemoKey := [(12,10,1,mn1081,[mw6,mw7,mw2,mw124,mw3,mw4,mw5]),(12,10,1,mn1082,[mw6,mw7,mw2,mw124,mw3,mw4,mw20,mw5]),(12,10,1,mn1083,[mw6,mw7,mw2,mw3,mw4,mw5,mw125]),(12,10,1,mn1084,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw125]),(12,10,1,mn1085,[mw6,mw7,mw2,mw3,mw4,mw126,mw5]),(12,10,1,mn1086,[mw6,mw7,mw2,mw3,mw4,mw126,mw20,mw5]),(12,10,1,mn1101,[mw6,mw127,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1102,[mw6,mw21,mw127,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC30p : mcC30.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC31 : List MemoKey := [(12,10,1,mn1103,[mw49,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1104,[mw49,mw6,mw21,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1105,[mw6,mw7,mw2,mw128,mw3,mw4,mw5]),(12,10,1,mn1106,[mw6,mw21,mw7,mw2,mw128,mw3,mw4,mw5]),(12,10,1,mn1107,[mw6,mw107,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1108,[mw6,mw107,mw21,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1109,[mw6,mw7,mw2,mw3,mw129,mw4,mw5]),(12,10,1,mn1110,[mw6,mw21,mw7,mw2,mw3,mw129,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC31p : mcC31.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC32 : List MemoKey := [(12,10,1,mn1111,[mw6,mw119,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1112,[mw6,mw119,mw21,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1113,[mw6,mw7,mw2,mw3,mw4,mw5,mw130]),(12,10,1,mn1114,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw130]),(12,10,1,mn1115,[mw6,mw131,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1116,[mw6,mw131,mw21,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1133,[mw6,mw7,mw2,mw3,mw4,mw5,mw42]),(12,10,1,mn1134,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw42])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC32p : mcC32.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC33 : List MemoKey := [(12,10,1,mn1135,[mw132,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1136,[mw132,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(12,10,1,mn1137,[mw6,mw7,mw2,mw3,mw4,mw5,mw101]),(12,10,1,mn1138,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw101]),(12,10,1,mn1139,[mw6,mw7,mw133,mw2,mw3,mw4,mw5]),(12,10,1,mn1140,[mw6,mw7,mw133,mw2,mw3,mw4,mw5,mw22]),(12,10,1,mn1141,[mw6,mw7,mw2,mw3,mw4,mw5,mw114]),(12,10,1,mn1142,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw114])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC33p : mcC33.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC34 : List MemoKey := [(12,10,1,mn1143,[mw6,mw7,mw2,mw134,mw3,mw4,mw5]),(12,10,1,mn1144,[mw6,mw7,mw2,mw134,mw3,mw4,mw5,mw22]),(12,10,1,mn1145,[mw6,mw7,mw2,mw3,mw4,mw5,mw125]),(12,10,1,mn1146,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw125]),(12,10,1,mn1147,[mw6,mw7,mw2,mw3,mw135,mw4,mw5]),(12,10,1,mn1148,[mw6,mw7,mw2,mw3,mw135,mw4,mw5,mw22]),(12,10,1,mn1161,[mw6,mw136,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1162,[mw6,mw23,mw136,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC34p : mcC34.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC35 : List MemoKey := [(12,10,1,mn1163,[mw51,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1164,[mw51,mw6,mw23,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1165,[mw6,mw7,mw2,mw137,mw3,mw4,mw5]),(12,10,1,mn1166,[mw6,mw23,mw7,mw2,mw137,mw3,mw4,mw5]),(12,10,1,mn1167,[mw6,mw109,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1168,[mw6,mw109,mw23,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1169,[mw6,mw7,mw2,mw3,mw138,mw4,mw5]),(12,10,1,mn1170,[mw6,mw23,mw7,mw2,mw3,mw138,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC35p : mcC35.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC36 : List MemoKey := [(12,10,1,mn1171,[mw6,mw121,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1172,[mw6,mw121,mw23,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1173,[mw6,mw7,mw2,mw3,mw4,mw139,mw5]),(12,10,1,mn1174,[mw6,mw23,mw7,mw2,mw3,mw4,mw139,mw5]),(12,10,1,mn1175,[mw6,mw131,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1176,[mw6,mw131,mw23,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1191,[mw6,mw7,mw2,mw3,mw4,mw53,mw5]),(12,10,1,mn1192,[mw6,mw7,mw2,mw3,mw4,mw24,mw53,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC36p : mcC36.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC37 : List MemoKey := [(12,10,1,mn1193,[mw140,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1194,[mw140,mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(12,10,1,mn1195,[mw6,mw7,mw2,mw3,mw4,mw5,mw97]),(12,10,1,mn1196,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw97]),(12,10,1,mn1197,[mw6,mw141,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1198,[mw6,mw141,mw7,mw2,mw3,mw4,mw24,mw5]),(12,10,1,mn1199,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn1200,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw142])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC37p : mcC37.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC38 : List MemoKey := [(12,10,1,mn1201,[mw6,mw7,mw2,mw3,mw143,mw4,mw5]),(12,10,1,mn1202,[mw6,mw7,mw2,mw3,mw143,mw4,mw24,mw5]),(12,10,1,mn1203,[mw6,mw7,mw2,mw3,mw4,mw5,mw144]),(12,10,1,mn1204,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw144]),(12,10,1,mn1205,[mw6,mw7,mw2,mw3,mw4,mw145,mw5]),(12,10,1,mn1206,[mw6,mw7,mw2,mw3,mw4,mw145,mw24,mw5]),(12,10,1,mn1218,[mw6,mw7,mw146,mw2,mw3,mw4,mw5]),(12,10,1,mn1219,[mw6,mw7,mw25,mw146,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC38p : mcC38.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC39 : List MemoKey := [(12,10,1,mn1220,[mw61,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1221,[mw61,mw6,mw7,mw25,mw2,mw3,mw4,mw5]),(12,10,1,mn1222,[mw6,mw7,mw147,mw2,mw3,mw4,mw5]),(12,10,1,mn1223,[mw6,mw7,mw25,mw147,mw2,mw3,mw4,mw5]),(12,10,1,mn1224,[mw6,mw105,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1225,[mw6,mw105,mw7,mw25,mw2,mw3,mw4,mw5]),(12,10,1,mn1226,[mw6,mw7,mw2,mw3,mw5,mw148]),(12,10,1,mn1227,[mw6,mw7,mw25,mw2,mw3,mw5,mw148])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC39p : mcC39.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC40 : List MemoKey := [(12,10,1,mn1228,[mw6,mw7,mw2,mw3,mw4,mw5,mw148]),(12,10,1,mn1229,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw148]),(12,10,1,mn1230,[mw6,mw7,mw149,mw2,mw3,mw4,mw5]),(12,10,1,mn1231,[mw6,mw7,mw149,mw25,mw2,mw3,mw4,mw5]),(12,10,1,mn1232,[mw6,mw7,mw2,mw3,mw4,mw5,mw150]),(12,10,1,mn1233,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw150]),(12,10,1,mn1234,[mw6,mw7,mw151,mw2,mw3,mw4,mw5]),(12,10,1,mn1235,[mw6,mw7,mw151,mw25,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC40p : mcC40.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC41 : List MemoKey := [(12,10,1,mn1250,[mw6,mw7,mw2,mw3,mw4,mw5,mw55]),(12,10,1,mn1251,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw55]),(12,10,1,mn1252,[mw152,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1253,[mw152,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(12,10,1,mn1254,[mw6,mw7,mw2,mw3,mw4,mw5,mw99]),(12,10,1,mn1255,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw99]),(12,10,1,mn1256,[mw6,mw153,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1257,[mw6,mw153,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC41p : mcC41.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC42 : List MemoKey := [(12,10,1,mn1258,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn1259,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw142]),(12,10,1,mn1260,[mw6,mw7,mw2,mw154,mw4,mw5]),(12,10,1,mn1261,[mw6,mw7,mw2,mw154,mw4,mw5,mw26]),(12,10,1,mn1262,[mw6,mw7,mw2,mw154,mw3,mw4,mw5]),(12,10,1,mn1263,[mw6,mw7,mw2,mw154,mw3,mw4,mw5,mw26]),(12,10,1,mn1264,[mw6,mw7,mw2,mw3,mw4,mw5,mw155]),(12,10,1,mn1265,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw155])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC42p : mcC42.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC43 : List MemoKey := [(12,10,1,mn1266,[mw6,mw7,mw2,mw3,mw4,mw156,mw5]),(12,10,1,mn1267,[mw6,mw7,mw2,mw3,mw4,mw156,mw5,mw26]),(12,10,1,mn1276,[mw6,mw7,mw157,mw2,mw3,mw4,mw5]),(12,10,1,mn1277,[mw6,mw7,mw27,mw157,mw2,mw3,mw4,mw5]),(12,10,1,mn1278,[mw63,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1279,[mw63,mw6,mw7,mw27,mw2,mw3,mw4,mw5]),(12,10,1,mn1280,[mw6,mw7,mw158,mw2,mw3,mw4,mw5]),(12,10,1,mn1281,[mw6,mw7,mw27,mw158,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC43p : mcC43.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC44 : List MemoKey := [(12,10,1,mn1282,[mw6,mw107,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1283,[mw6,mw107,mw7,mw27,mw2,mw3,mw4,mw5]),(12,10,1,mn1284,[mw6,mw7,mw2,mw3,mw4,mw159,mw5]),(12,10,1,mn1285,[mw6,mw7,mw27,mw2,mw3,mw4,mw159,mw5]),(12,10,1,mn1286,[mw6,mw7,mw149,mw2,mw3,mw4,mw5]),(12,10,1,mn1287,[mw6,mw7,mw149,mw27,mw2,mw3,mw4,mw5]),(12,10,1,mn1288,[mw6,mw7,mw2,mw3,mw4,mw5,mw160]),(12,10,1,mn1289,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw160])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC44p : mcC44.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC45 : List MemoKey := [(12,10,1,mn1290,[mw6,mw7,mw161,mw2,mw3,mw4,mw5]),(12,10,1,mn1291,[mw6,mw7,mw161,mw27,mw2,mw3,mw4,mw5]),(12,10,1,mn1302,[mw6,mw7,mw2,mw3,mw4,mw5,mw57]),(12,10,1,mn1303,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw57]),(12,10,1,mn1304,[mw162,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1305,[mw162,mw6,mw7,mw2,mw3,mw4,mw5,mw28]),(12,10,1,mn1306,[mw6,mw7,mw2,mw3,mw4,mw5,mw101]),(12,10,1,mn1307,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC45p : mcC45.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC46 : List MemoKey := [(12,10,1,mn1308,[mw6,mw163,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1309,[mw6,mw163,mw7,mw2,mw3,mw4,mw5,mw28]),(12,10,1,mn1310,[mw6,mw7,mw2,mw3,mw4,mw5,mw144]),(12,10,1,mn1311,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw144]),(12,10,1,mn1312,[mw6,mw7,mw2,mw164,mw3,mw4,mw5]),(12,10,1,mn1313,[mw6,mw7,mw2,mw164,mw3,mw4,mw5,mw28]),(12,10,1,mn1314,[mw6,mw7,mw2,mw3,mw4,mw5,mw155]),(12,10,1,mn1315,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw155])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC46p : mcC46.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC47 : List MemoKey := [(12,10,1,mn1316,[mw6,mw7,mw2,mw3,mw165,mw4,mw5]),(12,10,1,mn1317,[mw6,mw7,mw2,mw3,mw165,mw4,mw5,mw28]),(12,10,1,mn1324,[mw6,mw7,mw166,mw2,mw3,mw4,mw5]),(12,10,1,mn1325,[mw6,mw7,mw29,mw166,mw2,mw3,mw4,mw5]),(12,10,1,mn1326,[mw65,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1327,[mw65,mw6,mw7,mw29,mw2,mw3,mw4,mw5]),(12,10,1,mn1328,[mw6,mw7,mw2,mw167,mw3,mw4,mw5]),(12,10,1,mn1329,[mw6,mw7,mw29,mw2,mw167,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC47p : mcC47.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC48 : List MemoKey := [(12,10,1,mn1330,[mw6,mw109,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1331,[mw6,mw109,mw7,mw29,mw2,mw3,mw4,mw5]),(12,10,1,mn1332,[mw6,mw7,mw2,mw3,mw4,mw168,mw5]),(12,10,1,mn1333,[mw6,mw7,mw29,mw2,mw3,mw4,mw168,mw5]),(12,10,1,mn1334,[mw6,mw7,mw151,mw2,mw3,mw4,mw5]),(12,10,1,mn1335,[mw6,mw7,mw151,mw29,mw2,mw3,mw4,mw5]),(12,10,1,mn1336,[mw6,mw7,mw2,mw3,mw4,mw5,mw169]),(12,10,1,mn1337,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw169])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC48p : mcC48.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC49 : List MemoKey := [(12,10,1,mn1338,[mw6,mw7,mw161,mw2,mw3,mw4,mw5]),(12,10,1,mn1339,[mw6,mw7,mw161,mw29,mw2,mw3,mw4,mw5]),(12,10,1,mn1348,[mw6,mw7,mw2,mw3,mw4,mw5,mw68]),(12,10,1,mn1349,[mw6,mw7,mw2,mw3,mw4,mw5,mw30,mw68]),(12,10,1,mn1350,[mw170,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1351,[mw170,mw6,mw7,mw2,mw3,mw4,mw5,mw30]),(12,10,1,mn1352,[mw6,mw7,mw2,mw3,mw4,mw5,mw112]),(12,10,1,mn1353,[mw6,mw7,mw2,mw3,mw4,mw5,mw30,mw112])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC49p : mcC49.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC50 : List MemoKey := [(12,10,1,mn1354,[mw6,mw171,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1355,[mw6,mw171,mw7,mw2,mw3,mw4,mw5,mw30]),(12,10,1,mn1356,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn1357,[mw6,mw7,mw2,mw3,mw4,mw5,mw30,mw142]),(12,10,1,mn1358,[mw6,mw7,mw172,mw2,mw3,mw4,mw5]),(12,10,1,mn1359,[mw6,mw7,mw172,mw2,mw3,mw4,mw5,mw30]),(12,10,1,mn1360,[mw6,mw7,mw2,mw3,mw4,mw5,mw173]),(12,10,1,mn1361,[mw6,mw7,mw2,mw3,mw4,mw5,mw30,mw173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC50p : mcC50.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC51 : List MemoKey := [(12,10,1,mn1362,[mw6,mw7,mw2,mw3,mw4,mw174,mw5]),(12,10,1,mn1363,[mw6,mw7,mw2,mw3,mw4,mw174,mw5,mw30]),(12,10,1,mn1368,[mw6,mw7,mw2,mw175,mw3,mw4,mw5]),(12,10,1,mn1369,[mw6,mw7,mw2,mw31,mw175,mw3,mw4,mw5]),(12,10,1,mn1370,[mw75,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1371,[mw75,mw6,mw7,mw2,mw31,mw3,mw4,mw5]),(12,10,1,mn1372,[mw6,mw7,mw2,mw176,mw3,mw4,mw5]),(12,10,1,mn1373,[mw6,mw7,mw2,mw31,mw176,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC51p : mcC51.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC52 : List MemoKey := [(12,10,1,mn1374,[mw6,mw119,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1375,[mw6,mw119,mw7,mw2,mw31,mw3,mw4,mw5]),(12,10,1,mn1376,[mw6,mw7,mw2,mw3,mw4,mw177,mw5]),(12,10,1,mn1377,[mw6,mw7,mw2,mw31,mw3,mw4,mw177,mw5]),(12,10,1,mn1378,[mw6,mw7,mw149,mw2,mw3,mw4,mw5]),(12,10,1,mn1379,[mw6,mw7,mw149,mw2,mw31,mw3,mw4,mw5]),(12,10,1,mn1380,[mw6,mw7,mw2,mw3,mw4,mw5,mw178]),(12,10,1,mn1381,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw178])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC52p : mcC52.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC53 : List MemoKey := [(12,10,1,mn1382,[mw6,mw7,mw2,mw179,mw3,mw4,mw5]),(12,10,1,mn1383,[mw6,mw7,mw2,mw179,mw31,mw3,mw4,mw5]),(12,10,1,mn1390,[mw6,mw7,mw2,mw3,mw4,mw5,mw70]),(12,10,1,mn1391,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw70]),(12,10,1,mn1392,[mw180,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1393,[mw180,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(12,10,1,mn1394,[mw6,mw7,mw2,mw3,mw4,mw5,mw114]),(12,10,1,mn1395,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw114])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC53p : mcC53.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC54 : List MemoKey := [(12,10,1,mn1396,[mw6,mw181,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1397,[mw6,mw181,mw7,mw2,mw3,mw4,mw5,mw32]),(12,10,1,mn1398,[mw6,mw7,mw2,mw3,mw4,mw5,mw144]),(12,10,1,mn1399,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw144]),(12,10,1,mn1400,[mw6,mw7,mw182,mw2,mw3,mw4,mw5]),(12,10,1,mn1401,[mw6,mw7,mw182,mw2,mw3,mw4,mw5,mw32]),(12,10,1,mn1402,[mw6,mw7,mw2,mw3,mw4,mw5,mw173]),(12,10,1,mn1403,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC54p : mcC54.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC55 : List MemoKey := [(12,10,1,mn1404,[mw6,mw7,mw2,mw3,mw183,mw4,mw5]),(12,10,1,mn1405,[mw6,mw7,mw2,mw3,mw183,mw4,mw5,mw32]),(12,10,1,mn1408,[mw6,mw7,mw2,mw184,mw3,mw4,mw5]),(12,10,1,mn1409,[mw6,mw7,mw2,mw33,mw184,mw3,mw4,mw5]),(12,10,1,mn1410,[mw77,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1411,[mw77,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn1412,[mw6,mw7,mw2,mw3,mw185,mw4,mw5]),(12,10,1,mn1413,[mw6,mw7,mw2,mw33,mw3,mw185,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC55p : mcC55.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC56 : List MemoKey := [(12,10,1,mn1414,[mw6,mw121,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1415,[mw6,mw121,mw7,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn1416,[mw6,mw7,mw2,mw3,mw4,mw186,mw5]),(12,10,1,mn1417,[mw6,mw7,mw2,mw33,mw3,mw4,mw186,mw5]),(12,10,1,mn1418,[mw6,mw7,mw151,mw2,mw3,mw4,mw5]),(12,10,1,mn1419,[mw6,mw7,mw151,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn1420,[mw6,mw7,mw2,mw3,mw4,mw5,mw187]),(12,10,1,mn1421,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw187])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC56p : mcC56.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC57 : List MemoKey := [(12,10,1,mn1422,[mw6,mw7,mw2,mw179,mw3,mw4,mw5]),(12,10,1,mn1423,[mw6,mw7,mw2,mw179,mw33,mw3,mw4,mw5]),(12,10,1,mn1428,[mw6,mw7,mw2,mw3,mw4,mw5,mw81]),(12,10,1,mn1429,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw81]),(12,10,1,mn1430,[mw188,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1431,[mw188,mw6,mw7,mw2,mw3,mw4,mw5,mw34]),(12,10,1,mn1432,[mw6,mw7,mw2,mw3,mw4,mw5,mw125]),(12,10,1,mn1433,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw125])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC57p : mcC57.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC58 : List MemoKey := [(12,10,1,mn1434,[mw6,mw189,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1435,[mw6,mw189,mw7,mw2,mw3,mw4,mw5,mw34]),(12,10,1,mn1436,[mw6,mw7,mw2,mw3,mw4,mw5,mw155]),(12,10,1,mn1437,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw155]),(12,10,1,mn1438,[mw6,mw7,mw190,mw2,mw3,mw4,mw5]),(12,10,1,mn1439,[mw6,mw7,mw190,mw2,mw3,mw4,mw5,mw34]),(12,10,1,mn1440,[mw6,mw7,mw2,mw3,mw4,mw5,mw173]),(12,10,1,mn1441,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw173])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC58p : mcC58.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC59 : List MemoKey := [(12,10,1,mn1442,[mw6,mw7,mw2,mw191,mw3,mw4,mw5]),(12,10,1,mn1443,[mw6,mw7,mw2,mw191,mw3,mw4,mw5,mw34]),(12,10,1,mn1444,[mw7,mw2,mw3,mw192,mw4,mw5]),(12,10,1,mn1445,[mw7,mw2,mw3,mw35,mw192,mw4,mw5]),(12,10,1,mn1446,[mw6,mw7,mw2,mw3,mw192,mw4,mw5]),(12,10,1,mn1447,[mw6,mw7,mw2,mw3,mw35,mw192,mw4,mw5]),(12,10,1,mn1448,[mw87,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1449,[mw87,mw6,mw7,mw2,mw3,mw35,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC59p : mcC59.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC60 : List MemoKey := [(12,10,1,mn1450,[mw6,mw7,mw2,mw3,mw4,mw193,mw5]),(12,10,1,mn1451,[mw6,mw7,mw2,mw3,mw35,mw4,mw193,mw5]),(12,10,1,mn1452,[mw6,mw131,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1453,[mw6,mw131,mw7,mw2,mw3,mw35,mw4,mw5]),(12,10,1,mn1454,[mw6,mw7,mw2,mw3,mw4,mw5,mw194]),(12,10,1,mn1455,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw194]),(12,10,1,mn1456,[mw6,mw7,mw161,mw2,mw3,mw4,mw5]),(12,10,1,mn1457,[mw6,mw7,mw161,mw2,mw3,mw35,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC60p : mcC60.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC61 : List MemoKey := [(12,10,1,mn1458,[mw6,mw7,mw2,mw3,mw4,mw5,mw195]),(12,10,1,mn1459,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw195]),(12,10,1,mn1460,[mw6,mw7,mw2,mw179,mw3,mw4,mw5]),(12,10,1,mn1461,[mw6,mw7,mw2,mw179,mw3,mw35,mw4,mw5]),(12,10,0,mn1462,[mw6,mw196,mw7,mw2,mw3,mw4]),(12,10,0,mn1463,[mw6,mw197,mw196,mw7,mw2,mw3,mw4]),(12,10,0,mn1464,[mw198,mw6,mw7,mw2,mw3,mw4]),(12,10,0,mn1465,[mw198,mw6,mw197,mw7,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC61p : mcC61.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC62 : List MemoKey := [(12,10,0,mn1466,[mw6,mw7,mw199,mw2,mw3,mw4]),(12,10,0,mn1467,[mw6,mw197,mw7,mw199,mw2,mw3,mw4]),(12,10,0,mn1468,[mw6,mw200,mw7,mw2,mw3,mw4]),(12,10,0,mn1469,[mw6,mw200,mw197,mw7,mw2,mw3,mw4]),(12,10,0,mn1470,[mw6,mw7,mw2,mw201,mw3,mw4]),(12,10,0,mn1471,[mw6,mw197,mw7,mw2,mw201,mw3,mw4]),(12,10,0,mn1472,[mw6,mw202,mw7,mw2,mw3,mw4]),(12,10,0,mn1473,[mw6,mw202,mw197,mw7,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC62p : mcC62.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC63 : List MemoKey := [(12,10,0,mn1474,[mw6,mw7,mw2,mw3,mw203,mw4]),(12,10,0,mn1475,[mw6,mw197,mw7,mw2,mw3,mw203,mw4]),(12,10,0,mn1476,[mw6,mw204,mw7,mw2,mw3,mw4]),(12,10,0,mn1477,[mw6,mw204,mw197,mw7,mw2,mw3,mw4]),(12,10,0,mn1478,[mw6,mw7,mw2,mw3,mw4,mw205]),(12,10,0,mn1479,[mw6,mw197,mw7,mw2,mw3,mw4,mw205]),(12,10,0,mn1480,[mw6,mw206,mw7,mw2,mw3,mw4]),(12,10,0,mn1481,[mw6,mw206,mw197,mw7,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC63p : mcC63.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC64 : List MemoKey := [(12,10,0,mn1463,[mw6,mw196,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1482,[mw6,mw197,mw196,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1465,[mw198,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1483,[mw198,mw6,mw197,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1467,[mw6,mw7,mw199,mw2,mw3,mw4,mw5]),(12,10,0,mn1484,[mw6,mw197,mw7,mw199,mw2,mw3,mw4,mw5]),(12,10,0,mn1469,[mw6,mw200,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1485,[mw6,mw200,mw197,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC64p : mcC64.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC65 : List MemoKey := [(12,10,0,mn1471,[mw6,mw7,mw2,mw201,mw3,mw4,mw5]),(12,10,0,mn1486,[mw6,mw197,mw7,mw2,mw201,mw3,mw4,mw5]),(12,10,0,mn1473,[mw6,mw202,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1487,[mw6,mw202,mw197,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1475,[mw6,mw7,mw2,mw3,mw203,mw4,mw5]),(12,10,0,mn1488,[mw6,mw197,mw7,mw2,mw3,mw203,mw4,mw5]),(12,10,0,mn1477,[mw6,mw204,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1489,[mw6,mw204,mw197,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC65p : mcC65.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC66 : List MemoKey := [(12,10,0,mn1479,[mw6,mw7,mw2,mw3,mw4,mw205,mw5]),(12,10,0,mn1490,[mw6,mw197,mw7,mw2,mw3,mw4,mw205,mw5]),(12,10,0,mn1481,[mw6,mw206,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1491,[mw6,mw206,mw197,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1492,[mw6,mw7,mw207,mw2,mw3,mw5]),(12,10,0,mn1493,[mw6,mw7,mw208,mw207,mw2,mw3,mw5]),(12,10,0,mn1494,[mw209,mw6,mw7,mw2,mw3,mw5]),(12,10,0,mn1495,[mw209,mw6,mw7,mw208,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC66p : mcC66.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC67 : List MemoKey := [(12,10,0,mn1496,[mw6,mw7,mw210,mw2,mw3,mw5]),(12,10,0,mn1497,[mw6,mw7,mw208,mw210,mw2,mw3,mw5]),(12,10,0,mn1498,[mw6,mw211,mw7,mw2,mw3,mw5]),(12,10,0,mn1499,[mw6,mw211,mw7,mw208,mw2,mw3,mw5]),(12,10,0,mn1500,[mw6,mw7,mw2,mw212,mw3,mw5]),(12,10,0,mn1501,[mw6,mw7,mw208,mw2,mw212,mw3,mw5]),(12,10,0,mn1502,[mw6,mw7,mw213,mw2,mw3,mw5]),(12,10,0,mn1503,[mw6,mw7,mw213,mw208,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC67p : mcC67.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC68 : List MemoKey := [(12,10,0,mn1504,[mw6,mw7,mw2,mw3,mw214,mw5]),(12,10,0,mn1505,[mw6,mw7,mw208,mw2,mw3,mw214,mw5]),(12,10,0,mn1506,[mw6,mw7,mw215,mw2,mw3,mw5]),(12,10,0,mn1507,[mw6,mw7,mw215,mw208,mw2,mw3,mw5]),(12,10,0,mn1480,[mw6,mw7,mw2,mw3,mw5,mw216]),(12,10,0,mn1508,[mw6,mw7,mw208,mw2,mw3,mw5,mw216]),(12,10,0,mn1478,[mw6,mw7,mw217,mw2,mw3,mw5]),(12,10,0,mn1509,[mw6,mw7,mw217,mw208,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC68p : mcC68.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC69 : List MemoKey := [(12,10,0,mn1493,[mw6,mw7,mw207,mw2,mw3,mw4,mw5]),(12,10,0,mn1510,[mw6,mw7,mw208,mw207,mw2,mw3,mw4,mw5]),(12,10,0,mn1495,[mw209,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1511,[mw209,mw6,mw7,mw208,mw2,mw3,mw4,mw5]),(12,10,0,mn1497,[mw6,mw7,mw210,mw2,mw3,mw4,mw5]),(12,10,0,mn1512,[mw6,mw7,mw208,mw210,mw2,mw3,mw4,mw5]),(12,10,0,mn1499,[mw6,mw211,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1513,[mw6,mw211,mw7,mw208,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC69p : mcC69.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC70 : List MemoKey := [(12,10,0,mn1501,[mw6,mw7,mw2,mw212,mw3,mw4,mw5]),(12,10,0,mn1514,[mw6,mw7,mw208,mw2,mw212,mw3,mw4,mw5]),(12,10,0,mn1503,[mw6,mw7,mw213,mw2,mw3,mw4,mw5]),(12,10,0,mn1515,[mw6,mw7,mw213,mw208,mw2,mw3,mw4,mw5]),(12,10,0,mn1505,[mw6,mw7,mw2,mw3,mw214,mw4,mw5]),(12,10,0,mn1516,[mw6,mw7,mw208,mw2,mw3,mw214,mw4,mw5]),(12,10,0,mn1507,[mw6,mw7,mw215,mw2,mw3,mw4,mw5]),(12,10,0,mn1517,[mw6,mw7,mw215,mw208,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC70p : mcC70.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC71 : List MemoKey := [(12,10,0,mn1508,[mw6,mw7,mw2,mw3,mw4,mw5,mw216]),(12,10,0,mn1518,[mw6,mw7,mw208,mw2,mw3,mw4,mw5,mw216]),(12,10,0,mn1509,[mw6,mw7,mw217,mw2,mw3,mw4,mw5]),(12,10,0,mn1519,[mw6,mw7,mw217,mw208,mw2,mw3,mw4,mw5]),(12,10,0,mn1520,[mw6,mw7,mw218,mw2,mw4,mw5]),(12,10,0,mn1521,[mw6,mw7,mw219,mw218,mw2,mw4,mw5]),(12,10,0,mn1522,[mw220,mw6,mw7,mw2,mw4,mw5]),(12,10,0,mn1523,[mw220,mw6,mw7,mw219,mw2,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC71p : mcC71.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC72 : List MemoKey := [(12,10,0,mn1524,[mw6,mw7,mw221,mw2,mw4,mw5]),(12,10,0,mn1525,[mw6,mw7,mw219,mw221,mw2,mw4,mw5]),(12,10,0,mn1526,[mw6,mw222,mw7,mw2,mw4,mw5]),(12,10,0,mn1527,[mw6,mw222,mw7,mw219,mw2,mw4,mw5]),(12,10,0,mn1528,[mw6,mw7,mw2,mw223,mw4,mw5]),(12,10,0,mn1529,[mw6,mw7,mw219,mw2,mw223,mw4,mw5]),(12,10,0,mn1530,[mw6,mw7,mw224,mw2,mw4,mw5]),(12,10,0,mn1531,[mw6,mw7,mw224,mw219,mw2,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC72p : mcC72.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC73 : List MemoKey := [(12,10,0,mn1506,[mw6,mw7,mw2,mw4,mw225,mw5]),(12,10,0,mn1532,[mw6,mw7,mw219,mw2,mw4,mw225,mw5]),(12,10,0,mn1504,[mw6,mw7,mw226,mw2,mw4,mw5]),(12,10,0,mn1533,[mw6,mw7,mw226,mw219,mw2,mw4,mw5]),(12,10,0,mn1476,[mw6,mw7,mw2,mw4,mw5,mw227]),(12,10,0,mn1534,[mw6,mw7,mw219,mw2,mw4,mw5,mw227]),(12,10,0,mn1474,[mw6,mw7,mw228,mw2,mw4,mw5]),(12,10,0,mn1535,[mw6,mw7,mw228,mw219,mw2,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC73p : mcC73.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC74 : List MemoKey := [(12,10,0,mn1521,[mw6,mw7,mw218,mw2,mw3,mw4,mw5]),(12,10,0,mn1536,[mw6,mw7,mw219,mw218,mw2,mw3,mw4,mw5]),(12,10,0,mn1523,[mw220,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1537,[mw220,mw6,mw7,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1525,[mw6,mw7,mw221,mw2,mw3,mw4,mw5]),(12,10,0,mn1538,[mw6,mw7,mw219,mw221,mw2,mw3,mw4,mw5]),(12,10,0,mn1527,[mw6,mw222,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1539,[mw6,mw222,mw7,mw219,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC74p : mcC74.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC75 : List MemoKey := [(12,10,0,mn1529,[mw6,mw7,mw2,mw223,mw3,mw4,mw5]),(12,10,0,mn1540,[mw6,mw7,mw219,mw2,mw223,mw3,mw4,mw5]),(12,10,0,mn1531,[mw6,mw7,mw224,mw2,mw3,mw4,mw5]),(12,10,0,mn1541,[mw6,mw7,mw224,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1532,[mw6,mw7,mw2,mw3,mw4,mw225,mw5]),(12,10,0,mn1542,[mw6,mw7,mw219,mw2,mw3,mw4,mw225,mw5]),(12,10,0,mn1533,[mw6,mw7,mw226,mw2,mw3,mw4,mw5]),(12,10,0,mn1543,[mw6,mw7,mw226,mw219,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC75p : mcC75.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC76 : List MemoKey := [(12,10,0,mn1534,[mw6,mw7,mw2,mw3,mw4,mw5,mw227]),(12,10,0,mn1544,[mw6,mw7,mw219,mw2,mw3,mw4,mw5,mw227]),(12,10,0,mn1535,[mw6,mw7,mw228,mw2,mw3,mw4,mw5]),(12,10,0,mn1545,[mw6,mw7,mw228,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1546,[mw6,mw7,mw229,mw3,mw4,mw5]),(12,10,0,mn1547,[mw6,mw7,mw230,mw229,mw3,mw4,mw5]),(12,10,0,mn1548,[mw231,mw6,mw7,mw3,mw4,mw5]),(12,10,0,mn1549,[mw231,mw6,mw7,mw230,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC76p : mcC76.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC77 : List MemoKey := [(12,10,0,mn1550,[mw6,mw7,mw232,mw3,mw4,mw5]),(12,10,0,mn1551,[mw6,mw7,mw230,mw232,mw3,mw4,mw5]),(12,10,0,mn1552,[mw6,mw233,mw7,mw3,mw4,mw5]),(12,10,0,mn1553,[mw6,mw233,mw7,mw230,mw3,mw4,mw5]),(12,10,0,mn1530,[mw6,mw7,mw3,mw234,mw4,mw5]),(12,10,0,mn1554,[mw6,mw7,mw230,mw3,mw234,mw4,mw5]),(12,10,0,mn1528,[mw6,mw7,mw235,mw3,mw4,mw5]),(12,10,0,mn1555,[mw6,mw7,mw235,mw230,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC77p : mcC77.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC78 : List MemoKey := [(12,10,0,mn1502,[mw6,mw7,mw3,mw4,mw236,mw5]),(12,10,0,mn1556,[mw6,mw7,mw230,mw3,mw4,mw236,mw5]),(12,10,0,mn1500,[mw6,mw7,mw237,mw3,mw4,mw5]),(12,10,0,mn1557,[mw6,mw7,mw237,mw230,mw3,mw4,mw5]),(12,10,0,mn1472,[mw6,mw7,mw3,mw4,mw5,mw238]),(12,10,0,mn1558,[mw6,mw7,mw230,mw3,mw4,mw5,mw238]),(12,10,0,mn1470,[mw6,mw7,mw239,mw3,mw4,mw5]),(12,10,0,mn1559,[mw6,mw7,mw239,mw230,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC78p : mcC78.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC79 : List MemoKey := [(12,10,0,mn1547,[mw6,mw7,mw2,mw229,mw3,mw4,mw5]),(12,10,0,mn1560,[mw6,mw7,mw2,mw230,mw229,mw3,mw4,mw5]),(12,10,0,mn1549,[mw231,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1561,[mw231,mw6,mw7,mw2,mw230,mw3,mw4,mw5]),(12,10,0,mn1551,[mw6,mw7,mw2,mw232,mw3,mw4,mw5]),(12,10,0,mn1562,[mw6,mw7,mw2,mw230,mw232,mw3,mw4,mw5]),(12,10,0,mn1553,[mw6,mw233,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1563,[mw6,mw233,mw7,mw2,mw230,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC79p : mcC79.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC80 : List MemoKey := [(12,10,0,mn1554,[mw6,mw7,mw2,mw3,mw234,mw4,mw5]),(12,10,0,mn1564,[mw6,mw7,mw2,mw230,mw3,mw234,mw4,mw5]),(12,10,0,mn1555,[mw6,mw7,mw2,mw235,mw3,mw4,mw5]),(12,10,0,mn1565,[mw6,mw7,mw2,mw235,mw230,mw3,mw4,mw5]),(12,10,0,mn1556,[mw6,mw7,mw2,mw3,mw4,mw236,mw5]),(12,10,0,mn1566,[mw6,mw7,mw2,mw230,mw3,mw4,mw236,mw5]),(12,10,0,mn1557,[mw6,mw7,mw2,mw237,mw3,mw4,mw5]),(12,10,0,mn1567,[mw6,mw7,mw2,mw237,mw230,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC80p : mcC80.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC81 : List MemoKey := [(12,10,0,mn1558,[mw6,mw7,mw2,mw3,mw4,mw5,mw238]),(12,10,0,mn1568,[mw6,mw7,mw2,mw230,mw3,mw4,mw5,mw238]),(12,10,0,mn1559,[mw6,mw7,mw2,mw239,mw3,mw4,mw5]),(12,10,0,mn1569,[mw6,mw7,mw2,mw239,mw230,mw3,mw4,mw5]),(12,10,0,mn1570,[mw6,mw2,mw3,mw4,mw240,mw5]),(12,10,0,mn1571,[mw6,mw2,mw3,mw4,mw241,mw240,mw5]),(12,10,0,mn1572,[mw242,mw6,mw2,mw3,mw4,mw5]),(12,10,0,mn1573,[mw242,mw6,mw2,mw3,mw4,mw241,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC81p : mcC81.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC82 : List MemoKey := [(12,10,0,mn1552,[mw6,mw2,mw3,mw4,mw243,mw5]),(12,10,0,mn1574,[mw6,mw2,mw3,mw4,mw241,mw243,mw5]),(12,10,0,mn1550,[mw6,mw244,mw2,mw3,mw4,mw5]),(12,10,0,mn1575,[mw6,mw244,mw2,mw3,mw4,mw241,mw5]),(12,10,0,mn1526,[mw6,mw2,mw3,mw4,mw245,mw5]),(12,10,0,mn1576,[mw6,mw2,mw3,mw4,mw241,mw245,mw5]),(12,10,0,mn1524,[mw6,mw2,mw246,mw3,mw4,mw5]),(12,10,0,mn1577,[mw6,mw2,mw246,mw3,mw4,mw241,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC82p : mcC82.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC83 : List MemoKey := [(12,10,0,mn1498,[mw6,mw2,mw3,mw4,mw247,mw5]),(12,10,0,mn1578,[mw6,mw2,mw3,mw4,mw241,mw247,mw5]),(12,10,0,mn1496,[mw6,mw2,mw3,mw248,mw4,mw5]),(12,10,0,mn1579,[mw6,mw2,mw3,mw248,mw4,mw241,mw5]),(12,10,0,mn1468,[mw6,mw2,mw3,mw4,mw5,mw249]),(12,10,0,mn1580,[mw6,mw2,mw3,mw4,mw241,mw5,mw249]),(12,10,0,mn1466,[mw6,mw2,mw3,mw4,mw250,mw5]),(12,10,0,mn1581,[mw6,mw2,mw3,mw4,mw250,mw241,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC83p : mcC83.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC84 : List MemoKey := [(12,10,0,mn1571,[mw6,mw7,mw2,mw3,mw4,mw240,mw5]),(12,10,0,mn1582,[mw6,mw7,mw2,mw3,mw4,mw241,mw240,mw5]),(12,10,0,mn1573,[mw242,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1583,[mw242,mw6,mw7,mw2,mw3,mw4,mw241,mw5]),(12,10,0,mn1574,[mw6,mw7,mw2,mw3,mw4,mw243,mw5]),(12,10,0,mn1584,[mw6,mw7,mw2,mw3,mw4,mw241,mw243,mw5]),(12,10,0,mn1575,[mw6,mw7,mw244,mw2,mw3,mw4,mw5]),(12,10,0,mn1585,[mw6,mw7,mw244,mw2,mw3,mw4,mw241,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC84p : mcC84.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC85 : List MemoKey := [(12,10,0,mn1576,[mw6,mw7,mw2,mw3,mw4,mw245,mw5]),(12,10,0,mn1586,[mw6,mw7,mw2,mw3,mw4,mw241,mw245,mw5]),(12,10,0,mn1577,[mw6,mw7,mw2,mw246,mw3,mw4,mw5]),(12,10,0,mn1587,[mw6,mw7,mw2,mw246,mw3,mw4,mw241,mw5]),(12,10,0,mn1578,[mw6,mw7,mw2,mw3,mw4,mw247,mw5]),(12,10,0,mn1588,[mw6,mw7,mw2,mw3,mw4,mw241,mw247,mw5]),(12,10,0,mn1579,[mw6,mw7,mw2,mw3,mw248,mw4,mw5]),(12,10,0,mn1589,[mw6,mw7,mw2,mw3,mw248,mw4,mw241,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC85p : mcC85.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC86 : List MemoKey := [(12,10,0,mn1580,[mw6,mw7,mw2,mw3,mw4,mw5,mw249]),(12,10,0,mn1590,[mw6,mw7,mw2,mw3,mw4,mw241,mw5,mw249]),(12,10,0,mn1581,[mw6,mw7,mw2,mw3,mw4,mw250,mw5]),(12,10,0,mn1591,[mw6,mw7,mw2,mw3,mw4,mw250,mw241,mw5]),(12,10,0,mn1572,[mw7,mw2,mw3,mw4,mw5,mw251]),(12,10,0,mn1592,[mw7,mw2,mw3,mw4,mw5,mw252,mw251]),(12,10,0,mn1570,[mw253,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1593,[mw253,mw7,mw2,mw3,mw4,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC86p : mcC86.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC87 : List MemoKey := [(12,10,0,mn1548,[mw7,mw2,mw3,mw4,mw5,mw254]),(12,10,0,mn1594,[mw7,mw2,mw3,mw4,mw5,mw252,mw254]),(12,10,0,mn1546,[mw7,mw255,mw2,mw3,mw4,mw5]),(12,10,0,mn1595,[mw7,mw255,mw2,mw3,mw4,mw5,mw252]),(12,10,0,mn1522,[mw7,mw2,mw3,mw4,mw5,mw256]),(12,10,0,mn1596,[mw7,mw2,mw3,mw4,mw5,mw252,mw256]),(12,10,0,mn1520,[mw7,mw2,mw257,mw3,mw4,mw5]),(12,10,0,mn1597,[mw7,mw2,mw257,mw3,mw4,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC87p : mcC87.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC88 : List MemoKey := [(12,10,0,mn1494,[mw7,mw2,mw3,mw4,mw5,mw258]),(12,10,0,mn1598,[mw7,mw2,mw3,mw4,mw5,mw252,mw258]),(12,10,0,mn1492,[mw7,mw2,mw3,mw259,mw4,mw5]),(12,10,0,mn1599,[mw7,mw2,mw3,mw259,mw4,mw5,mw252]),(12,10,0,mn1464,[mw7,mw2,mw3,mw4,mw5,mw260]),(12,10,0,mn1600,[mw7,mw2,mw3,mw4,mw5,mw252,mw260]),(12,10,0,mn1462,[mw7,mw2,mw3,mw4,mw261,mw5]),(12,10,0,mn1601,[mw7,mw2,mw3,mw4,mw261,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC88p : mcC88.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC89 : List MemoKey := [(12,10,0,mn1592,[mw6,mw7,mw2,mw3,mw4,mw5,mw251]),(12,10,0,mn1602,[mw6,mw7,mw2,mw3,mw4,mw5,mw252,mw251]),(12,10,0,mn1593,[mw6,mw253,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1603,[mw6,mw253,mw7,mw2,mw3,mw4,mw5,mw252]),(12,10,0,mn1594,[mw6,mw7,mw2,mw3,mw4,mw5,mw254]),(12,10,0,mn1604,[mw6,mw7,mw2,mw3,mw4,mw5,mw252,mw254]),(12,10,0,mn1595,[mw6,mw7,mw255,mw2,mw3,mw4,mw5]),(12,10,0,mn1605,[mw6,mw7,mw255,mw2,mw3,mw4,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC89p : mcC89.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC90 : List MemoKey := [(12,10,0,mn1596,[mw6,mw7,mw2,mw3,mw4,mw5,mw256]),(12,10,0,mn1606,[mw6,mw7,mw2,mw3,mw4,mw5,mw252,mw256]),(12,10,0,mn1597,[mw6,mw7,mw2,mw257,mw3,mw4,mw5]),(12,10,0,mn1607,[mw6,mw7,mw2,mw257,mw3,mw4,mw5,mw252]),(12,10,0,mn1598,[mw6,mw7,mw2,mw3,mw4,mw5,mw258]),(12,10,0,mn1608,[mw6,mw7,mw2,mw3,mw4,mw5,mw252,mw258]),(12,10,0,mn1599,[mw6,mw7,mw2,mw3,mw259,mw4,mw5]),(12,10,0,mn1609,[mw6,mw7,mw2,mw3,mw259,mw4,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC90p : mcC90.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC91 : List MemoKey := [(12,10,0,mn1600,[mw6,mw7,mw2,mw3,mw4,mw5,mw260]),(12,10,0,mn1610,[mw6,mw7,mw2,mw3,mw4,mw5,mw252,mw260]),(12,10,0,mn1601,[mw6,mw7,mw2,mw3,mw4,mw261,mw5]),(12,10,0,mn1611,[mw6,mw7,mw2,mw3,mw4,mw261,mw5,mw252])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC91p : mcC91.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def memoChunksC : List {xs : List MemoKey // xs.all (fun e => !(keyRun originalC e)) = true} := [⟨mcC0,mcC0p⟩,⟨mcC1,mcC1p⟩,⟨mcC2,mcC2p⟩,⟨mcC3,mcC3p⟩,⟨mcC4,mcC4p⟩,⟨mcC5,mcC5p⟩,⟨mcC6,mcC6p⟩,⟨mcC7,mcC7p⟩,⟨mcC8,mcC8p⟩,⟨mcC9,mcC9p⟩,⟨mcC10,mcC10p⟩,⟨mcC11,mcC11p⟩,⟨mcC12,mcC12p⟩,⟨mcC13,mcC13p⟩,⟨mcC14,mcC14p⟩,⟨mcC15,mcC15p⟩,⟨mcC16,mcC16p⟩,⟨mcC17,mcC17p⟩,⟨mcC18,mcC18p⟩,⟨mcC19,mcC19p⟩,⟨mcC20,mcC20p⟩,⟨mcC21,mcC21p⟩,⟨mcC22,mcC22p⟩,⟨mcC23,mcC23p⟩,⟨mcC24,mcC24p⟩,⟨mcC25,mcC25p⟩,⟨mcC26,mcC26p⟩,⟨mcC27,mcC27p⟩,⟨mcC28,mcC28p⟩,⟨mcC29,mcC29p⟩,⟨mcC30,mcC30p⟩,⟨mcC31,mcC31p⟩,⟨mcC32,mcC32p⟩,⟨mcC33,mcC33p⟩,⟨mcC34,mcC34p⟩,⟨mcC35,mcC35p⟩,⟨mcC36,mcC36p⟩,⟨mcC37,mcC37p⟩,⟨mcC38,mcC38p⟩,⟨mcC39,mcC39p⟩,⟨mcC40,mcC40p⟩,⟨mcC41,mcC41p⟩,⟨mcC42,mcC42p⟩,⟨mcC43,mcC43p⟩,⟨mcC44,mcC44p⟩,⟨mcC45,mcC45p⟩,⟨mcC46,mcC46p⟩,⟨mcC47,mcC47p⟩,⟨mcC48,mcC48p⟩,⟨mcC49,mcC49p⟩,⟨mcC50,mcC50p⟩,⟨mcC51,mcC51p⟩,⟨mcC52,mcC52p⟩,⟨mcC53,mcC53p⟩,⟨mcC54,mcC54p⟩,⟨mcC55,mcC55p⟩,⟨mcC56,mcC56p⟩,⟨mcC57,mcC57p⟩,⟨mcC58,mcC58p⟩,⟨mcC59,mcC59p⟩,⟨mcC60,mcC60p⟩,⟨mcC61,mcC61p⟩,⟨mcC62,mcC62p⟩,⟨mcC63,mcC63p⟩,⟨mcC64,mcC64p⟩,⟨mcC65,mcC65p⟩,⟨mcC66,mcC66p⟩,⟨mcC67,mcC67p⟩,⟨mcC68,mcC68p⟩,⟨mcC69,mcC69p⟩,⟨mcC70,mcC70p⟩,⟨mcC71,mcC71p⟩,⟨mcC72,mcC72p⟩,⟨mcC73,mcC73p⟩,⟨mcC74,mcC74p⟩,⟨mcC75,mcC75p⟩,⟨mcC76,mcC76p⟩,⟨mcC77,mcC77p⟩,⟨mcC78,mcC78p⟩,⟨mcC79,mcC79p⟩,⟨mcC80,mcC80p⟩,⟨mcC81,mcC81p⟩,⟨mcC82,mcC82p⟩,⟨mcC83,mcC83p⟩,⟨mcC84,mcC84p⟩,⟨mcC85,mcC85p⟩,⟨mcC86,mcC86p⟩,⟨mcC87,mcC87p⟩,⟨mcC88,mcC88p⟩,⟨mcC89,mcC89p⟩,⟨mcC90,mcC90p⟩,⟨mcC91,mcC91p⟩]
def memoKeysC : List MemoKey := (memoChunksC.map Subtype.val).flatten
lemma memoKeysC_sound : ∀ e ∈ memoKeysC, keyRun originalC e = false := checkedChunks_sound (keyRun originalC) memoChunksC
def mcS0 : List MemoKey := [(11,10,1,mn481,[mw0,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn482,[mw0,mw6,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn483,[mw0,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn484,[mw0,mw6,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn485,[mw6,mw7,mw1,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn486,[mw9,mw6,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn487,[mw6,mw7,mw1,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn488,[mw11,mw6,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS0p : mcS0.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS1 : List MemoKey := [(11,10,1,mn489,[mw6,mw7,mw1,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn490,[mw13,mw6,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn491,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn492,[mw15,mw6,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn493,[mw6,mw7,mw1,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn494,[mw6,mw17,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn495,[mw6,mw7,mw1,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn496,[mw6,mw19,mw7,mw1,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS1p : mcS1.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS2 : List MemoKey := [(11,10,1,mn497,[mw6,mw7,mw1,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn498,[mw6,mw21,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn499,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn500,[mw6,mw23,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn501,[mw6,mw7,mw1,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn502,[mw6,mw7,mw1,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn503,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn504,[mw6,mw7,mw1,mw27,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS2p : mcS2.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS3 : List MemoKey := [(11,10,1,mn505,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn506,[mw6,mw7,mw1,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn507,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn508,[mw6,mw7,mw1,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn509,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn510,[mw6,mw7,mw1,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn511,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn512,[mw6,mw7,mw1,mw2,mw3,mw35,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS3p : mcS3.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS4 : List MemoKey := [(11,10,1,mn529,[mw0,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn530,[mw0,mw9,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn531,[mw0,mw6,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn532,[mw0,mw11,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn533,[mw0,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn534,[mw0,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn535,[mw0,mw13,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn536,[mw0,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS4p : mcS4.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS5 : List MemoKey := [(11,10,1,mn537,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn538,[mw0,mw15,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn539,[mw0,mw6,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn540,[mw0,mw6,mw17,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn541,[mw0,mw6,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn542,[mw0,mw6,mw19,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn543,[mw0,mw6,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn544,[mw0,mw6,mw21,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS5p : mcS5.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS6 : List MemoKey := [(11,10,1,mn545,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn546,[mw0,mw6,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn547,[mw0,mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn548,[mw0,mw6,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn549,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn550,[mw0,mw6,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn551,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn552,[mw0,mw6,mw7,mw29,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS6p : mcS6.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS7 : List MemoKey := [(11,10,1,mn553,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn554,[mw0,mw6,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn555,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn556,[mw0,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn557,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn558,[mw0,mw6,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn577,[mw9,mw7,mw8,mw3,mw4,mw5]),(11,10,1,mn578,[mw9,mw6,mw7,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS7p : mcS7.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS8 : List MemoKey := [(11,10,1,mn579,[mw9,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn580,[mw9,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn581,[mw6,mw7,mw2,mw8,mw3,mw10,mw4,mw5]),(11,10,1,mn582,[mw11,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn583,[mw6,mw7,mw2,mw8,mw3,mw4,mw12,mw5]),(11,10,1,mn584,[mw13,mw6,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn585,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw14]),(11,10,1,mn586,[mw15,mw6,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS8p : mcS8.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS9 : List MemoKey := [(11,10,1,mn587,[mw6,mw7,mw2,mw8,mw16,mw3,mw4,mw5]),(11,10,1,mn588,[mw6,mw17,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn589,[mw6,mw7,mw2,mw8,mw3,mw18,mw4,mw5]),(11,10,1,mn590,[mw6,mw19,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn591,[mw6,mw7,mw2,mw8,mw3,mw4,mw20,mw5]),(11,10,1,mn592,[mw6,mw21,mw7,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn593,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw22]),(11,10,1,mn594,[mw6,mw23,mw7,mw2,mw8,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS9p : mcS9.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS10 : List MemoKey := [(11,10,1,mn595,[mw6,mw7,mw2,mw8,mw3,mw4,mw24,mw5]),(11,10,1,mn596,[mw6,mw7,mw25,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn597,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw26]),(11,10,1,mn598,[mw6,mw7,mw27,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn599,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw28]),(11,10,1,mn600,[mw6,mw7,mw29,mw2,mw8,mw3,mw4,mw5]),(11,10,1,mn601,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw30]),(11,10,1,mn602,[mw6,mw7,mw2,mw8,mw31,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS10p : mcS10.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS11 : List MemoKey := [(11,10,1,mn603,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw32]),(11,10,1,mn604,[mw6,mw7,mw2,mw8,mw33,mw3,mw4,mw5]),(11,10,1,mn605,[mw6,mw7,mw2,mw8,mw3,mw4,mw5,mw34]),(11,10,1,mn606,[mw6,mw7,mw2,mw8,mw3,mw35,mw4,mw5]),(11,10,1,mn623,[mw9,mw6,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn624,[mw9,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn625,[mw9,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn626,[mw9,mw13,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS11p : mcS11.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS12 : List MemoKey := [(11,10,1,mn627,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn628,[mw9,mw15,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn629,[mw9,mw6,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn630,[mw9,mw6,mw17,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn631,[mw9,mw6,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn632,[mw9,mw6,mw19,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn633,[mw9,mw6,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn634,[mw9,mw6,mw21,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS12p : mcS12.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS13 : List MemoKey := [(11,10,1,mn635,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn636,[mw9,mw6,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn637,[mw9,mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn638,[mw9,mw6,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn639,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn640,[mw9,mw6,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn641,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn642,[mw9,mw6,mw7,mw29,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS13p : mcS13.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS14 : List MemoKey := [(11,10,1,mn643,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn644,[mw9,mw6,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn645,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn646,[mw9,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn647,[mw9,mw6,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn648,[mw9,mw6,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn665,[mw11,mw7,mw2,mw10,mw4,mw5]),(11,10,1,mn666,[mw11,mw6,mw7,mw2,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS14p : mcS14.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS15 : List MemoKey := [(11,10,1,mn667,[mw11,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn668,[mw11,mw6,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn669,[mw6,mw7,mw2,mw3,mw10,mw4,mw12,mw5]),(11,10,1,mn670,[mw13,mw6,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn671,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw14]),(11,10,1,mn672,[mw15,mw6,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn673,[mw6,mw7,mw2,mw16,mw3,mw10,mw4,mw5]),(11,10,1,mn674,[mw6,mw17,mw7,mw2,mw3,mw10,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS15p : mcS15.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS16 : List MemoKey := [(11,10,1,mn675,[mw6,mw7,mw2,mw10,mw18,mw4,mw5]),(11,10,1,mn676,[mw6,mw7,mw2,mw3,mw10,mw18,mw4,mw5]),(11,10,1,mn677,[mw6,mw19,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn678,[mw6,mw7,mw2,mw3,mw10,mw4,mw20,mw5]),(11,10,1,mn679,[mw6,mw21,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn680,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw22]),(11,10,1,mn681,[mw6,mw23,mw7,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn682,[mw6,mw7,mw2,mw3,mw10,mw4,mw24,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS16p : mcS16.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS17 : List MemoKey := [(11,10,1,mn683,[mw6,mw7,mw25,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn684,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw26]),(11,10,1,mn685,[mw6,mw7,mw27,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn686,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw28]),(11,10,1,mn687,[mw6,mw7,mw29,mw2,mw3,mw10,mw4,mw5]),(11,10,1,mn688,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw30]),(11,10,1,mn689,[mw6,mw7,mw2,mw31,mw3,mw10,mw4,mw5]),(11,10,1,mn690,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS17p : mcS17.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS18 : List MemoKey := [(11,10,1,mn691,[mw6,mw7,mw2,mw33,mw3,mw10,mw4,mw5]),(11,10,1,mn692,[mw6,mw7,mw2,mw3,mw10,mw4,mw5,mw34]),(11,10,1,mn693,[mw6,mw7,mw2,mw3,mw10,mw35,mw4,mw5]),(11,10,1,mn710,[mw11,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn711,[mw11,mw13,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn712,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn713,[mw15,mw11,mw6,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn714,[mw11,mw6,mw7,mw2,mw16,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS18p : mcS18.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS19 : List MemoKey := [(11,10,1,mn715,[mw11,mw6,mw17,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn716,[mw11,mw6,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn717,[mw11,mw6,mw19,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn718,[mw11,mw6,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn719,[mw11,mw6,mw21,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn720,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn721,[mw11,mw6,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn722,[mw11,mw6,mw7,mw2,mw3,mw4,mw24,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS19p : mcS19.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS20 : List MemoKey := [(11,10,1,mn723,[mw11,mw6,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn724,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn725,[mw11,mw6,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn726,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn727,[mw11,mw6,mw7,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn728,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn729,[mw11,mw6,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn730,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS20p : mcS20.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS21 : List MemoKey := [(11,10,1,mn731,[mw11,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn732,[mw11,mw6,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn733,[mw11,mw6,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn750,[mw13,mw7,mw2,mw3,mw12,mw5]),(11,10,1,mn751,[mw13,mw6,mw7,mw2,mw3,mw12,mw5]),(11,10,1,mn752,[mw13,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn753,[mw13,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn754,[mw7,mw2,mw3,mw4,mw12,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS21p : mcS21.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS22 : List MemoKey := [(11,10,1,mn755,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw14]),(11,10,1,mn756,[mw15,mw6,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn757,[mw6,mw7,mw2,mw16,mw3,mw4,mw12,mw5]),(11,10,1,mn758,[mw6,mw17,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn759,[mw6,mw7,mw2,mw3,mw18,mw4,mw12,mw5]),(11,10,1,mn760,[mw6,mw19,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn761,[mw6,mw7,mw2,mw3,mw4,mw12,mw20,mw5]),(11,10,1,mn762,[mw6,mw21,mw7,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS22p : mcS22.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS23 : List MemoKey := [(11,10,1,mn763,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw22]),(11,10,1,mn764,[mw6,mw23,mw7,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn765,[mw6,mw7,mw2,mw3,mw4,mw12,mw24,mw5]),(11,10,1,mn766,[mw6,mw7,mw25,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn767,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw26]),(11,10,1,mn768,[mw6,mw7,mw27,mw2,mw3,mw4,mw12,mw5]),(11,10,1,mn769,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw28]),(11,10,1,mn770,[mw6,mw7,mw29,mw2,mw3,mw4,mw12,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS23p : mcS23.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS24 : List MemoKey := [(11,10,1,mn771,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw30]),(11,10,1,mn772,[mw6,mw7,mw2,mw31,mw3,mw4,mw12,mw5]),(11,10,1,mn773,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw32]),(11,10,1,mn774,[mw6,mw7,mw2,mw33,mw3,mw4,mw12,mw5]),(11,10,1,mn775,[mw6,mw7,mw2,mw3,mw4,mw12,mw5,mw34]),(11,10,1,mn776,[mw6,mw7,mw2,mw3,mw35,mw4,mw12,mw5]),(11,10,1,mn793,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn794,[mw15,mw13,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS24p : mcS24.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS25 : List MemoKey := [(11,10,1,mn795,[mw13,mw6,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn796,[mw13,mw6,mw17,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn797,[mw13,mw6,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn798,[mw13,mw6,mw19,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn799,[mw13,mw6,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn800,[mw13,mw6,mw21,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn801,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn802,[mw13,mw6,mw23,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS25p : mcS25.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS26 : List MemoKey := [(11,10,1,mn803,[mw13,mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn804,[mw13,mw6,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn805,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn806,[mw13,mw6,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn807,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn808,[mw13,mw6,mw7,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn809,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn810,[mw13,mw6,mw7,mw2,mw31,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS26p : mcS26.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS27 : List MemoKey := [(11,10,1,mn811,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn812,[mw13,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn813,[mw13,mw6,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn814,[mw13,mw6,mw7,mw2,mw3,mw35,mw5]),(11,10,1,mn815,[mw13,mw6,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn832,[mw15,mw7,mw2,mw3,mw4,mw14]),(11,10,1,mn833,[mw15,mw6,mw7,mw2,mw3,mw4,mw14]),(11,10,1,mn834,[mw15,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS27p : mcS27.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS28 : List MemoKey := [(11,10,1,mn835,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn836,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw14]),(11,10,1,mn837,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn838,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw14]),(11,10,1,mn839,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn840,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw14]),(11,10,1,mn841,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn842,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS28p : mcS28.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS29 : List MemoKey := [(11,10,1,mn843,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn844,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw14]),(11,10,1,mn845,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn846,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw26]),(11,10,1,mn847,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn848,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw28]),(11,10,1,mn849,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn850,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw30])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS29p : mcS29.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS30 : List MemoKey := [(11,10,1,mn851,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw14]),(11,10,1,mn852,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw32]),(11,10,1,mn853,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw14]),(11,10,1,mn854,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw34]),(11,10,1,mn855,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw14]),(11,10,1,mn874,[mw15,mw6,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn875,[mw15,mw6,mw17,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn876,[mw15,mw6,mw7,mw2,mw3,mw18,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS30p : mcS30.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS31 : List MemoKey := [(11,10,1,mn877,[mw15,mw6,mw19,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn878,[mw15,mw6,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn879,[mw15,mw6,mw21,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn880,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn881,[mw15,mw6,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn882,[mw15,mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn883,[mw15,mw6,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn884,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS31p : mcS31.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS32 : List MemoKey := [(11,10,1,mn885,[mw15,mw6,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn886,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn887,[mw15,mw6,mw7,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn888,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn889,[mw15,mw6,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn890,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn891,[mw15,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn892,[mw15,mw6,mw7,mw2,mw3,mw4,mw5,mw34])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS32p : mcS32.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS33 : List MemoKey := [(11,10,1,mn893,[mw15,mw6,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn910,[mw6,mw17,mw16,mw3,mw4,mw5]),(11,10,1,mn911,[mw6,mw17,mw7,mw16,mw3,mw4,mw5]),(11,10,1,mn912,[mw6,mw17,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn913,[mw6,mw17,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn914,[mw6,mw7,mw2,mw16,mw3,mw18,mw4,mw5]),(11,10,1,mn915,[mw6,mw19,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn916,[mw6,mw7,mw2,mw16,mw3,mw4,mw20,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS33p : mcS33.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS34 : List MemoKey := [(11,10,1,mn917,[mw6,mw21,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn918,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw22]),(11,10,1,mn919,[mw6,mw23,mw7,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn920,[mw6,mw7,mw2,mw16,mw3,mw4,mw24,mw5]),(11,10,1,mn921,[mw6,mw7,mw25,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn922,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw26]),(11,10,1,mn923,[mw6,mw7,mw27,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn924,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw28])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS34p : mcS34.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS35 : List MemoKey := [(11,10,1,mn925,[mw6,mw7,mw29,mw2,mw16,mw3,mw4,mw5]),(11,10,1,mn926,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw30]),(11,10,1,mn927,[mw6,mw7,mw2,mw16,mw31,mw3,mw4,mw5]),(11,10,1,mn928,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw32]),(11,10,1,mn929,[mw6,mw7,mw2,mw16,mw33,mw3,mw4,mw5]),(11,10,1,mn930,[mw6,mw7,mw2,mw16,mw3,mw4,mw5,mw34]),(11,10,1,mn931,[mw6,mw7,mw2,mw16,mw3,mw35,mw4,mw5]),(11,10,1,mn948,[mw6,mw17,mw7,mw2,mw3,mw18,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS35p : mcS35.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS36 : List MemoKey := [(11,10,1,mn949,[mw6,mw17,mw19,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn950,[mw6,mw17,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn951,[mw6,mw17,mw21,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn952,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn953,[mw6,mw17,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn954,[mw6,mw17,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn955,[mw6,mw17,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn956,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS36p : mcS36.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS37 : List MemoKey := [(11,10,1,mn957,[mw6,mw17,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn958,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn959,[mw6,mw17,mw7,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn960,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn961,[mw6,mw17,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn962,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn963,[mw6,mw17,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn964,[mw6,mw17,mw7,mw2,mw3,mw4,mw5,mw34])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS37p : mcS37.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS38 : List MemoKey := [(11,10,1,mn965,[mw6,mw17,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn982,[mw6,mw19,mw2,mw18,mw4,mw5]),(11,10,1,mn983,[mw6,mw19,mw7,mw2,mw18,mw4,mw5]),(11,10,1,mn984,[mw6,mw19,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn985,[mw6,mw19,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn986,[mw6,mw7,mw2,mw3,mw18,mw4,mw20,mw5]),(11,10,1,mn987,[mw6,mw21,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn988,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS38p : mcS38.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS39 : List MemoKey := [(11,10,1,mn989,[mw6,mw23,mw7,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn990,[mw6,mw7,mw2,mw3,mw18,mw4,mw24,mw5]),(11,10,1,mn991,[mw6,mw7,mw25,mw2,mw18,mw4,mw5]),(11,10,1,mn992,[mw6,mw7,mw25,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn993,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw26]),(11,10,1,mn994,[mw6,mw7,mw27,mw2,mw3,mw18,mw4,mw5]),(11,10,1,mn995,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw28]),(11,10,1,mn996,[mw6,mw7,mw29,mw2,mw3,mw18,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS39p : mcS39.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS40 : List MemoKey := [(11,10,1,mn997,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw30]),(11,10,1,mn998,[mw6,mw7,mw2,mw31,mw3,mw18,mw4,mw5]),(11,10,1,mn999,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw32]),(11,10,1,mn1000,[mw6,mw7,mw2,mw33,mw3,mw18,mw4,mw5]),(11,10,1,mn1001,[mw6,mw7,mw2,mw3,mw18,mw4,mw5,mw34]),(11,10,1,mn1002,[mw6,mw7,mw2,mw3,mw18,mw35,mw4,mw5]),(11,10,1,mn1021,[mw6,mw19,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn1022,[mw6,mw19,mw21,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS40p : mcS40.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS41 : List MemoKey := [(11,10,1,mn1023,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn1024,[mw6,mw19,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn1025,[mw6,mw19,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn1026,[mw6,mw19,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn1027,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn1028,[mw6,mw19,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn1029,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn1030,[mw6,mw19,mw7,mw29,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS41p : mcS41.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS42 : List MemoKey := [(11,10,1,mn1031,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn1032,[mw6,mw19,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn1033,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn1034,[mw6,mw19,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn1035,[mw6,mw19,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn1036,[mw6,mw19,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn1053,[mw6,mw21,mw2,mw3,mw20,mw5]),(11,10,1,mn1054,[mw6,mw21,mw7,mw2,mw3,mw20,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS42p : mcS42.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS43 : List MemoKey := [(11,10,1,mn1055,[mw6,mw21,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn1056,[mw6,mw21,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn1057,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw22]),(11,10,1,mn1058,[mw6,mw23,mw7,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn1059,[mw6,mw7,mw2,mw3,mw4,mw20,mw24,mw5]),(11,10,1,mn1060,[mw6,mw7,mw25,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn1061,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw26]),(11,10,1,mn1062,[mw6,mw7,mw27,mw2,mw3,mw4,mw20,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS43p : mcS43.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS44 : List MemoKey := [(11,10,1,mn1063,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw28]),(11,10,1,mn1064,[mw6,mw7,mw29,mw2,mw3,mw4,mw20,mw5]),(11,10,1,mn1065,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw30]),(11,10,1,mn1066,[mw6,mw7,mw2,mw31,mw3,mw4,mw20,mw5]),(11,10,1,mn1067,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw32]),(11,10,1,mn1068,[mw6,mw7,mw2,mw33,mw3,mw4,mw20,mw5]),(11,10,1,mn1069,[mw6,mw7,mw2,mw3,mw4,mw20,mw5,mw34]),(11,10,1,mn1070,[mw6,mw7,mw2,mw3,mw35,mw4,mw20,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS44p : mcS44.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS45 : List MemoKey := [(11,10,1,mn1087,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn1088,[mw6,mw21,mw23,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn1089,[mw6,mw21,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn1090,[mw6,mw21,mw7,mw25,mw2,mw3,mw4,mw5]),(11,10,1,mn1091,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn1092,[mw6,mw21,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn1093,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn1094,[mw6,mw21,mw7,mw29,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS45p : mcS45.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS46 : List MemoKey := [(11,10,1,mn1095,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn1096,[mw6,mw21,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn1097,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn1098,[mw6,mw21,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn1099,[mw6,mw21,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn1100,[mw6,mw21,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn1117,[mw6,mw23,mw2,mw3,mw4,mw22]),(11,10,1,mn1118,[mw6,mw23,mw7,mw2,mw3,mw4,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS46p : mcS46.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS47 : List MemoKey := [(11,10,1,mn1119,[mw6,mw23,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn1120,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn1121,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw22]),(11,10,1,mn1122,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn1123,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw26]),(11,10,1,mn1124,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw22]),(11,10,1,mn1125,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw28]),(11,10,1,mn1126,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw22])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS47p : mcS47.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS48 : List MemoKey := [(11,10,1,mn1127,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw30]),(11,10,1,mn1128,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw22]),(11,10,1,mn1129,[mw6,mw7,mw2,mw3,mw4,mw5,mw22,mw32]),(11,10,1,mn1130,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw22]),(11,10,1,mn1131,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw22]),(11,10,1,mn1132,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw22]),(11,10,1,mn1149,[mw6,mw23,mw7,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn1150,[mw6,mw23,mw7,mw25,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS48p : mcS48.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS49 : List MemoKey := [(11,10,1,mn1151,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn1152,[mw6,mw23,mw7,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn1153,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn1154,[mw6,mw23,mw7,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn1155,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn1156,[mw6,mw23,mw7,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn1157,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn1158,[mw6,mw23,mw7,mw2,mw33,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS49p : mcS49.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS50 : List MemoKey := [(11,10,1,mn1159,[mw6,mw23,mw7,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn1160,[mw6,mw23,mw7,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn1177,[mw6,mw7,mw25,mw4,mw24,mw5]),(11,10,1,mn1178,[mw6,mw7,mw25,mw2,mw4,mw24,mw5]),(11,10,1,mn1179,[mw6,mw7,mw25,mw3,mw4,mw24,mw5]),(11,10,1,mn1180,[mw6,mw7,mw25,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn1181,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw26]),(11,10,1,mn1182,[mw6,mw7,mw27,mw2,mw3,mw4,mw24,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS50p : mcS50.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS51 : List MemoKey := [(11,10,1,mn1183,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw28]),(11,10,1,mn1184,[mw6,mw7,mw29,mw2,mw3,mw4,mw24,mw5]),(11,10,1,mn1185,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw30]),(11,10,1,mn1186,[mw6,mw7,mw2,mw31,mw3,mw4,mw24,mw5]),(11,10,1,mn1187,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw32]),(11,10,1,mn1188,[mw6,mw7,mw2,mw33,mw3,mw4,mw24,mw5]),(11,10,1,mn1189,[mw6,mw7,mw2,mw3,mw4,mw24,mw5,mw34]),(11,10,1,mn1190,[mw6,mw7,mw2,mw3,mw35,mw4,mw24,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS51p : mcS51.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS52 : List MemoKey := [(11,10,1,mn1207,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn1208,[mw6,mw7,mw25,mw27,mw2,mw3,mw4,mw5]),(11,10,1,mn1209,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn1210,[mw6,mw7,mw25,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn1211,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn1212,[mw6,mw7,mw25,mw2,mw31,mw4,mw5]),(11,10,1,mn1213,[mw6,mw7,mw25,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn1214,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS52p : mcS52.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS53 : List MemoKey := [(11,10,1,mn1215,[mw6,mw7,mw25,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn1216,[mw6,mw7,mw25,mw2,mw3,mw4,mw5,mw34]),(11,10,1,mn1217,[mw6,mw7,mw25,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn1236,[mw6,mw7,mw27,mw3,mw5,mw26]),(11,10,1,mn1237,[mw6,mw7,mw27,mw2,mw3,mw5,mw26]),(11,10,1,mn1238,[mw6,mw7,mw27,mw3,mw4,mw5,mw26]),(11,10,1,mn1239,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn1240,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS53p : mcS53.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS54 : List MemoKey := [(11,10,1,mn1241,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw26]),(11,10,1,mn1242,[mw6,mw7,mw2,mw3,mw5,mw26,mw30]),(11,10,1,mn1243,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw30]),(11,10,1,mn1244,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw26]),(11,10,1,mn1245,[mw6,mw7,mw2,mw3,mw4,mw5,mw26,mw32]),(11,10,1,mn1246,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw26]),(11,10,1,mn1247,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw26]),(11,10,1,mn1248,[mw6,mw7,mw2,mw3,mw35,mw5,mw26])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS54p : mcS54.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS55 : List MemoKey := [(11,10,1,mn1249,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw26]),(11,10,1,mn1268,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn1269,[mw6,mw7,mw27,mw29,mw2,mw3,mw4,mw5]),(11,10,1,mn1270,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn1271,[mw6,mw7,mw27,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn1272,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn1273,[mw6,mw7,mw27,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn1274,[mw6,mw7,mw27,mw2,mw3,mw4,mw5,mw34])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS55p : mcS55.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS56 : List MemoKey := [(11,10,1,mn1275,[mw6,mw7,mw27,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn1292,[mw6,mw7,mw29,mw3,mw4,mw28]),(11,10,1,mn1293,[mw6,mw7,mw29,mw2,mw3,mw4,mw28]),(11,10,1,mn1294,[mw6,mw7,mw29,mw3,mw4,mw5,mw28]),(11,10,1,mn1295,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw28]),(11,10,1,mn1296,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw30]),(11,10,1,mn1297,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw28]),(11,10,1,mn1298,[mw6,mw7,mw2,mw3,mw4,mw5,mw28,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS56p : mcS56.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS57 : List MemoKey := [(11,10,1,mn1299,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw28]),(11,10,1,mn1300,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw28]),(11,10,1,mn1301,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw28]),(11,10,1,mn1318,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw30]),(11,10,1,mn1319,[mw6,mw7,mw29,mw2,mw31,mw3,mw4,mw5]),(11,10,1,mn1320,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn1321,[mw6,mw7,mw29,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn1322,[mw6,mw7,mw29,mw2,mw3,mw4,mw5,mw34])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS57p : mcS57.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS58 : List MemoKey := [(11,10,1,mn1323,[mw6,mw7,mw29,mw2,mw3,mw35,mw4,mw5]),(11,10,1,mn1340,[mw6,mw7,mw2,mw31,mw5,mw30]),(11,10,1,mn1341,[mw6,mw7,mw2,mw31,mw3,mw5,mw30]),(11,10,1,mn1342,[mw6,mw7,mw2,mw31,mw4,mw5,mw30]),(11,10,1,mn1343,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw30]),(11,10,1,mn1344,[mw6,mw7,mw2,mw3,mw4,mw5,mw30,mw32]),(11,10,1,mn1345,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw30]),(11,10,1,mn1346,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw30])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS58p : mcS58.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS59 : List MemoKey := [(11,10,1,mn1347,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw30]),(11,10,1,mn1364,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw32]),(11,10,1,mn1365,[mw6,mw7,mw2,mw31,mw33,mw3,mw4,mw5]),(11,10,1,mn1366,[mw6,mw7,mw2,mw31,mw3,mw4,mw5,mw34]),(11,10,1,mn1367,[mw6,mw7,mw2,mw31,mw3,mw35,mw4,mw5]),(11,10,1,mn1384,[mw6,mw7,mw2,mw33,mw4,mw32]),(11,10,1,mn1385,[mw6,mw7,mw2,mw33,mw3,mw4,mw32]),(11,10,1,mn1386,[mw6,mw7,mw2,mw33,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS59p : mcS59.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS60 : List MemoKey := [(11,10,1,mn1387,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw32]),(11,10,1,mn1388,[mw6,mw7,mw2,mw3,mw4,mw5,mw34,mw32]),(11,10,1,mn1389,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw32]),(11,10,1,mn1406,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw34]),(11,10,1,mn1407,[mw6,mw7,mw2,mw33,mw3,mw35,mw4,mw5]),(11,10,1,mn1424,[mw6,mw7,mw2,mw3,mw35,mw34]),(11,10,1,mn1425,[mw6,mw7,mw2,mw3,mw35,mw4,mw34]),(11,10,1,mn1426,[mw6,mw7,mw2,mw3,mw35,mw5,mw34])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS60p : mcS60.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS61 : List MemoKey := [(11,10,1,mn1427,[mw6,mw7,mw2,mw3,mw35,mw4,mw5,mw34])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS61p : mcS61.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def memoChunksS : List {xs : List MemoKey // xs.all (fun e => !(keyRun originalS e)) = true} := [⟨mcS0,mcS0p⟩,⟨mcS1,mcS1p⟩,⟨mcS2,mcS2p⟩,⟨mcS3,mcS3p⟩,⟨mcS4,mcS4p⟩,⟨mcS5,mcS5p⟩,⟨mcS6,mcS6p⟩,⟨mcS7,mcS7p⟩,⟨mcS8,mcS8p⟩,⟨mcS9,mcS9p⟩,⟨mcS10,mcS10p⟩,⟨mcS11,mcS11p⟩,⟨mcS12,mcS12p⟩,⟨mcS13,mcS13p⟩,⟨mcS14,mcS14p⟩,⟨mcS15,mcS15p⟩,⟨mcS16,mcS16p⟩,⟨mcS17,mcS17p⟩,⟨mcS18,mcS18p⟩,⟨mcS19,mcS19p⟩,⟨mcS20,mcS20p⟩,⟨mcS21,mcS21p⟩,⟨mcS22,mcS22p⟩,⟨mcS23,mcS23p⟩,⟨mcS24,mcS24p⟩,⟨mcS25,mcS25p⟩,⟨mcS26,mcS26p⟩,⟨mcS27,mcS27p⟩,⟨mcS28,mcS28p⟩,⟨mcS29,mcS29p⟩,⟨mcS30,mcS30p⟩,⟨mcS31,mcS31p⟩,⟨mcS32,mcS32p⟩,⟨mcS33,mcS33p⟩,⟨mcS34,mcS34p⟩,⟨mcS35,mcS35p⟩,⟨mcS36,mcS36p⟩,⟨mcS37,mcS37p⟩,⟨mcS38,mcS38p⟩,⟨mcS39,mcS39p⟩,⟨mcS40,mcS40p⟩,⟨mcS41,mcS41p⟩,⟨mcS42,mcS42p⟩,⟨mcS43,mcS43p⟩,⟨mcS44,mcS44p⟩,⟨mcS45,mcS45p⟩,⟨mcS46,mcS46p⟩,⟨mcS47,mcS47p⟩,⟨mcS48,mcS48p⟩,⟨mcS49,mcS49p⟩,⟨mcS50,mcS50p⟩,⟨mcS51,mcS51p⟩,⟨mcS52,mcS52p⟩,⟨mcS53,mcS53p⟩,⟨mcS54,mcS54p⟩,⟨mcS55,mcS55p⟩,⟨mcS56,mcS56p⟩,⟨mcS57,mcS57p⟩,⟨mcS58,mcS58p⟩,⟨mcS59,mcS59p⟩,⟨mcS60,mcS60p⟩,⟨mcS61,mcS61p⟩]
def memoKeysS : List MemoKey := (memoChunksS.map Subtype.val).flatten
lemma memoKeysS_sound : ∀ e ∈ memoKeysS, keyRun originalS e = false := checkedChunks_sound (keyRun originalS) memoChunksS
end memo_data

noncomputable section memo_bridge
def memoTop (keysC keysS : List MemoKey) (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (memoLookC NN AA HX HY l m g keysC K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (memoLookS NN AA HX HY l m g K keysC keysS K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def memoStart (keysC keysS : List MemoKey) (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => memoTop keysC keysS NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def memoChk (keysC keysS : List MemoKey) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => memoStart keysC keysS nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma memoTop_eq (keysC keysS : List MemoKey) (NN AA HX HY l m g K H ph k t z : Nat) (v : List W)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoTop keysC keysS NN AA HX HY l m g K H ph k t z v = topCC NN AA HX HY l m g K H ph k t z v := by
  unfold memoTop topCC
  rw [memoLookC_eq NN AA HX HY l m g keysC hC, memoLookS_eq NN AA HX HY l m g K keysC keysS hC hS]
lemma memoStart_eq (keysC keysS : List MemoKey) (NN AA HX HY l m g B K t p H ph : Nat) (v : List W)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoStart keysC keysS NN AA HX HY l m g B K t p H ph v = startvC NN AA HX HY l m g B K t p H ph v := by
  simp only [memoStart,startvC,memoTop_eq keysC keysS NN AA HX HY l m g K _ _ _ _ _ _ hC hS]
lemma memoChk_eq (H ph : Nat) :
    memoChk memoKeysC memoKeysS [] rt 0 12 1 H ph = chk [] rt 0 12 1 H ph := by
  unfold memoChk chk
  simp only [st_eq]
  simp only [memoStart_eq memoKeysC memoKeysS I.NN I.AA I.HX I.HY (lz 0) (mz 0)
    (pL (rt.map (fun _ => 16))) _ 12 _ _ _ _ _ memoKeysC_sound memoKeysS_sound]
end memo_bridge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_p : pOk 0 rt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_0 : chk [] rt 0 11 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_1 : chk [] rt 0 11 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_2 : chk [] rt 0 11 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_3 : chk [] rt 0 11 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_4 : chk [] rt 0 11 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_5 : chk [] rt 0 11 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_6 : chk [] rt 0 11 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_7 : chk [] rt 0 11 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_8 : chk [] rt 0 11 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_9 : chk [] rt 0 11 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_10 : chk [] rt 0 11 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_11 : chk [] rt 0 11 11 FF 1 = false := by decide +kernel
lemma iroot : Imp [] 0 12 := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by
  interval_cases t
  · exact one root_0
  · exact one root_1
  · exact one root_2
  · exact one root_3
  · exact one root_4
  · exact one root_5
  · exact one root_6
  · exact one root_7
  · exact one root_8
  · exact one root_9
  · exact one root_10
  · exact one root_11)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_0 : chk [] rt 0 12 1 (0) 1 = false := (memoChk_eq (0) 1).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_1 : chk [] rt 0 12 1 (memoCell 4 0) 0 = false := (memoChk_eq (memoCell 4 0) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_2 : chk [] rt 0 12 1 (memoCell 4 4) 0 = false := (memoChk_eq (memoCell 4 4) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_3 : chk [] rt 0 12 1 (memoCell 4 8) 0 = false := (memoChk_eq (memoCell 4 8) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_4 : chk [] rt 0 12 1 (memoCell 4 12) 0 = false := (memoChk_eq (memoCell 4 12) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_5 : chk [] rt 0 12 1 (memoCell 4 16) 0 = false := (memoChk_eq (memoCell 4 16) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_6 : chk [] rt 0 12 1 (memoCell 4 20) 0 = false := (memoChk_eq (memoCell 4 20) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_7 : chk [] rt 0 12 1 (memoCell 4 24) 0 = false := (memoChk_eq (memoCell 4 24) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_8 : chk [] rt 0 12 1 (memoCell 4 28) 0 = false := (memoChk_eq (memoCell 4 28) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_9 : chk [] rt 0 12 1 (memoCell 4 32) 0 = false := (memoChk_eq (memoCell 4 32) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_10 : chk [] rt 0 12 1 (memoCell 4 36) 0 = false := (memoChk_eq (memoCell 4 36) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_11 : chk [] rt 0 12 1 (memoCell 4 40) 0 = false := (memoChk_eq (memoCell 4 40) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_12 : chk [] rt 0 12 1 (memoCell 4 44) 0 = false := (memoChk_eq (memoCell 4 44) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_13 : chk [] rt 0 12 1 (memoCell 4 48) 0 = false := (memoChk_eq (memoCell 4 48) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_14 : chk [] rt 0 12 1 (memoCell 4 52) 0 = false := (memoChk_eq (memoCell 4 52) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_15 : chk [] rt 0 12 1 (memoCell 4 56) 0 = false := (memoChk_eq (memoCell 4 56) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_16 : chk [] rt 0 12 1 (memoCell 4 60) 0 = false := (memoChk_eq (memoCell 4 60) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_17 : chk [] rt 0 12 1 (memoCell 4 64) 0 = false := (memoChk_eq (memoCell 4 64) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_18 : chk [] rt 0 12 1 (memoCell 4 68) 0 = false := (memoChk_eq (memoCell 4 68) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_19 : chk [] rt 0 12 1 (memoCell 4 72) 0 = false := (memoChk_eq (memoCell 4 72) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_20 : chk [] rt 0 12 1 (memoCell 4 76) 0 = false := (memoChk_eq (memoCell 4 76) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_21 : chk [] rt 0 12 1 (memoCell 4 80) 0 = false := (memoChk_eq (memoCell 4 80) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_22 : chk [] rt 0 12 1 (memoCell 4 84) 0 = false := (memoChk_eq (memoCell 4 84) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_23 : chk [] rt 0 12 1 (memoCell 4 88) 0 = false := (memoChk_eq (memoCell 4 88) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_24 : chk [] rt 0 12 1 (memoCell 4 92) 0 = false := (memoChk_eq (memoCell 4 92) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_25 : chk [] rt 0 12 1 (memoCell 4 96) 0 = false := (memoChk_eq (memoCell 4 96) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_26 : chk [] rt 0 12 1 (memoCell 4 100) 0 = false := (memoChk_eq (memoCell 4 100) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_27 : chk [] rt 0 12 1 (memoCell 4 104) 0 = false := (memoChk_eq (memoCell 4 104) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_28 : chk [] rt 0 12 1 (memoCell 4 108) 0 = false := (memoChk_eq (memoCell 4 108) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_29 : chk [] rt 0 12 1 (memoCell 4 112) 0 = false := (memoChk_eq (memoCell 4 112) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_30 : chk [] rt 0 12 1 (memoCell 4 116) 0 = false := (memoChk_eq (memoCell 4 116) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_31 : chk [] rt 0 12 1 (memoCell 4 120) 0 = false := (memoChk_eq (memoCell 4 120) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_32 : chk [] rt 0 12 1 (memoCell 4 124) 0 = false := (memoChk_eq (memoCell 4 124) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_33 : chk [] rt 0 12 1 (memoCell 4 128) 0 = false := (memoChk_eq (memoCell 4 128) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_34 : chk [] rt 0 12 1 (memoCell 4 132) 0 = false := (memoChk_eq (memoCell 4 132) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_35 : chk [] rt 0 12 1 (memoCell 4 136) 0 = false := (memoChk_eq (memoCell 4 136) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_36 : chk [] rt 0 12 1 (memoCell 4 140) 0 = false := (memoChk_eq (memoCell 4 140) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_37 : chk [] rt 0 12 1 (memoCell 4 144) 0 = false := (memoChk_eq (memoCell 4 144) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_38 : chk [] rt 0 12 1 (memoCell 4 148) 0 = false := (memoChk_eq (memoCell 4 148) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_39 : chk [] rt 0 12 1 (memoCell 4 152) 0 = false := (memoChk_eq (memoCell 4 152) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_40 : chk [] rt 0 12 1 (memoCell 4 156) 0 = false := (memoChk_eq (memoCell 4 156) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_41 : chk [] rt 0 12 1 (memoCell 4 160) 0 = false := (memoChk_eq (memoCell 4 160) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_42 : chk [] rt 0 12 1 (memoCell 4 164) 0 = false := (memoChk_eq (memoCell 4 164) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_43 : chk [] rt 0 12 1 (memoCell 4 168) 0 = false := (memoChk_eq (memoCell 4 168) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_44 : chk [] rt 0 12 1 (memoCell 4 172) 0 = false := (memoChk_eq (memoCell 4 172) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_45 : chk [] rt 0 12 1 (memoCell 4 176) 0 = false := (memoChk_eq (memoCell 4 176) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_46 : chk [] rt 0 12 1 (memoCell 4 180) 0 = false := (memoChk_eq (memoCell 4 180) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_47 : chk [] rt 0 12 1 (memoCell 4 184) 0 = false := (memoChk_eq (memoCell 4 184) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_48 : chk [] rt 0 12 1 (memoCell 4 188) 0 = false := (memoChk_eq (memoCell 4 188) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_49 : chk [] rt 0 12 1 (memoCell 4 192) 0 = false := (memoChk_eq (memoCell 4 192) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_50 : chk [] rt 0 12 1 (memoCell 4 196) 0 = false := (memoChk_eq (memoCell 4 196) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_51 : chk [] rt 0 12 1 (memoCell 4 200) 0 = false := (memoChk_eq (memoCell 4 200) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_52 : chk [] rt 0 12 1 (memoCell 4 204) 0 = false := (memoChk_eq (memoCell 4 204) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_53 : chk [] rt 0 12 1 (memoCell 4 208) 0 = false := (memoChk_eq (memoCell 4 208) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_54 : chk [] rt 0 12 1 (memoCell 4 212) 0 = false := (memoChk_eq (memoCell 4 212) 0).symm.trans (by decide +kernel)
def cacheR1Checked : List {p : ℕ × ℕ // chk [] rt 0 12 1 p.1 p.2 = false} := [⟨((0), 1), cacheR1Proof_0⟩, ⟨((memoCell 4 0), 0), cacheR1Proof_1⟩, ⟨((memoCell 4 4), 0), cacheR1Proof_2⟩, ⟨((memoCell 4 8), 0), cacheR1Proof_3⟩, ⟨((memoCell 4 12), 0), cacheR1Proof_4⟩, ⟨((memoCell 4 16), 0), cacheR1Proof_5⟩, ⟨((memoCell 4 20), 0), cacheR1Proof_6⟩, ⟨((memoCell 4 24), 0), cacheR1Proof_7⟩, ⟨((memoCell 4 28), 0), cacheR1Proof_8⟩, ⟨((memoCell 4 32), 0), cacheR1Proof_9⟩, ⟨((memoCell 4 36), 0), cacheR1Proof_10⟩, ⟨((memoCell 4 40), 0), cacheR1Proof_11⟩, ⟨((memoCell 4 44), 0), cacheR1Proof_12⟩, ⟨((memoCell 4 48), 0), cacheR1Proof_13⟩, ⟨((memoCell 4 52), 0), cacheR1Proof_14⟩, ⟨((memoCell 4 56), 0), cacheR1Proof_15⟩, ⟨((memoCell 4 60), 0), cacheR1Proof_16⟩, ⟨((memoCell 4 64), 0), cacheR1Proof_17⟩, ⟨((memoCell 4 68), 0), cacheR1Proof_18⟩, ⟨((memoCell 4 72), 0), cacheR1Proof_19⟩, ⟨((memoCell 4 76), 0), cacheR1Proof_20⟩, ⟨((memoCell 4 80), 0), cacheR1Proof_21⟩, ⟨((memoCell 4 84), 0), cacheR1Proof_22⟩, ⟨((memoCell 4 88), 0), cacheR1Proof_23⟩, ⟨((memoCell 4 92), 0), cacheR1Proof_24⟩, ⟨((memoCell 4 96), 0), cacheR1Proof_25⟩, ⟨((memoCell 4 100), 0), cacheR1Proof_26⟩, ⟨((memoCell 4 104), 0), cacheR1Proof_27⟩, ⟨((memoCell 4 108), 0), cacheR1Proof_28⟩, ⟨((memoCell 4 112), 0), cacheR1Proof_29⟩, ⟨((memoCell 4 116), 0), cacheR1Proof_30⟩, ⟨((memoCell 4 120), 0), cacheR1Proof_31⟩, ⟨((memoCell 4 124), 0), cacheR1Proof_32⟩, ⟨((memoCell 4 128), 0), cacheR1Proof_33⟩, ⟨((memoCell 4 132), 0), cacheR1Proof_34⟩, ⟨((memoCell 4 136), 0), cacheR1Proof_35⟩, ⟨((memoCell 4 140), 0), cacheR1Proof_36⟩, ⟨((memoCell 4 144), 0), cacheR1Proof_37⟩, ⟨((memoCell 4 148), 0), cacheR1Proof_38⟩, ⟨((memoCell 4 152), 0), cacheR1Proof_39⟩, ⟨((memoCell 4 156), 0), cacheR1Proof_40⟩, ⟨((memoCell 4 160), 0), cacheR1Proof_41⟩, ⟨((memoCell 4 164), 0), cacheR1Proof_42⟩, ⟨((memoCell 4 168), 0), cacheR1Proof_43⟩, ⟨((memoCell 4 172), 0), cacheR1Proof_44⟩, ⟨((memoCell 4 176), 0), cacheR1Proof_45⟩, ⟨((memoCell 4 180), 0), cacheR1Proof_46⟩, ⟨((memoCell 4 184), 0), cacheR1Proof_47⟩, ⟨((memoCell 4 188), 0), cacheR1Proof_48⟩, ⟨((memoCell 4 192), 0), cacheR1Proof_49⟩, ⟨((memoCell 4 196), 0), cacheR1Proof_50⟩, ⟨((memoCell 4 200), 0), cacheR1Proof_51⟩, ⟨((memoCell 4 204), 0), cacheR1Proof_52⟩, ⟨((memoCell 4 208), 0), cacheR1Proof_53⟩, ⟨((memoCell 4 212), 0), cacheR1Proof_54⟩]
def cacheR1Parts : List (ℕ × ℕ) := cacheR1Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Full : mFull cacheR1Parts = true := by decide +kernel
def cacheR1One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 1 p.1 p.2 = false := by
  refine ⟨cacheR1Parts, cacheR1Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_0 : chk [] rt 0 12 2 (0) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_1 : chk [] rt 0 12 2 (memoCell 4 0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_2 : chk [] rt 0 12 2 (memoCell 4 4) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_3 : chk [] rt 0 12 2 (memoCell 4 8) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_4 : chk [] rt 0 12 2 (memoCell 4 12) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_5 : chk [] rt 0 12 2 (memoCell 4 16) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_6 : chk [] rt 0 12 2 (memoCell 4 20) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_7 : chk [] rt 0 12 2 (memoCell 4 24) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_8 : chk [] rt 0 12 2 (memoCell 4 28) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_9 : chk [] rt 0 12 2 (memoCell 4 32) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_10 : chk [] rt 0 12 2 (memoCell 4 36) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_11 : chk [] rt 0 12 2 (memoCell 4 40) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_12 : chk [] rt 0 12 2 (memoCell 4 44) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_13 : chk [] rt 0 12 2 (memoCell 4 48) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_14 : chk [] rt 0 12 2 (memoCell 4 52) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_15 : chk [] rt 0 12 2 (memoCell 4 56) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_16 : chk [] rt 0 12 2 (memoCell 4 60) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_17 : chk [] rt 0 12 2 (memoCell 4 64) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_18 : chk [] rt 0 12 2 (memoCell 4 68) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_19 : chk [] rt 0 12 2 (memoCell 4 72) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_20 : chk [] rt 0 12 2 (memoCell 4 76) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_21 : chk [] rt 0 12 2 (memoCell 4 80) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_22 : chk [] rt 0 12 2 (memoCell 4 84) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_23 : chk [] rt 0 12 2 (memoCell 4 88) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_24 : chk [] rt 0 12 2 (memoCell 4 92) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_25 : chk [] rt 0 12 2 (memoCell 4 96) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_26 : chk [] rt 0 12 2 (memoCell 4 100) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_27 : chk [] rt 0 12 2 (memoCell 4 104) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_28 : chk [] rt 0 12 2 (memoCell 4 108) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_29 : chk [] rt 0 12 2 (memoCell 4 112) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_30 : chk [] rt 0 12 2 (memoCell 4 116) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_31 : chk [] rt 0 12 2 (memoCell 4 120) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_32 : chk [] rt 0 12 2 (memoCell 4 124) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_33 : chk [] rt 0 12 2 (memoCell 4 128) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_34 : chk [] rt 0 12 2 (memoCell 4 132) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_35 : chk [] rt 0 12 2 (memoCell 4 136) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_36 : chk [] rt 0 12 2 (memoCell 4 140) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_37 : chk [] rt 0 12 2 (memoCell 4 144) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_38 : chk [] rt 0 12 2 (memoCell 4 148) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_39 : chk [] rt 0 12 2 (memoCell 4 152) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_40 : chk [] rt 0 12 2 (memoCell 4 156) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_41 : chk [] rt 0 12 2 (memoCell 4 160) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_42 : chk [] rt 0 12 2 (memoCell 4 164) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_43 : chk [] rt 0 12 2 (memoCell 4 168) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_44 : chk [] rt 0 12 2 (memoCell 4 172) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_45 : chk [] rt 0 12 2 (memoCell 4 176) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_46 : chk [] rt 0 12 2 (memoCell 4 180) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_47 : chk [] rt 0 12 2 (memoCell 4 184) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_48 : chk [] rt 0 12 2 (memoCell 4 188) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_49 : chk [] rt 0 12 2 (memoCell 4 192) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_50 : chk [] rt 0 12 2 (memoCell 4 196) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_51 : chk [] rt 0 12 2 (memoCell 4 200) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_52 : chk [] rt 0 12 2 (memoCell 4 204) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_53 : chk [] rt 0 12 2 (memoCell 4 208) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_54 : chk [] rt 0 12 2 (memoCell 4 212) 0 = false := by decide +kernel
def cacheR2Checked : List {p : ℕ × ℕ // chk [] rt 0 12 2 p.1 p.2 = false} := [⟨((0), 1), cacheR2Proof_0⟩, ⟨((memoCell 4 0), 0), cacheR2Proof_1⟩, ⟨((memoCell 4 4), 0), cacheR2Proof_2⟩, ⟨((memoCell 4 8), 0), cacheR2Proof_3⟩, ⟨((memoCell 4 12), 0), cacheR2Proof_4⟩, ⟨((memoCell 4 16), 0), cacheR2Proof_5⟩, ⟨((memoCell 4 20), 0), cacheR2Proof_6⟩, ⟨((memoCell 4 24), 0), cacheR2Proof_7⟩, ⟨((memoCell 4 28), 0), cacheR2Proof_8⟩, ⟨((memoCell 4 32), 0), cacheR2Proof_9⟩, ⟨((memoCell 4 36), 0), cacheR2Proof_10⟩, ⟨((memoCell 4 40), 0), cacheR2Proof_11⟩, ⟨((memoCell 4 44), 0), cacheR2Proof_12⟩, ⟨((memoCell 4 48), 0), cacheR2Proof_13⟩, ⟨((memoCell 4 52), 0), cacheR2Proof_14⟩, ⟨((memoCell 4 56), 0), cacheR2Proof_15⟩, ⟨((memoCell 4 60), 0), cacheR2Proof_16⟩, ⟨((memoCell 4 64), 0), cacheR2Proof_17⟩, ⟨((memoCell 4 68), 0), cacheR2Proof_18⟩, ⟨((memoCell 4 72), 0), cacheR2Proof_19⟩, ⟨((memoCell 4 76), 0), cacheR2Proof_20⟩, ⟨((memoCell 4 80), 0), cacheR2Proof_21⟩, ⟨((memoCell 4 84), 0), cacheR2Proof_22⟩, ⟨((memoCell 4 88), 0), cacheR2Proof_23⟩, ⟨((memoCell 4 92), 0), cacheR2Proof_24⟩, ⟨((memoCell 4 96), 0), cacheR2Proof_25⟩, ⟨((memoCell 4 100), 0), cacheR2Proof_26⟩, ⟨((memoCell 4 104), 0), cacheR2Proof_27⟩, ⟨((memoCell 4 108), 0), cacheR2Proof_28⟩, ⟨((memoCell 4 112), 0), cacheR2Proof_29⟩, ⟨((memoCell 4 116), 0), cacheR2Proof_30⟩, ⟨((memoCell 4 120), 0), cacheR2Proof_31⟩, ⟨((memoCell 4 124), 0), cacheR2Proof_32⟩, ⟨((memoCell 4 128), 0), cacheR2Proof_33⟩, ⟨((memoCell 4 132), 0), cacheR2Proof_34⟩, ⟨((memoCell 4 136), 0), cacheR2Proof_35⟩, ⟨((memoCell 4 140), 0), cacheR2Proof_36⟩, ⟨((memoCell 4 144), 0), cacheR2Proof_37⟩, ⟨((memoCell 4 148), 0), cacheR2Proof_38⟩, ⟨((memoCell 4 152), 0), cacheR2Proof_39⟩, ⟨((memoCell 4 156), 0), cacheR2Proof_40⟩, ⟨((memoCell 4 160), 0), cacheR2Proof_41⟩, ⟨((memoCell 4 164), 0), cacheR2Proof_42⟩, ⟨((memoCell 4 168), 0), cacheR2Proof_43⟩, ⟨((memoCell 4 172), 0), cacheR2Proof_44⟩, ⟨((memoCell 4 176), 0), cacheR2Proof_45⟩, ⟨((memoCell 4 180), 0), cacheR2Proof_46⟩, ⟨((memoCell 4 184), 0), cacheR2Proof_47⟩, ⟨((memoCell 4 188), 0), cacheR2Proof_48⟩, ⟨((memoCell 4 192), 0), cacheR2Proof_49⟩, ⟨((memoCell 4 196), 0), cacheR2Proof_50⟩, ⟨((memoCell 4 200), 0), cacheR2Proof_51⟩, ⟨((memoCell 4 204), 0), cacheR2Proof_52⟩, ⟨((memoCell 4 208), 0), cacheR2Proof_53⟩, ⟨((memoCell 4 212), 0), cacheR2Proof_54⟩]
def cacheR2Parts : List (ℕ × ℕ) := cacheR2Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Full : mFull cacheR2Parts = true := by decide +kernel
def cacheR2One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 2 p.1 p.2 = false := by
  refine ⟨cacheR2Parts, cacheR2Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_0 : chk [] rt 0 12 3 (0) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_1 : chk [] rt 0 12 3 (memoCell 7 0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_2 : chk [] rt 0 12 3 (memoCell 7 7) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_3 : chk [] rt 0 12 3 (memoCell 7 14) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_4 : chk [] rt 0 12 3 (memoCell 7 21) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_5 : chk [] rt 0 12 3 (memoCell 7 28) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_6 : chk [] rt 0 12 3 (memoCell 7 35) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_7 : chk [] rt 0 12 3 (memoCell 7 42) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_8 : chk [] rt 0 12 3 (memoCell 7 49) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_9 : chk [] rt 0 12 3 (memoCell 7 56) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_10 : chk [] rt 0 12 3 (memoCell 7 63) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_11 : chk [] rt 0 12 3 (memoCell 7 70) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_12 : chk [] rt 0 12 3 (memoCell 7 77) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_13 : chk [] rt 0 12 3 (memoCell 7 84) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_14 : chk [] rt 0 12 3 (memoCell 7 91) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_15 : chk [] rt 0 12 3 (memoCell 7 98) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_16 : chk [] rt 0 12 3 (memoCell 7 105) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_17 : chk [] rt 0 12 3 (memoCell 7 112) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_18 : chk [] rt 0 12 3 (memoCell 7 119) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_19 : chk [] rt 0 12 3 (memoCell 7 126) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_20 : chk [] rt 0 12 3 (memoCell 7 133) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_21 : chk [] rt 0 12 3 (memoCell 7 140) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_22 : chk [] rt 0 12 3 (memoCell 7 147) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_23 : chk [] rt 0 12 3 (memoCell 7 154) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_24 : chk [] rt 0 12 3 (memoCell 7 161) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_25 : chk [] rt 0 12 3 (memoCell 7 168) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_26 : chk [] rt 0 12 3 (memoCell 7 175) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_27 : chk [] rt 0 12 3 (memoCell 7 182) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_28 : chk [] rt 0 12 3 (memoCell 7 189) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_29 : chk [] rt 0 12 3 (memoCell 7 196) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_30 : chk [] rt 0 12 3 (memoCell 7 203) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_31 : chk [] rt 0 12 3 (memoCell 7 210) 0 = false := by decide +kernel
def cacheR3Checked : List {p : ℕ × ℕ // chk [] rt 0 12 3 p.1 p.2 = false} := [⟨((0), 1), cacheR3Proof_0⟩, ⟨((memoCell 7 0), 0), cacheR3Proof_1⟩, ⟨((memoCell 7 7), 0), cacheR3Proof_2⟩, ⟨((memoCell 7 14), 0), cacheR3Proof_3⟩, ⟨((memoCell 7 21), 0), cacheR3Proof_4⟩, ⟨((memoCell 7 28), 0), cacheR3Proof_5⟩, ⟨((memoCell 7 35), 0), cacheR3Proof_6⟩, ⟨((memoCell 7 42), 0), cacheR3Proof_7⟩, ⟨((memoCell 7 49), 0), cacheR3Proof_8⟩, ⟨((memoCell 7 56), 0), cacheR3Proof_9⟩, ⟨((memoCell 7 63), 0), cacheR3Proof_10⟩, ⟨((memoCell 7 70), 0), cacheR3Proof_11⟩, ⟨((memoCell 7 77), 0), cacheR3Proof_12⟩, ⟨((memoCell 7 84), 0), cacheR3Proof_13⟩, ⟨((memoCell 7 91), 0), cacheR3Proof_14⟩, ⟨((memoCell 7 98), 0), cacheR3Proof_15⟩, ⟨((memoCell 7 105), 0), cacheR3Proof_16⟩, ⟨((memoCell 7 112), 0), cacheR3Proof_17⟩, ⟨((memoCell 7 119), 0), cacheR3Proof_18⟩, ⟨((memoCell 7 126), 0), cacheR3Proof_19⟩, ⟨((memoCell 7 133), 0), cacheR3Proof_20⟩, ⟨((memoCell 7 140), 0), cacheR3Proof_21⟩, ⟨((memoCell 7 147), 0), cacheR3Proof_22⟩, ⟨((memoCell 7 154), 0), cacheR3Proof_23⟩, ⟨((memoCell 7 161), 0), cacheR3Proof_24⟩, ⟨((memoCell 7 168), 0), cacheR3Proof_25⟩, ⟨((memoCell 7 175), 0), cacheR3Proof_26⟩, ⟨((memoCell 7 182), 0), cacheR3Proof_27⟩, ⟨((memoCell 7 189), 0), cacheR3Proof_28⟩, ⟨((memoCell 7 196), 0), cacheR3Proof_29⟩, ⟨((memoCell 7 203), 0), cacheR3Proof_30⟩, ⟨((memoCell 7 210), 0), cacheR3Proof_31⟩]
def cacheR3Parts : List (ℕ × ℕ) := cacheR3Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Full : mFull cacheR3Parts = true := by decide +kernel
def cacheR3One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 3 p.1 p.2 = false := by
  refine ⟨cacheR3Parts, cacheR3Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_4 : chk [] rt 0 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_5 : chk [] rt 0 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_6 : chk [] rt 0 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_7 : chk [] rt 0 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_8 : chk [] rt 0 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_9 : chk [] rt 0 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_10 : chk [] rt 0 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_11 : chk [] rt 0 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_12 : chk [] rt 0 12 12 FF 1 = false := by decide +kernel
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 12 t S) : False := by
  have hmin : ∀ q < 12, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 12 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 13 := by have := hm0.size.2; omega
  have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 t p.1 p.2 = false := by
    interval_cases t
    · exact cacheR1One
    · exact cacheR2One
    · exact cacheR3One
    · exact one proot_4
    · exact one proot_5
    · exact one proot_6
    · exact one proot_7
    · exact one proot_8
    · exact one proot_9
    · exact one proot_10
    · exact one proot_11
    · exact one proot_12
  exact imp_of_live (L := 13) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr hM)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1 && x 3) || (x 0 && x 2 && x 4) || (x 1 && x 2 && x 4) || (x 1 && x 3 && x 4) || (x 2 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 1 && x 2 && x 5) || (x 0 && x 3 && x 5) || (x 1 && x 3 && x 5) || (x 0 && x 4 && x 5)
def EF : ℕ := (rawP0.getD 0 0 &&& rawP0.getD 1 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 2 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 3 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 3 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 4 0 &&& rawP0.getD 5 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 6 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 6 => (rawP0.getD v.val 0).testBit b) = rawP0.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len0]
  · intro i h1 h2
    have : i < rawP0.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 6 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
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
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
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
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot ⟨o, hout⟩
def onWit : List Gate := [⟨.or, [4, 5]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [7, 0]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [5, 1]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [16, 4]⟩, ⟨.or, [13, 17]⟩]
theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 6 → Bool, Circuit.eval ⟨onWit, 18⟩ (List.ofFn x) = f x := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem onTableCorrect : ∀ x : Fin 6 → Bool, f x = Nat.testBit (4276809440 * 2 ^ 32 + 4242573312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel
end inst_data
end PEqualNP.Outside.L_meta_44576_aux

open PEqualNP.Outside.L_meta_44576_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_44576 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4242573312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4242573312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨⟨gates, o⟩, hC, hsize, hcorrect⟩ := hs
  have hf : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x := fun x => (hcorrect x).trans (onTableCorrect x).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 13 ≤ gates.length := by
      by_contra hlt
      by_cases hsmall : gates.length < 12
      · exact iroot gates.length hsmall (bridge ⟨gates, o⟩ hC hf)
      · have heq : gates.length = 12 := by omega
        rcases bridge_not gates o hC hnot hf with hs | ⟨t, ht, S0, hS, hl⟩
        · exact iroot (gates.length - 1) (by omega) hs
        · rw [heq] at hl
          exact iroot_pos ht hS hl
    refine ⟨⟨onWit, 18⟩, ?_, ?_, fun x => (onWitCorrect x).trans (onTableCorrect x)⟩
    · intro g hg
      obtain ⟨ho, hl⟩ := onWitBasis g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
    · have hw : (⟨onWit, 18⟩ : Circuit).size = 13 := rfl
      change gates.length ≤ s at hsize
      omega
  · refine ⟨⟨gates, o⟩, ?_, hsize, hcorrect⟩
    intro g hg
    obtain ⟨ho, hl⟩ := hC g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim
