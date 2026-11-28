import PEqualNP.Defs

/- The decision procedure and its soundness proof are adapted from the project proofs
L-meta-32910 and L-meta-1673, with new instance data and checked circuit bounds. -/

namespace PEqualNP.Outside.L_meta_35240_aux

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
def guardedCoverage (nn : ℕ) (enabled d : Bool) (l : ℕ) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC nn d l v) l)) enabled
def lookCore (NN AA HX HY : Nat) (l m g : Nat) (enabled : Bool) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (guardedCoverage NN enabled (pos t) l v (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y))) true (Nat.ble v.length 1)) fuel
-- Check coverage at each step of the fourteen-gate search.
abbrev lookC (NN AA HX HY : Nat) (l m g fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  lookCore NN AA HX HY l m g (Nat.beq fuel 14) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end coreC

def bigNat_0 : Nat := 0x7fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfff0000000000000000
def bigNat_1 : Nat := 0x1529549554000aaa000550002a8001400080012924a92a4925528001248001254924aa5000240009249240009240000000000000000000
def bigNat_2 : Nat := 0x800010200008000210000420000842400010800021088000210000421200008422000084221220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0xffff81ffff03c00000000000000000000ffff81e000000001ffff03c1e1c00001008200030a044189000c49106288314062c0040024430c0210c24c30c280080400421850861604161862424862600000000000000000208a04044501114283e28107a503c0082a101054211010542432e81e004130844255b03c1e1c08a0100860000000440000000011000080007ffe00c006c430c0210000c300000280c05420001bfff0c36180006dbfff05095e78da63bb83
def bigNat_4 : Nat := 0x7fffc0000001ffff7800000007fffc0f000000000000001ffff03c1ffff7801ec00002000900885460002a322152940a98854e0a9802184600004a2c1494d814980802184582a318a8c208248a8e618a9400000000000000000410408088242f0800421050ba2780010442429c80f0020284040304244a4e03c0294e7801ec01042000b008800000000022000140000bfff00000618460000da2c0000d80000180618458000180006186dbfff6180008333acbef42c83ce
def bigNat_5 : Nat := 0x7fffc0ffffbc01ffff7801ffff7bdc00000000000000001e45001b2800e95007c003c007800000010120280007449007c40900904a00f8003c6c06c006c6c0074000000000000000008230101118042604084c081038084821904042a042224bb0049763c0052ea780031ea7bdc00023000020000000045000028000157ffe00000000100050103602800000db7ffec0b01b05afffc00006c06c00006c00002bbde9588e747baf
def bigNat_6 : Nat := 0x3fffe07fffde007fffde00000001ffff7bdc000000000000000000008a00d45000722a03b0001d000e801d04009001080028401d80001d0da001b50006a001a869a0001c84901d800000000000000001044220222108484810909020c1109246e2048dc5e0028d35e10848040634b7bdc420300402044420008008a00005000002afffc0000000000000c01b00158002ad7ffe000000da001b500000000006db0000006dbfffc2fe323dd067eef3
def bigNat_7 : Nat := 0x1ffff000000ffffbc00000003fffef000000007fffdeffffbdec0000000000000000000000812000a00a9855455c002ac0015600ab01560d4c00015b690002960002960d2b4c000054c015304d34915700015600000000000000000208044143c2108080a1e13c4102200284e4f1010804030939e61273dec800c0080800c0800440804816000a00000555fff8000000000000000000d6c00015b6d8000000000000dab6c0000000000006db6dbfff000000731fc533d12e69c4
def bigNat_8 : Nat := 0x1ffff7fffde00000000000003fffef7fffdef7000000000000000000000000000000000000a40000aa8ce0000660003300019800cc01980d69b548000000031800031809a2692510670119c00000019800019800000000000000000410188183cc60f31e410600820c010304f8f609f1ef7401c00803808810070100100701084809018ac0000aabfff0000000000000000000000000d6db56c00000000000000000dab6db55afffdbfff00000000000000003dff840d09b9e83
def bigNat_9 : Nat := 0x7fffe01ffff7fffdeffffbdffff7bd80000000000000000000000000000000000000000000000000ad6ab6002f0000178000bc0005e002f005e0096d256c524d8297e00927e00000000000f8003e00000003e00003e0000000000000000007e0600103f040fc1e81f83d03f07bd80700000e0080000e00801c010000380210803802108000060ad6ab60000000000000000000000000000000d6db56d5b6daad7ffedb7ffe0000000000000000000000000000000083e001c11f614e20
def bigNat_10 : Nat := 0x7fffefc0000000000000000000000000000000000000000000000000000000000000000000000000084a2400300000180000c00006000300060000000000000000040000040000000000008000200000000200000200000000000000000007ff80fdfc007f0010fe0021fc004203f80087f0010847f0010fe002109fc004211fc004211091f80ad6ab6aabfff555fffaafffd57ffebfff7ffe00000000000000000000000000000000000000000000000000000000fc000185278004b9
def bigNat_11 : Nat := 0x7fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfffffffffffffffffff
def NN0 : Nat := 756
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 78), (78, 81), (81, 84), (84, 87), (87, 102), (102, 105), (105, 108), (108, 111), (111, 114), (114, 117), (117, 120), (120, 123), (123, 138), (138, 141), (141, 156), (156, 158), (158, 161), (161, 163), (163, 165), (165, 167), (167, 170), (170, 173), (173, 176), (176, 179), (179, 182), (182, 184), (184, 186), (186, 189), (189, 192), (192, 207), (207, 210), (210, 213), (213, 216), (216, 231), (231, 233), (233, 236), (236, 238), (238, 240), (240, 242), (242, 245), (245, 248), (248, 251), (251, 254), (254, 257), (257, 259), (259, 261), (261, 264), (264, 267), (267, 269), (269, 271), (271, 274), (274, 277), (277, 280), (280, 283), (283, 285), (285, 288), (288, 303), (303, 318), (318, 320), (320, 335), (335, 337), (337, 339), (339, 341), (341, 356), (356, 358), (358, 360), (360, 362), (362, 377), (377, 379), (379, 381), (381, 383), (383, 385), (385, 387), (387, 402), (402, 404), (404, 406), (406, 408), (408, 410), (410, 412), (412, 415), (415, 418), (418, 420), (420, 422), (422, 424), (424, 427), (427, 429), (429, 432), (432, 434), (434, 436)]
def segsY0 : List (ℕ × ℕ) := [(436, 449), (449, 453), (453, 456), (456, 461), (461, 465), (465, 470), (470, 475), (475, 493), (493, 497), (497, 502), (502, 507), (507, 525), (525, 528), (528, 533), (533, 538), (538, 556), (556, 561), (561, 579), (579, 583), (583, 588), (588, 593), (593, 611), (611, 616), (616, 634), (634, 637), (637, 642), (642, 647), (647, 665), (665, 670), (670, 688), (688, 693), (693, 711), (711, 729), (729, 736), (736, 755)]
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
lemma cov_full {t k k' z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hl : Live R m T k' t S) : Nat.beq (cov (pos' t) l v) l = true := by
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
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov := cov_full X hs hl
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
theorem lookCore_sound (hR : RR R) (enabled : Bool) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), lookCore I.NN I.AA I.HX I.HY l m g enabled fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [lookCore] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (guardedCoverage I.NN enabled (pos t) l v (tst (pos t) l (k + 1 - t) v (fun y => mv (lookCore I.NN I.AA I.HX I.HY l m g enabled fuel) l m g k t z v y))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have same (b : Bool) : guardedCoverage I.NN enabled (pos' t) l v b = b := by
        have hc := cov_full X hs hm.1
        cases enabled <;> simp [guardedCoverage, bR, hc]
      rw [same] at h
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  exact lookCore_sound X hR (Nat.beq fuel 14) fuel
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
def xw (e : ℕ × ℕ) : ℕ := I.rawP.getD e.1 0 ^^^ (2 ^ (I.NN + I.NN) - 1)
def rawL (E : List (ℕ × ℕ)) : List ℕ := I.rawP ++ E.map xw
def six : List (ℕ × ℕ) := [(0, 0), (1, 0), (2, 0), (6, 0), (7, 0)]
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawG_good : rawG.all (fun w => I.segsX.all (segGood w 0) &&
    I.segsY.all (segGood w I.NN)) = true := by decide +kernel

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
  have h := List.all_eq_true.1 rawG_good w hw
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

open Classical in
noncomputable def notCount : List Gate → ℕ
  | [] => 0
  | g :: gs => (if g.op = .not then 1 else 0) + notCount gs

def UniqueNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j

lemma count_noNot {gs : List Gate} (h : ∀ g ∈ gs, g.op ≠ .not) :
    notCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [notCount, h g (by simp), ih (fun w hw => h w (by simp [hw]))]

lemma count_pos {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) :
    1 ≤ notCount gs := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨w, hw, hn⟩ := h
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [notCount, hn]
    · have hle := ih ⟨w, hw, hn⟩
      simp only [notCount]
      omega

lemma count_le_one {gs : List Gate} (h : UniqueNot gs) : notCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases hn : g.op = .not
    · have tailNo : ∀ w ∈ gs, w.op ≠ .not := by
        intro w hw hnot
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
        have he := h i.succ ⟨0, by simp⟩ hnot hn
        exact Nat.succ_ne_zero i.val (congrArg Fin.val he)
      simp [notCount, hn, count_noNot tailNo]
    · have ht : UniqueNot gs := by
        intro i j hi hj
        have he := h i.succ j.succ hi hj
        exact Fin.ext (Nat.succ.inj (congrArg Fin.val he))
      simp [notCount, hn, ih ht]

lemma live_biBack {m T k t a b : ℕ} {S : Set ℕ} {S0 : Finset ℕ} (d : Bool)
    (ha : a ∈ S) (hb : b ∈ S) (hS : (S0 : Set ℕ) ⊆ insert (op d a b) S)
    (hl : Live Z0 m T k t S0) :
    ∃ inc ≤ 1, ∃ S1 : Finset ℕ, (S1 : Set ℕ) ⊆ S ∧ Live Z0 m T (k+inc) t S1 := by
  by_cases hout : op d a b ∈ S0
  · by_cases hab : a = b
    · exact ⟨0, by decide, S0, fun x hx => (hS hx).elim
        (fun e => by rw [hab, op_self] at e; exact e ▸ hb) id, by simpa using hl⟩
    · refine ⟨1, by decide, insert a (insert b (S0.erase (op d a b))), ?_,
        Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hout])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hS h1).resolve_left h2
  · exact ⟨0, by decide, S0, fun x hx => (hS hx).resolve_left (fun e => hout (e ▸ hx)),
      by simpa using hl⟩

lemma ex_liveCount {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k t : ℕ, t ≤ notCount gs ∧ k + notCount gs ≤ gs.length + t ∧
      ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    have hi : (ex m [] w).getD i 0 ∈ S := getD_mem hw h0 i
    exact ⟨0, 0, by decide, by decide, {_}, by simpa using hi, .stop⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stays (h : gv m w g ∈ S) :
        ∃ k t : ℕ, t ≤ notCount (g :: gs) ∧
          k + notCount (g :: gs) ≤ (g :: gs).length + t ∧
          ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
      have hw' : ∀ x ∈ w ++ [gv m w g], x ∈ S := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h
      obtain ⟨k,t,ht,hk,S0,hS,hl⟩ := ih _ _ hw' h0 hm hgs hT
      refine ⟨k,t,?_,?_,S0,hS,hl⟩ <;> simp only [notCount, List.length_cons] <;>
        split <;> omega
    have hw' : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inr (hw x hx)
      · exact Or.inl rfl
    obtain ⟨k,t,ht,hk,S0,hS,hl⟩ := ih _ _ hw' (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, _⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stays hm
      | [i] => exact stays (rd i)
      | i :: j :: _ =>
        obtain ⟨inc,hinc,S1,hs,hLive⟩ := live_biBack false (rd i) (rd j) hS hl
        refine ⟨k+inc,t,?_,?_,S1,hs,hLive⟩ <;> simp [notCount] <;> omega
    · match l with
      | [] => exact stays h0
      | [i] => exact stays (rd i)
      | i :: j :: _ =>
        obtain ⟨inc,hinc,S1,hs,hLive⟩ := live_biBack true (rd i) (rd j) hS hl
        refine ⟨k+inc,t,?_,?_,S1,hs,hLive⟩ <;> simp [notCount] <;> omega
    · match l with
      | [] => exact stays hm
      | i :: _ =>
        change (S0 : Set ℕ) ⊆ insert (w.getD i 0 ^^^ m) S at hS
        by_cases hz : w.getD i 0 ^^^ m ∈ S0
        · refine ⟨k+1,t+1,?_,?_,insert (w.getD i 0) (S0.erase (w.getD i 0 ^^^ m)),?_,
            Live.un (by rwa [Finset.insert_erase hz])⟩
          · simp [notCount]
            omega
          · simp [notCount]
            omega
          · intro x hx
            simp at hx
            rcases hx with rfl | ⟨ha,hb⟩
            · exact rd i
            · exact (hS ha).resolve_left hb
        · refine ⟨k,t,?_,?_,S0,fun x hx => (hS hx).resolve_left (fun e => hz (e ▸ hx)),hl⟩ <;>
            simp [notCount] <;> omega

def picked {X : Type} (F : X → Bool) (G : Fin 8 → X → Bool) : Prop :=
  ∀ x, F x = true → ∃ b, G b x = true

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
      cases scan (fun e => bif PEqualNP.Outside.L_meta_35240_aux.hb H (x.s + e.s) then q b x e else false) xs <;> rfl
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

section
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X

set_option maxHeartbeats 0 in
lemma one_bi_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S S1 : Finset ℕ} (hs : StOk P T l k z v S)
    (hcod : ∀ w ∈ v, w.r = R w.s)
    {k0 : ℕ} (hk : k0+1 ≤ k) (hl : Live Z0 m T (k0+1) t S)
    {a b : ℕ} {d : Bool} (ha : R a ≠ 0) (hb' : R b ≠ 0) (hb : Bi Z0 d a b S S1)
    (hl1 : Live Z0 m T k0 t S1)
    (hmW : ∀ q < k0+1, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T (k0+1) t S))
    (h1 : ∀ wa ∈ v, ∀ wb ∈ v, wa.s = a → wb.s = b → wa.s ≠ wb.s → wa.r ≠ 0 → wb.r ≠ 0 →
      ∃ go : (XW → XW → Bool) → List XW → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) wa) (mkx (pos' t) l (wst (pos' t) l v) wb) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) wb) (mkx (pos' t) l (wst (pos' t) l v) wa) = false) : False := by
  have hmin : Min Z0 m T (k0+1) t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb rfl rfl hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
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
set_option maxHeartbeats 0 in
lemma topC_bi_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b)
    {K k t z H : ℕ} {v : List W} {S S1 : Finset ℕ}
    (h : topC l m g K H 0 k t z v = false)
    (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k0 a b : ℕ} {d : Bool} (hk : k0+1 ≤ k) (hl : Live Z0 m T (k0+1) t S)
    (ha : R a ≠ 0) (hb' : R b ≠ 0) (hb0 : Bi Z0 d a b S S1) (hTail : Live Z0 m T k0 t S1)
    (hash : hb H (a+b) = true)
    (hmW : ∀ q < k0+1, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  have un : tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (mv (look l m g K) l m g k t z v y) (Nat.beq 0 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v
        (fun f xs => pairsC H f (fs xs)))) = false := by
    change (Bool.rec (motive := fun _ => Bool)
      (tst (pos t) l (k + 1 - t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
           (mv (look l m g K) l m g k t z v y) (Nat.beq 0 1)) true
        (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v
          (fun f xs => pairsC H f (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false => rw [h0, cond_false] at h; exact h
  have hmin : Min Z0 m T (k0+1) t S := ⟨hl, fun q hq sq => hmW q hq
    (sq.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y,hFy,hyk⟩ := tst_sound X hs hmin hk
  have hthen := (hFy _).symm.trans un
  have hnode := (or_false' X hthen).1
  refine one_bi_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K)
      hs hcod hk hl ha hb' hb0 hTail hmW hyk ?_
  intro wa hwa wb hwb ea eb hne har hcr
  refine ⟨_,hnode,fun f' hp => ?_⟩
  have hpw := pairsC_false hp
  have symm : Std.Symm (fun a b : XW => hb H (a.s + b.s) = true → (f' a b = false ∨ f' b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  exact (hpw.imp (S := fun a b => hb H (a.s + b.s) = true → (f' a b = false ∨ f' b a = false))
    fun hh e => Or.inl (hh e)).forall (fs_mem (List.mem_map_of_mem hwa) har)
      (fs_mem (List.mem_map_of_mem hwb) hcr) (fun e => hne (congrArg XW.s e)) (by
        change hb H (wa.s + wb.s) = true
        rw [ea,eb]
        exact hash)

end

set_option maxHeartbeats 0 in
theorem imp_of_bi {Q : List (ℕ × ℕ)} {Z L k0 t H a b : ℕ} {d : Bool}
    {S S1 : Finset ℕ} (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp [] e.1 e.2)
    (hk : k0+1 < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z))
    (hl : Live Z0 (mz Z) (tz Z) (k0+1) t S)
    (ha : a ∈ WZ [] Z) (hwB : b ∈ WZ [] Z)
    (bi : Bi Z0 d a b S S1) (tail : Live Z0 (mz Z) (tz Z) k0 t S1)
    (hash : hb H (a+b) = true)
    (hmin : ∀ q < k0+1, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ [] Z)))
    (hchk : chk [] Q Z (L-1) t H 0 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ ([] : List (ℕ × ℕ)), e ∈ six := by simp
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) (k0+1) t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ [] Z := by
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
  have hpw : pwr [] Z = 0 ∨ pwr [] Z ∈ S := Or.inl rfl
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL [])
  set v := (avl (PZ Q) (mz Z) (rawL [])).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL [])) := List.filter_sublist
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
  have hcod : ∀ w ∈ v, w.r = RZ [] Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ [] Z := ⟨x, hx, rfl⟩
    change 3 = RZ [] Z (x &&& mz Z)
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
  have hhas : hasP (pwr [] Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have top : topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) H 0 (L - 1) t
      (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    have h2 := hchk
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) H 0 (L - 1) t z r)
      (fun h => rfl) hst hm (by omega) h3
  have haR : RZ [] Z a ≠ 0 := by rw [← RZ_set] at ha; exact ha
  have hbR : RZ [] Z b ≠ 0 := by rw [← RZ_set] at hwB; exact hwB
  refine topC_bi_sound X (RZ_R [] Z) (RZ_R2 [] Z) top hst hcod (by omega) hl
    haR hbR bi tail hash ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

section inst_data
def rt4 : List (ℕ × ℕ) := [(15, 2), (23, 4), (27, 5), (29, 2), (30, 4), (39, 4), (43, 4), (45, 4), (46, 2), (51, 3), (53, 4), (54, 5), (57, 4), (58, 4), (60, 2), (71, 3), (75, 5), (77, 5), (78, 5), (83, 5), (85, 3), (86, 5), (89, 5), (90, 5), (92, 5), (99, 3), (101, 5), (102, 5), (105, 5), (106, 3), (108, 5), (113, 3), (114, 5), (116, 5), (120, 3), (135, 1), (139, 2), (141, 1), (142, 1), (147, 4), (149, 1), (150, 4), (153, 2), (154, 4), (156, 1), (163, 2), (165, 3), (166, 2), (169, 3), (170, 1), (172, 1), (177, 2), (178, 4), (180, 2), (184, 1), (195, 1), (197, 1), (198, 2), (201, 3), (202, 2), (204, 3), (209, 1), (210, 4), (212, 2), (216, 2), (225, 1), (226, 1), (228, 3), (232, 1), (240, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r4 : rt4.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma i4 : ∀ e ∈ rt4, Imp [] e.1 e.2 := okAll (T := []) r4 (by simp)

def rt3 : List (ℕ × ℕ) := [(7, 5), (11, 6), (13, 5), (14, 5), (19, 6), (21, 5), (22, 7), (25, 6), (26, 7), (28, 5), (35, 5), (37, 7), (38, 6), (41, 7), (42, 5), (44, 5), (49, 5), (50, 6), (52, 6), (56, 5), (67, 6), (69, 6), (70, 6), (73, 8), (74, 6), (76, 8), (81, 6), (82, 7), (84, 6), (88, 6), (97, 6), (98, 6), (100, 8), (104, 6), (112, 6), (131, 4), (133, 3), (134, 4), (137, 4), (138, 4), (140, 3), (145, 4), (146, 7), (148, 4), (152, 4), (161, 4), (162, 4), (164, 4), (168, 3), (176, 4), (193, 3), (194, 4), (196, 4), (200, 4), (208, 4), (224, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3 : rt3.all (fun e => okE [] (pr rt4 e.1) e) = true := by decide +kernel
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll (T := rt4) r3 i4

def rt2 : List (ℕ × ℕ) := [(3, 8), (5, 8), (6, 8), (9, 9), (10, 8), (12, 8), (17, 8), (18, 10), (20, 8), (24, 8), (33, 8), (34, 8), (36, 9), (40, 8), (48, 8), (65, 9), (66, 9), (68, 9), (72, 9), (80, 9), (96, 9), (129, 6), (130, 7), (132, 6), (136, 6), (144, 7), (160, 6), (192, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2 : rt2.all (fun e => okE [] (pr (rt3 ++ rt4) e.1) e) = true := by decide +kernel
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll (T := (rt3 ++ rt4)) r2 (apI i3 i4)

def rt : List (ℕ × ℕ) := (rt2 ++ (rt3 ++ rt4))
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := (apI i2 (apI i3 i4))

open PEqualNP.CircuitLowerBounds

def witness : List Gate := [⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [16, 0]⟩, ⟨.and, [17, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [20, 14]⟩, ⟨.or, [21, 18]⟩]

theorem witness_basis : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

theorem f_graph (x : Fin 8 → Bool) : f x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  have hx : f x = true ↔ (x 0 = true ∧ x 3 = true) ∨ (x 1 = true ∧ x 4 = true) ∨ (x 0 = true ∧ x 5 = true) ∨ (x 2 = true ∧ x 5 = true) ∨ (x 2 = true ∧ x 6 = true) ∨ (x 3 = true ∧ x 6 = true) ∨ (x 0 = true ∧ x 7 = true) ∨ (x 1 = true ∧ x 7 = true) ∨ (x 2 = true ∧ x 7 = true) ∨ (x 3 = true ∧ x 7 = true) ∨ (x 4 = true ∧ x 7 = true) ∨ (x 5 = true ∧ x 7 = true) := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  rw [Bool.eq_iff_iff, hx, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h)
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
  · rintro ⟨i, hi, h⟩
    have hi' : i < 12 := hi
    interval_cases i <;> simp_all

def EF : ℕ := ((((((((((((rawP0.getD 0 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 5 0 &&& rawP0.getD 7 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 8 := rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
def selectedBits (flag : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if flag n then selectedBits flag n ||| 2 ^ n else selectedBits flag n

lemma selectedBits_bit (flag : ℕ → Bool) (n k : ℕ) :
    (selectedBits flag n).testBit k = (decide (k < n) && flag k) := by
  induction n with
  | zero => simp [selectedBits]
  | succ n ih =>
    rw [selectedBits]
    cases hk : flag n
    · simp only [hk, Bool.false_eq_true, ite_false, ih]
      by_cases lt : k < n
      · simp [lt, show k < n + 1 by omega]
      · by_cases eq : k = n
        · subst k
          simp [hk]
        · simp [lt, show ¬ k < n + 1 by omega]
    · simp only [hk, ite_true, Nat.testBit_or, ih, Nat.testBit_two_pow]
      by_cases lt : k < n
      · simp [lt, show k < n + 1 by omega, show k ≠ n by omega, show n ≠ k by omega]
      · by_cases eq : k = n
        · subst k
          simp [hk]
        · simp [lt, eq, Ne.symm eq, show ¬ k < n + 1 by omega]

theorem Live.mapSignals {m T m' T' k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (f : ℕ → ℕ) (htarget : f T = T') (hneg : ∀ a, f (a ^^^ m) = f a ^^^ m')
    (hbin : ∀ d a b, f (op d a b) = op d (f a) (f b)) :
    ∃ k' t' : ℕ, t' ≤ t ∧ k' + t ≤ k + t' ∧
      ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ f '' (S : Set ℕ) ∧ Live Z0 m' T' k' t' S' := by
  induction hl with
  | stop =>
    exact ⟨0,0,le_rfl,le_rfl,{T'},by
      intro x hx
      simp at hx
      subst x
      exact ⟨T,by simp,htarget⟩,.stop⟩
  | @un k t a U hl ih =>
    obtain ⟨k',t',ht,hk,S',hs,hLive⟩ := ih
    by_cases used : f (a ^^^ m) ∈ S'
    · refine ⟨k'+1,t'+1,by omega,by omega,insert (f a) (S'.erase (f (a ^^^ m))),?_,
        Live.un ?_⟩
      · intro x hx
        simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hx
        rcases hx with rfl | ⟨hne,hx⟩
        · exact ⟨a,by simp,rfl⟩
        · obtain ⟨v,hv,rfl⟩ := hs hx
          have hu : v ∈ U := by
            rcases Finset.mem_insert.mp hv with ev | hv
            · exact (hne (congrArg f ev)).elim
            · exact hv
          exact ⟨v,by simp [hu],rfl⟩
      · rw [← hneg, Finset.insert_erase used]
        exact hLive
    · refine ⟨k',t',by omega,by omega,S',?_,hLive⟩
      intro x hx
      obtain ⟨v,hv,rfl⟩ := hs hx
      have hu : v ∈ U := by
        rcases Finset.mem_insert.mp hv with ev | hv
        · exact (used ((congrArg f ev) ▸ hx)).elim
        · exact hv
      exact ⟨v,by simp [hu],rfl⟩
  | @bi k t d a b U hab hal hl ih =>
    obtain ⟨k',t',ht,hk,S',hs,hLive⟩ := ih
    by_cases used : f (op d a b) ∈ S'
    · by_cases heq : f a = f b
      · refine ⟨k',t',ht,by omega,S',?_,hLive⟩
        intro x hx
        obtain ⟨v,hv,rfl⟩ := hs hx
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨b,by simp,by rw [hbin, heq, op_self]⟩
        · exact ⟨v,by simp [hv],rfl⟩
      · refine ⟨k'+1,t',ht,by omega,
          insert (f a) (insert (f b) (S'.erase (f (op d a b)))),?_,
          Live.bi (d := d) heq (al0 _ _ _) ?_⟩
        · intro x hx
          simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hx
          rcases hx with rfl | rfl | ⟨hne,hx⟩
          · exact ⟨a,by simp,rfl⟩
          · exact ⟨b,by simp,rfl⟩
          · obtain ⟨v,hv,rfl⟩ := hs hx
            rcases Finset.mem_insert.mp hv with ev | hv
            · exact (hne (congrArg f ev)).elim
            · exact ⟨v,by simp [hv],rfl⟩
        · rw [← hbin, Finset.insert_erase used]
          exact hLive
    · refine ⟨k',t',ht,by omega,S',?_,hLive⟩
      intro x hx
      obtain ⟨v,hv,rfl⟩ := hs hx
      rcases Finset.mem_insert.mp hv with ev | hv
      · exact (used ((congrArg f ev) ▸ hx)).elim
      · exact ⟨v,by simp [hv],rfl⟩

theorem Sol.mapSignals {m T m' T' k : ℕ} {S : Set ℕ} (hl : Sol Z0 m T k S)
    (f : ℕ → ℕ) (htarget : f T = T') (hneg : ∀ a, f (a ^^^ m) = f a ^^^ m')
    (hbin : ∀ d a b, f (op d a b) = op d (f a) (f b)) :
    Sol Z0 m' T' k (f '' S) := by
  induction hl with
  | @done q U h =>
    exact .done ⟨T,h,htarget⟩
  | @un q U a ha _ ih =>
    refine .un (a := f a) ⟨a,ha,rfl⟩ (ih.mono le_rfl ?_)
    rintro _ ⟨w,hw,rfl⟩
    rcases hw with rfl | hw
    · exact Or.inl (hneg a)
    · exact Or.inr ⟨w,hw,rfl⟩
  | @bi q U d a b ha hb _ _ ih =>
    refine .bi (d := d) (a := f a) (b := f b) ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ (al0 _ _ _) (ih.mono le_rfl ?_)
    rintro _ ⟨w,hw,rfl⟩
    rcases hw with rfl | hw
    · exact Or.inl (hbin d a b)
    · exact Or.inr ⟨w,hw,rfl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def permutations : List (List (Fin 8)) :=
  [[0,1,2,3,4,5,6,7], [5,1,3,2,4,0,6,7], [0,4,2,3,1,5,6,7], [5,4,3,2,1,0,6,7]]

def permuted (a : Fin 4) (i : Fin 8) : Fin 8 :=
  (permutations.getD a.val []).getD i.val i

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma permuted_preserves_f : ∀ a : Fin 4, ∀ x : Fin 8 → Bool,
    f (fun i => x (permuted a i)) = f x := by
  decide +kernel

def fullMask : ℕ := 2 ^ 256 - 1

def fullWire (i : Fin 8) : ℕ := selectedBits (·.testBit i.val) 256

def fullBank : List ℕ := List.ofFn fullWire

def fullTarget : ℕ := selectedBits (fun k => f (fun i : Fin 8 => k.testBit i.val)) 256

def fullStock : Set ℕ := {a | a ∈ fullBank}

lemma fullWire_mask (i : Fin 8) : fullWire i &&& fullMask = fullWire i := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, fullWire, selectedBits_bit, fullMask, Nat.testBit_two_pow_sub_one]
  cases decide (k < 256) <;> simp

lemma fullTarget_mask : fullTarget &&& fullMask = fullTarget := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, fullTarget, selectedBits_bit, fullMask, Nat.testBit_two_pow_sub_one]
  cases decide (k < 256) <;> simp

lemma fullStock_rows {x : ℕ} (h : x ∈ fullStock) : ∃ v : Fin 8, x = fullWire v := by
  simpa [fullStock, fullBank, eq_comm] using (List.mem_ofFn.mp h)

lemma fullStock_mask {x : ℕ} (h : x ∈ C fullMask fullStock) : x &&& fullMask = x := by
  rcases h with h | h
  · obtain ⟨i,rfl⟩ := fullStock_rows h
    exact fullWire_mask i
  · simp at h
    rcases h with rfl | rfl <;> simp

lemma fullBridge (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩)
    (hf : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = f x) :
    ∃ k t : ℕ, t ≤ notCount gates ∧ k + notCount gates ≤ gates.length+t ∧
      ∃ S : Finset ℕ, (S : Set ℕ) ⊆ C fullMask fullStock ∧ Live Z0 fullMask fullTarget k t S := by
  have hmasked : ∀ w ∈ fullBank, w &&& fullMask = w := fun _ h => fullStock_mask (Or.inl h)
  have hinit : ∀ w ∈ fullBank, w ∈ C fullMask fullStock := fun _ h => Or.inl h
  have hsub := ex_sub fullMask (gs := gates) hmasked
  have hget := getD_mem (S := {x | x &&& fullMask = x}) hsub (by simp) o
  have hresult : (ex fullMask gates fullBank).getD o 0 = fullTarget := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 256
    · have hm : fullMask.testBit k = true := by
        rw [fullMask,Nat.testBit_two_pow_sub_one]
        simp [hk]
      have hrows : fullBank.map (fun v => v.testBit k) = List.ofFn (fun v : Fin 8 => k.testBit v.val) := by
        rw [fullBank,List.map_ofFn]
        apply congrArg (fun u : Fin 8 → Bool => List.ofFn u)
        funext v
        simp [Function.comp_def, fullWire, selectedBits_bit,hk]
      rw [← getD_map, ex_bit fullMask hm gates fullBank hD,hrows]
      have hev := hf (fun v : Fin 8 => k.testBit v.val)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun v : Fin 8 => k.testBit v.val)).getD o false = f (fun v : Fin 8 => k.testBit v.val) at hev
      rw [hev]
      simp [fullTarget,selectedBits_bit,hk]
    · have hm : fullMask.testBit k = false := by
        rw [fullMask,Nat.testBit_two_pow_sub_one]
        simp [hk]
      have hs := congrArg (fun n => n.testBit k) hget
      simp only [Set.mem_setOf_eq,Nat.testBit_and,hm,Bool.and_false] at hs
      rw [← hs]
      simp [fullTarget,selectedBits_bit,hk]
  exact ex_liveCount fullMask gates fullBank (C fullMask fullStock) hinit
    (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨o,hresult⟩

def sampleIndex (a : Fin 4) (k : ℕ) : ℕ :=
  selectedBits (fun i =>
    (rawP0.getD (permuted a ⟨i % 8, Nat.mod_lt _ (by decide)⟩).val 0).testBit k) 8 % 256

lemma sampleIndex_lt (a : Fin 4) (k : ℕ) : sampleIndex a k < 256 := Nat.mod_lt _ (by decide)

lemma sampleIndex_bit (a : Fin 4) (k : ℕ) (i : Fin 8) :
    (sampleIndex a k).testBit i.val = (rawP0.getD (permuted a i).val 0).testBit k := by
  unfold sampleIndex
  rw [show (256:ℕ) = 2^8 by decide, Nat.testBit_mod_two_pow, selectedBits_bit]
  simp [i.isLt, Nat.mod_eq_of_lt i.isLt]

def pull (a : Fin 4) (w : ℕ) : ℕ :=
  selectedBits (fun k => (mz 0).testBit k && w.testBit (sampleIndex a k)) (I.NN + I.NN)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma sampleMaskBound : mz 0 < 2^(I.NN + I.NN) := by decide +kernel

lemma pull_bit (a : Fin 4) (w k : ℕ) :
    (pull a w).testBit k = ((mz 0).testBit k && w.testBit (sampleIndex a k)) := by
  unfold pull
  rw [selectedBits_bit]
  by_cases hk : k < I.NN + I.NN
  · simp [hk]
  · have hb := Nat.testBit_lt_two_pow (lt_of_lt_of_le sampleMaskBound (Nat.pow_le_pow_right (by decide) (by omega : I.NN+I.NN ≤ k)))
    simp [hk,hb]

lemma pull_zero (a : Fin 4) : pull a 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp [pull_bit]

lemma pull_mask (a : Fin 4) : pull a fullMask = mz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit,fullMask,Nat.testBit_two_pow_sub_one]
  simp [sampleIndex_lt]

lemma pull_neg (a : Fin 4) (w : ℕ) : pull a (w ^^^ fullMask) = pull a w ^^^ mz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit, Nat.testBit_xor, Nat.testBit_xor, pull_bit, fullMask, Nat.testBit_two_pow_sub_one]
  simp only [sampleIndex_lt,decide_true]
  cases (mz 0).testBit k <;> cases w.testBit (sampleIndex a k) <;> rfl

lemma pull_op (a : Fin 4) (d : Bool) (u v : ℕ) :
    pull a (op d u v) = op d (pull a u) (pull a v) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit, op_bit, op_bit, pull_bit, pull_bit]
  cases d <;> cases (mz 0).testBit k <;> cases u.testBit (sampleIndex a k) <;>
    cases v.testBit (sampleIndex a k) <;> rfl

lemma pull_fullWire (a : Fin 4) (i : Fin 8) :
    pull a (fullWire i) = rawP0.getD (permuted a i).val 0 &&& mz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pull_bit, Nat.testBit_and, fullWire, selectedBits_bit, sampleIndex_bit]
  simp [sampleIndex_lt,Bool.and_comm]

lemma pull_target (a : Fin 4) : pull a fullTarget = tz 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [← EF_ok,pull_bit, Nat.testBit_and, f_bit, fullTarget, selectedBits_bit]
  simp only [sampleIndex_lt,decide_true,Bool.true_and]
  have equiv : (fun i : Fin 8 => (sampleIndex a k).testBit i.val) =
      fun i : Fin 8 => (rawP0.getD (permuted a i).val 0).testBit k := by
    funext i
    exact sampleIndex_bit a k i
  have same := permuted_preserves_f a (fun v => (rawP0.getD v.val 0).testBit k)
  rw [equiv, same, Bool.and_comm]

lemma pull_initial (a : Fin 4) :
    pull a '' C fullMask fullStock ⊆ C (mz 0) (WZ [] 0) := by
  rintro _ ⟨v,hv,rfl⟩
  rcases hv with hv | hv
  · obtain ⟨i,rfl⟩ := fullStock_rows hv
    rw [pull_fullWire]
    refine Or.inl ⟨_,?_,rfl⟩
    apply List.mem_append_left
    have hh : (permuted a i).val < rawP0.length := by simpa [rawP_len0] using (permuted a i).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]
    exact List.getElem_mem _
  · simp at hv
    rcases hv with rfl | rfl
    · rw [pull_zero]
      exact Or.inr (Set.mem_insert _ _)
    · rw [pull_mask]
      exact Or.inr (Set.mem_insert_of_mem _ rfl)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness table specifies one source sample position for each of the 256 assignments. -/
def cofactorPosition (a : Fin 4) (table k : ℕ) : ℕ :=
  (table >>> (13 * sampleIndex a k)) &&& 8191

def cofactorAlignment (known other table : ℕ) (a : Fin 4) : Bool :=
  (List.range (I.NN + I.NN)).all fun k =>
    !(mz known).testBit k ||
      ((mz other).testBit (cofactorPosition a table k) &&
        (sampleIndex 0 (cofactorPosition a table k) == sampleIndex a k))

lemma cofactorAlignment_sound {known other table : ℕ} {a : Fin 4}
    (h : cofactorAlignment known other table a = true) {k : ℕ}
    (hk : k < I.NN + I.NN) (hm : (mz known).testBit k = true) :
    (mz other).testBit (cofactorPosition a table k) = true ∧
      sampleIndex 0 (cofactorPosition a table k) = sampleIndex a k := by
  have ha := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa [hm] using ha

def cofactorPull (known table : ℕ) (a : Fin 4) (w : ℕ) : ℕ :=
  selectedBits (fun k => (mz known).testBit k && w.testBit (cofactorPosition a table k)) (I.NN + I.NN)

lemma cofactorPull_bit {known : ℕ} (bound : mz known < 2 ^ (I.NN + I.NN))
    (a : Fin 4) (table w k : ℕ) :
    (cofactorPull known table a w).testBit k = ((mz known).testBit k && w.testBit (cofactorPosition a table k)) := by
  rw [cofactorPull, selectedBits_bit]
  by_cases hk : k < I.NN + I.NN
  · simp [hk]
  · have hm := Nat.testBit_lt_two_pow
      (bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega : I.NN + I.NN ≤ k)))
    simp [hk,hm]

lemma rawP_getD_mem (i : Fin 8) : rawP0.getD i.val 0 ∈ rawP0 := by
  have h : i.val < rawP0.length := by rw [rawP_len0]; exact i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem _

lemma rawP_mem_getD {w : ℕ} (h : w ∈ rawP0) : ∃ i : Fin 8, w = rawP0.getD i.val 0 := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨i,by simpa only [rawP_len0] using hi⟩,?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact eq.symm

set_option maxHeartbeats 0 in
lemma imp_by_cofactor_symmetry {known other L table : ℕ} {a : Fin 4}
    (bound : mz known < 2 ^ (I.NN + I.NN))
    (aligned : cofactorAlignment known other table a = true)
    (fKnown : EF &&& mz known = tz known) (fOther : EF &&& mz other = tz other)
    (lower : Imp [] known L) : Imp [] other L := by
  let map := cofactorPull known table a
  have bit := cofactorPull_bit bound a table
  have data (k : ℕ) (hm : (mz known).testBit k = true) := by
    have hk : k < I.NN + I.NN := by
      by_contra h
      have zero := Nat.testBit_lt_two_pow
        (bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega : I.NN + I.NN ≤ k)))
      rw [zero] at hm
      exact Bool.noConfusion hm
    exact cofactorAlignment_sound aligned hk hm
  have row (k : ℕ) (i : Fin 8) (hm : (mz known).testBit k = true) :
      (rawP0.getD i.val 0).testBit (cofactorPosition a table k) =
        (rawP0.getD (permuted a i).val 0).testBit k := by
    have h := congrArg (fun x : ℕ => x.testBit i.val) (data k hm).2
    simpa only [sampleIndex_bit, show permuted 0 i = i from by
      fin_cases i <;> rfl] using h
  have m : map (mz other) = mz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [show map (mz other) = cofactorPull known table a (mz other) from rfl,bit]
    by_cases hm : (mz known).testBit k = true
    · rw [(data k hm).1,hm,Bool.and_true]
    · simp [Bool.eq_false_iff.mpr hm]
  have z : map 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [show map 0 = cofactorPull known table a 0 from rfl,bit]
    simp
  have neg (w : ℕ) : map (w ^^^ mz other) = map w ^^^ mz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (w ^^^ mz other)).testBit k =
      (cofactorPull known table a w ^^^ mz known).testBit k
    rw [bit,Nat.testBit_xor,Nat.testBit_xor,bit]
    by_cases hm : (mz known).testBit k = true
    · simp only [(data k hm).1,hm,Bool.true_and]
    · simp [Bool.eq_false_iff.mpr hm]
  have bin (d : Bool) (x y : ℕ) : map (op d x y) = op d (map x) (map y) := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (op d x y)).testBit k =
      (op d (cofactorPull known table a x) (cofactorPull known table a y)).testBit k
    rw [bit,op_bit,op_bit,bit,bit]
    cases d <;> cases (mz known).testBit k <;> rfl
  have target : map (tz other) = tz known := by
    apply Nat.eq_of_testBit_eq
    intro k
    change (cofactorPull known table a (tz other)).testBit k = (tz known).testBit k
    rw [bit,← fOther,← fKnown,Nat.testBit_and,Nat.testBit_and]
    by_cases hm : (mz known).testBit k = true
    · rw [(data k hm).1,hm,Bool.and_true,Bool.and_true,Bool.true_and,f_bit,f_bit]
      have eq : (fun i : Fin 8 => (rawP0.getD i.val 0).testBit (cofactorPosition a table k)) =
          fun i : Fin 8 => (rawP0.getD (permuted a i).val 0).testBit k := funext fun i => row k i hm
      rw [eq]
      exact permuted_preserves_f a (fun i : Fin 8 => (rawP0.getD i.val 0).testBit k)
    · simp [Bool.eq_false_iff.mpr hm]
  have initial : map '' C (mz other) (WZ [] other) ⊆ C (mz known) (WZ [] known) := by
    rintro _ ⟨w,h,rfl⟩
    rcases h with h | h
    · obtain ⟨v,hv,rfl⟩ := h
      have hv' : v ∈ rawP0 := by
        change v ∈ I.rawP
        simpa only [rawL,List.map_nil,List.append_nil] using hv
      obtain ⟨i,rfl⟩ := rawP_mem_getD hv'
      refine Or.inl ⟨_,List.mem_append_left _ (rawP_getD_mem (permuted a i)),?_⟩
      apply Nat.eq_of_testBit_eq
      intro k
      change (cofactorPull known table a (rawP0.getD i.val 0 &&& mz other)).testBit k =
        (rawP0.getD (permuted a i).val 0 &&& mz known).testBit k
      rw [bit,Nat.testBit_and,Nat.testBit_and]
      by_cases hm : (mz known).testBit k = true
      · rw [(data k hm).1,row k i hm,hm,Bool.and_true,Bool.true_and]
      · simp [Bool.eq_false_iff.mpr hm]
    · simp at h
      rcases h with rfl | rfl
      · rw [z]
        exact Or.inr (Set.mem_insert _ _)
      · rw [m]
        exact Or.inr (Set.mem_insert_of_mem _ rfl)
  intro q hq sol
  exact lower q hq ((sol.mapSignals map target neg bin).mono le_rfl initial)

def q1 : List (ℕ × ℕ) := pr rt 1
lemma co1_p : pOk 1 q1 = true := by decide +kernel
lemma co1_id : ∀ a ∈ q1, Imp [] a.1 a.2 := by
  intro a ha
  unfold q1 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t0_res : chk [] q1 1 10 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 0 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t0_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t1_res : chk [] q1 1 10 1 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 1 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t1_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t2_res : chk [] q1 1 10 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 2 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t2_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t3_res : chk [] q1 1 10 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 3 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t3_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t4_res : chk [] q1 1 10 4 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 4 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t4_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t5_res : chk [] q1 1 10 5 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 5 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t5_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t6_res : chk [] q1 1 10 6 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 6 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t6_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t7_res : chk [] q1 1 10 7 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 7 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t7_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t8_res : chk [] q1 1 10 8 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 8 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t8_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t9_res : chk [] q1 1 10 9 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 9 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t9_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co1t10_res : chk [] q1 1 10 10 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co1t10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q1 1 10 10 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co1t10_res⟩
lemma co1 : Imp [] 1 11 := imp_of (Or.inl rfl) co1_p (by norm_num) co1_id
    (Or.inr fun t ht => by
  interval_cases t
  · exact co1t0
  · exact co1t1
  · exact co1t2
  · exact co1t3
  · exact co1t4
  · exact co1t5
  · exact co1t6
  · exact co1t7
  · exact co1t8
  · exact co1t9
  · exact co1t10)

def q2 : List (ℕ × ℕ) := pr rt 2
lemma co2_p : pOk 2 q2 = true := by decide +kernel
lemma co2_id : ∀ a ∈ q2, Imp [] a.1 a.2 := by
  intro a ha
  unfold q2 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeAppend (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all

noncomputable def restrictedTest (Q : List (ℕ × ℕ)) (Z t : ℕ)
    (cases : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  let a := cases.getD i (0,0)
  !chkFast [] Q Z 11 t a.1 a.2

lemma restrictedWitness (Q : List (ℕ × ℕ)) (Z t : ℕ) (M : List (ℕ × ℕ))
    (covers : mFull M = true) (checked : rangeCheck (restrictedTest Q Z t M) 0 M.length = true) :
    ∃ cases : List (ℕ × ℕ), mFull cases = true ∧
      ∀ a ∈ cases, chk [] Q Z 11 t a.1 a.2 = false := by
  refine ⟨M,covers,?_⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
  have h := boolOfNeg (rangeCheck_at checked hi)
  simpa only [restrictedTest, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, chkFast_eq] using h

def co2t0_cov : List (ℕ × ℕ) := [(0x0, 1), (0x20, 0), (0x2000, 0), (0x400000000, 0), (0x40000000000, 0), (0x400000000000000, 0), (0x800000000000000, 0), (0x8000000000000000, 0), (0x40000000000000000, 0), (0x100000000000000000, 0), (0x800000000000000000, 0), (0x10000000000000000000, 0), (0x800000000000000000000, 0), (0x10000000000000000000000, 0), (0x200000000000000000000000, 0), (0x10000000000000000000000000000, 0), (0x200000000000000000000000000000, 0), (0x4000000000000000000000000000000, 0), (0x200000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000000, 0), (0x3ffbffffffffffff7bdffffbdeffffdef7ef6b73fffbfbffffdfdf, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t0batch0 : rangeCheck (restrictedTest q2 2 0 co2t0_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t0batch1 : rangeCheck (restrictedTest q2 2 0 co2t0_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t0batch2 : rangeCheck (restrictedTest q2 2 0 co2t0_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t0batch3 : rangeCheck (restrictedTest q2 2 0 co2t0_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t0batch4 : rangeCheck (restrictedTest q2 2 0 co2t0_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t0batch5 : rangeCheck (restrictedTest q2 2 0 co2t0_cov) 20 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co2t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 0 a.1 a.2 = false :=
  restrictedWitness q2 2 0 co2t0_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q2 2 0 co2t0_cov) 0 12 11
      (@rangeAppend (restrictedTest q2 2 0 co2t0_cov) 0 4 8
       co2t0batch0
       (@rangeAppend (restrictedTest q2 2 0 co2t0_cov) 4 4 4
        co2t0batch1
        co2t0batch2))
      (@rangeAppend (restrictedTest q2 2 0 co2t0_cov) 12 4 7
       co2t0batch3
       (@rangeAppend (restrictedTest q2 2 0 co2t0_cov) 16 4 3
        co2t0batch4
        co2t0batch5)))

def co2t1_cov : List (ℕ × ℕ) := [(0x0, 1), (0x20, 0), (0x2000, 0), (0x400000000, 0), (0x40000000000, 0), (0x400000000000000, 0), (0x800000000000000, 0), (0x8000000000000000, 0), (0x40000000000000000, 0), (0x100000000000000000, 0), (0x800000000000000000, 0), (0x10000000000000000000, 0), (0x800000000000000000000, 0), (0x10000000000000000000000, 0), (0x200000000000000000000000, 0), (0x10000000000000000000000000000, 0), (0x200000000000000000000000000000, 0), (0x4000000000000000000000000000000, 0), (0x200000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000000, 0), (0x3ffbffffffffffff7bdffffbdeffffdef7ef6b73fffbfbffffdfdf, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch0 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch1 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch2 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch3 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch4 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t1batch5 : rangeCheck (restrictedTest q2 2 1 co2t1_cov) 20 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co2t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 1 a.1 a.2 = false :=
  restrictedWitness q2 2 1 co2t1_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 0 12 11
      (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 0 4 8
       co2t1batch0
       (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 4 4 4
        co2t1batch1
        co2t1batch2))
      (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 12 4 7
       co2t1batch3
       (@rangeAppend (restrictedTest q2 2 1 co2t1_cov) 16 4 3
        co2t1batch4
        co2t1batch5)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t2_res : chk [] q2 2 11 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 2 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t2_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t3_res : chk [] q2 2 11 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 3 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t3_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t4_res : chk [] q2 2 11 4 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 4 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t4_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t5_res : chk [] q2 2 11 5 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 5 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t5_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t6_res : chk [] q2 2 11 6 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 6 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t6_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t7_res : chk [] q2 2 11 7 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 7 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t7_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t8_res : chk [] q2 2 11 8 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 8 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t8_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t9_res : chk [] q2 2 11 9 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 9 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t9_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t10_res : chk [] q2 2 11 10 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 10 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t10_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co2t11_res : chk [] q2 2 11 11 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co2t11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q2 2 11 11 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co2t11_res⟩
lemma co2 : Imp [] 2 12 := imp_of (Or.inl rfl) co2_p (by norm_num) co2_id
    (Or.inr fun t ht => by
  interval_cases t
  · exact co2t0
  · exact co2t1
  · exact co2t2
  · exact co2t3
  · exact co2t4
  · exact co2t5
  · exact co2t6
  · exact co2t7
  · exact co2t8
  · exact co2t9
  · exact co2t10
  · exact co2t11)

def q4 : List (ℕ × ℕ) := pr rt 4
lemma co4_p : pOk 4 q4 = true := by decide +kernel
lemma co4_id : ∀ a ∈ q4, Imp [] a.1 a.2 := by
  intro a ha
  unfold q4 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t0_res : chk [] q4 4 10 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 0 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t0_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t1_res : chk [] q4 4 10 1 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 1 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t1_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t2_res : chk [] q4 4 10 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 2 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t2_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t3_res : chk [] q4 4 10 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 3 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t3_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t4_res : chk [] q4 4 10 4 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 4 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t4_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t5_res : chk [] q4 4 10 5 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 5 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t5_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t6_res : chk [] q4 4 10 6 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 6 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t6_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t7_res : chk [] q4 4 10 7 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 7 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t7_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t8_res : chk [] q4 4 10 8 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 8 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t8_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t9_res : chk [] q4 4 10 9 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 9 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t9_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co4t10_res : chk [] q4 4 10 10 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co4t10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q4 4 10 10 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co4t10_res⟩
lemma co4 : Imp [] 4 11 := imp_of (Or.inl rfl) co4_p (by norm_num) co4_id
    (Or.inr fun t ht => by
  interval_cases t
  · exact co4t0
  · exact co4t1
  · exact co4t2
  · exact co4t3
  · exact co4t4
  · exact co4t5
  · exact co4t6
  · exact co4t7
  · exact co4t8
  · exact co4t9
  · exact co4t10)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co8_alignment : cofactorAlignment 4 8 0x1b300000000000000000000000000000000000000000006c40001ae00000000000000000000000000000000000002800000003580180000000000000000000000000000000680321a50d1809c33a3590000000000000000000000000000000000000000000000000199000000000000000000000000000000000000000000064c0000170000000000000000000000000000000002fc03d00000002f403c000000000000000000000000000aa000c2a003b09f80740744210000000000000000000000000001c000000011c000046422c35800000000000000000000000000000043804c10c0848d5c20c3fb0000000000000000000000000000000001f80f907b03cc6ac3e80000000000000000000000000006b034c0360c11aa8f2078a3bd0000000000000000000000000001800bc05c0b4000004c15c3a300000000000000000000000000015827c0180140458e000f83760000000000000000000000000000400086a235f01500846b8350000000000000000000000000001a70d787223831ad8d346e234c 1 = true := by decide +kernel

lemma co8 : Imp [] 8 11 :=
  imp_by_cofactor_symmetry (by decide +kernel) co8_alignment (by decide +kernel) (by decide +kernel) co4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co16_alignment : cofactorAlignment 2 16 0xa000000000000000006c40001ae0000000000000000000000000000000000000000000000000000000000000000500000fc0001a700000680321a50d1809c33a34100000000000000000000000000000000000000000000000000000000000000000000065c0001950000000000000000064c000017000000000000000000000000000000000000000000000000000000005a400016700000880000040aa000c2a003b09f807407442100000000000000000000000000000000000000000000000000000048000000037000044c020036000043804c10c0848cfc20c3fb000000000000000000000000000000000000000000000000000000000d402c0ef07683a81d00d906b034c0360c119e8f2078a3bd000000000000000000000000000000000000000000000000000000080b40000a80078cec058398015827c0180140458e000f837600000000000000000000000000000000000000000000000000000118ce00a43470278d1005233719b0e4c68c3831a1909466a334 2 = true := by decide +kernel

lemma co16 : Imp [] 16 12 :=
  imp_by_cofactor_symmetry (by decide +kernel) co16_alignment (by decide +kernel) (by decide +kernel) co2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co32_alignment : cofactorAlignment 1 32 0x2000000000000280000000358018000000000000500000fc0001a700000680321a50d1809c33a341000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000182000000000003e00000002fc03d00000002f403c00005a400016700000880000040aa000c2a003b09f80740744210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a800000000e00000002040ff00000001f80f907b03cc67c3e800000d402c0ef07683a81d00d906b034c0360c119e8f2078a3bd00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012004801a33a01280180e0365004000867235f01500846b83500118ce00a43470278d1005233719b0d7868c3b61a18d3466a334 1 = true := by decide +kernel

lemma co32 : Imp [] 32 11 :=
  imp_by_cofactor_symmetry (by decide +kernel) co32_alignment (by decide +kernel) (by decide +kernel) co1

def q64 : List (ℕ × ℕ) := pr rt 64
lemma co64_p : pOk 64 q64 = true := by decide +kernel
lemma co64_id : ∀ a ∈ q64, Imp [] a.1 a.2 := by
  intro a ha
  unfold q64 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
def co64t0_cov : List (ℕ × ℕ) := [(0x0, 1), (0x1, 0), (0x2, 0), (0x40, 0), (0x80, 0), (0x400, 0), (0x1000, 0), (0x2000, 0), (0x10000, 0), (0x20000000, 0), (0x40000000, 0), (0x200000000, 0), (0x800000000, 0), (0x4000000000, 0), (0x8000000000, 0), (0x4000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000000000000000000, 0), (0x33dfbfefbfffffffffffffffffffffffffffffffffff359ffecb3c, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch0 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch1 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch2 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch3 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch4 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t0batch5 : rangeCheck (restrictedTest q64 64 0 co64t0_cov) 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co64t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 0 a.1 a.2 = false :=
  restrictedWitness q64 64 0 co64t0_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 0 12 10
      (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 0 4 8
       co64t0batch0
       (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 4 4 4
        co64t0batch1
        co64t0batch2))
      (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 12 4 6
       co64t0batch3
       (@rangeAppend (restrictedTest q64 64 0 co64t0_cov) 16 4 2
        co64t0batch4
        co64t0batch5)))

def co64t1_cov : List (ℕ × ℕ) := [(0x0, 1), (0x1, 0), (0x2, 0), (0x40, 0), (0x80, 0), (0x400, 0), (0x1000, 0), (0x2000, 0), (0x10000, 0), (0x20000000, 0), (0x40000000, 0), (0x200000000, 0), (0x800000000, 0), (0x4000000000, 0), (0x8000000000, 0), (0x4000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000000, 0), (0x80000000000000000000000000000000000000000000000000000, 0), (0x33dfbfefbfffffffffffffffffffffffffffffffffff359ffecb3c, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch0 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch1 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch2 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch3 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch4 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t1batch5 : rangeCheck (restrictedTest q64 64 1 co64t1_cov) 20 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma co64t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 1 a.1 a.2 = false :=
  restrictedWitness q64 64 1 co64t1_cov (by decide +kernel)
    (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 0 12 10
      (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 0 4 8
       co64t1batch0
       (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 4 4 4
        co64t1batch1
        co64t1batch2))
      (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 12 4 6
       co64t1batch3
       (@rangeAppend (restrictedTest q64 64 1 co64t1_cov) 16 4 2
        co64t1batch4
        co64t1batch5)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t2_res : chk [] q64 64 11 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 2 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t2_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t3_res : chk [] q64 64 11 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 3 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t3_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t4_res : chk [] q64 64 11 4 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 4 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t4_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t5_res : chk [] q64 64 11 5 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 5 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t5_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t6_res : chk [] q64 64 11 6 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 6 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t6_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t7_res : chk [] q64 64 11 7 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 7 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t7_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t8_res : chk [] q64 64 11 8 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 8 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t8_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t9_res : chk [] q64 64 11 9 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 9 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t9_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t10_res : chk [] q64 64 11 10 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 10 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t10_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co64t11_res : chk [] q64 64 11 11 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co64t11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q64 64 11 11 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co64t11_res⟩
lemma co64 : Imp [] 64 12 := imp_of (Or.inl rfl) co64_p (by norm_num) co64_id
    (Or.inr fun t ht => by
  interval_cases t
  · exact co64t0
  · exact co64t1
  · exact co64t2
  · exact co64t3
  · exact co64t4
  · exact co64t5
  · exact co64t6
  · exact co64t7
  · exact co64t8
  · exact co64t9
  · exact co64t10
  · exact co64t11)

def q128 : List (ℕ × ℕ) := pr rt 128
lemma co128_p : pOk 128 q128 = true := by decide +kernel
lemma co128_id : ∀ a ∈ q128, Imp [] a.1 a.2 := by
  intro a ha
  unfold q128 pr at ha
  exact ir a (List.mem_of_mem_filter ha)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t0_res : chk [] q128 128 8 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 0 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t0_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t1_res : chk [] q128 128 8 1 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 1 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t1_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t2_res : chk [] q128 128 8 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 2 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t2_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t3_res : chk [] q128 128 8 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 3 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t3_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t4_res : chk [] q128 128 8 4 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 4 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t4_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t5_res : chk [] q128 128 8 5 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 5 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t5_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t6_res : chk [] q128 128 8 6 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 6 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t6_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t7_res : chk [] q128 128 8 7 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 7 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t7_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem co128t8_res : chk [] q128 128 8 8 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma co128t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] q128 128 8 8 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using co128t8_res⟩
lemma co128 : Imp [] 128 9 := imp_of (Or.inl rfl) co128_p (by norm_num) co128_id
    (Or.inr fun t ht => by
  interval_cases t
  · exact co128t0
  · exact co128t1
  · exact co128t2
  · exact co128t3
  · exact co128t4
  · exact co128t5
  · exact co128t6
  · exact co128t7
  · exact co128t8)

def rt1 : List (ℕ × ℕ) := [(1, 11), (2, 12), (4, 11), (8, 11), (16, 12), (32, 11), (64, 12), (128, 9)]
lemma i1 : ∀ a ∈ rt1, Imp [] a.1 a.2 := by
  intro a ha
  simp only [rt1, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact co1
  · exact co2
  · exact co4
  · exact co8
  · exact co16
  · exact co32
  · exact co64
  · exact co128
def pins4 : List (ℕ × ℕ) := [(525, 1), (533, 2), (537, 3), (540, 2), (549, 3), (553, 3), (556, 1), (561, 3), (564, 3), (568, 2), (581, 1), (585, 3), (588, 3), (593, 2), (596, 3), (600, 3), (609, 1), (612, 3), (616, 1), (624, 2), (645, 2), (649, 3), (652, 2), (657, 4), (660, 4), (664, 4), (673, 3), (676, 3), (680, 2), (688, 4), (705, 2), (708, 3), (712, 3), (720, 4), (736, 2), (780, 2), (788, 2), (792, 3), (804, 2), (808, 3), (816, 3), (836, 3), (840, 2), (848, 2), (864, 2), (900, 2), (904, 3), (912, 3), (928, 3), (960, 2), (1545, 3), (1553, 2), (1560, 2), (1569, 2), (1576, 2), (1584, 3), (1601, 2), (1608, 2), (1616, 3), (1632, 3), (1665, 2), (1672, 2), (1680, 3), (1696, 3), (1728, 3), (1800, 3), (1808, 3), (1824, 3), (1856, 3), (1920, 3), (2565, 2), (2577, 3), (2580, 2), (2593, 2), (2596, 3), (2608, 2), (2625, 3), (2628, 2), (2640, 3), (2656, 2), (2689, 3), (2692, 2), (2704, 3), (2720, 2), (2752, 3), (3585, 3), (3600, 3), (3616, 3), (3648, 3), (3712, 3), (4103, 2), (4107, 3), (4109, 1), (4110, 2), (4131, 3), (4133, 3), (4134, 3), (4137, 3), (4138, 2), (4140, 1), (4163, 2), (4165, 1), (4166, 3), (4169, 3), (4170, 3), (4172, 3), (4193, 1), (4194, 2), (4196, 3), (4200, 1), (4227, 4), (4229, 2), (4230, 4), (4233, 3), (4234, 4), (4236, 2), (4257, 3), (4258, 4), (4260, 3), (4264, 2), (4289, 2), (4290, 4), (4292, 3), (4296, 3), (4320, 2), (4358, 2), (4362, 3), (4364, 2), (4386, 3), (4388, 2), (4392, 3), (4418, 2), (4420, 3), (4424, 2), (4448, 2), (4482, 3), (4484, 2), (4488, 3), (4512, 3), (4544, 2), (5123, 2), (5129, 3), (5130, 2), (5153, 2), (5154, 3), (5160, 2), (5185, 2), (5186, 3), (5192, 2), (5216, 3), (5249, 2), (5250, 3), (5256, 2), (5280, 3), (5312, 3), (5378, 3), (5384, 3), (5408, 3), (5440, 3), (5504, 3), (6147, 3), (6149, 2), (6150, 2), (6177, 2), (6178, 2), (6180, 3), (6209, 3), (6210, 3), (6212, 2), (6240, 2), (6273, 3), (6274, 3), (6276, 2), (6304, 2), (6336, 3), (7169, 3), (7170, 3), (7200, 3), (7232, 3), (7296, 3), (8709, 3), (8713, 2), (8716, 2), (8721, 3), (8724, 3), (8728, 2), (8769, 2), (8772, 2), (8776, 3), (8784, 2), (8833, 3), (8836, 3), (8840, 2), (8848, 3), (8896, 2), (10753, 3), (10756, 3), (10768, 3), (10816, 3), (10880, 3), (12291, 3), (12293, 3), (12294, 3), (12297, 2), (12298, 2), (12300, 2), (12353, 2), (12354, 2), (12356, 2), (12360, 3), (12417, 3), (12418, 3), (12420, 3), (12424, 2), (12480, 2), (14337, 3), (14338, 3), (14340, 3), (14400, 3), (14464, 3), (16391, 3), (16395, 3), (16397, 5), (16398, 5), (16403, 3), (16405, 3), (16406, 5), (16409, 3), (16410, 5), (16412, 5), (16419, 3), (16421, 5), (16422, 3), (16425, 5), (16426, 3), (16428, 5), (16433, 3), (16434, 3), (16436, 3), (16440, 3), (16515, 1), (16517, 2), (16518, 2), (16521, 2), (16522, 2), (16524, 3), (16529, 1), (16530, 3), (16532, 2), (16536, 2), (16545, 3), (16546, 1), (16548, 2), (16552, 2), (16560, 1), (16646, 2), (16650, 2), (16652, 3), (16658, 3), (16660, 2), (16664, 2), (16674, 2), (16676, 3), (16680, 3), (16688, 2), (16770, 2), (16772, 3), (16776, 3), (16784, 2), (16800, 3), (16901, 2), (16905, 2), (16908, 3), (16913, 2), (16916, 3), (16920, 3), (16929, 3), (16932, 2), (16936, 2), (16944, 2), (17025, 2), (17028, 3), (17032, 3), (17040, 3), (17056, 2), (17156, 3), (17160, 3), (17168, 3), (17184, 3), (17280, 3), (20483, 2), (20485, 2), (20486, 3), (20489, 2), (20490, 3), (20492, 3), (20513, 3), (20514, 2), (20516, 2), (20520, 2), (20609, 2), (20610, 3), (20612, 3), (20616, 3), (20640, 2), (20738, 3), (20740, 3), (20744, 3), (20768, 3), (20864, 3), (24579, 2), (24581, 3), (24582, 2), (24585, 3), (24586, 2), (24588, 3), (24593, 2), (24594, 3), (24596, 2), (24600, 2), (24705, 3), (24706, 2), (24708, 3), (24712, 3), (24720, 2), (25089, 3), (25092, 3), (25096, 3), (25104, 3), (25216, 3), (28673, 3), (28674, 3), (28676, 3), (28680, 3), (28800, 3), (49155, 3), (49157, 3), (49158, 3), (49161, 3), (49162, 3), (49164, 3), (49169, 3), (49170, 3), (49172, 3), (49176, 3), (49185, 3), (49186, 3), (49188, 3), (49192, 3), (49200, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins4_ok : pins4.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma pins4_I : ∀ e ∈ pins4, Imp [] e.1 e.2 := okAll (T := []) pins4_ok (by simp)

def pins3 : List (ℕ × ℕ) := [(517, 3), (521, 4), (524, 3), (529, 5), (532, 5), (536, 5), (545, 4), (548, 4), (552, 3), (560, 5), (577, 3), (580, 4), (584, 4), (592, 5), (608, 3), (641, 5), (644, 5), (648, 5), (656, 7), (672, 5), (704, 5), (772, 3), (776, 4), (784, 4), (800, 4), (832, 3), (896, 4), (1537, 3), (1544, 3), (1552, 4), (1568, 4), (1600, 4), (1664, 4), (1792, 4), (2561, 4), (2564, 3), (2576, 4), (2592, 3), (2624, 4), (2688, 4), (3584, 4), (4099, 5), (4101, 3), (4102, 5), (4105, 4), (4106, 5), (4108, 3), (4129, 4), (4130, 5), (4132, 4), (4136, 3), (4161, 3), (4162, 5), (4164, 4), (4168, 4), (4192, 3), (4225, 5), (4226, 7), (4228, 5), (4232, 5), (4256, 5), (4288, 5), (4354, 4), (4356, 3), (4360, 4), (4384, 4), (4416, 3), (4480, 4), (5121, 3), (5122, 4), (5128, 3), (5152, 4), (5184, 4), (5248, 4), (5376, 4), (6145, 4), (6146, 4), (6148, 3), (6176, 3), (6208, 4), (6272, 4), (7168, 4), (8705, 4), (8708, 4), (8712, 3), (8720, 4), (8768, 3), (8832, 4), (10752, 4), (12289, 4), (12290, 4), (12292, 4), (12296, 3), (12352, 3), (12416, 4), (14336, 4), (16387, 4), (16389, 6), (16390, 6), (16393, 6), (16394, 6), (16396, 8), (16401, 4), (16402, 6), (16404, 6), (16408, 6), (16417, 6), (16418, 4), (16420, 6), (16424, 6), (16432, 4), (16513, 3), (16514, 3), (16516, 4), (16520, 4), (16528, 3), (16544, 3), (16642, 3), (16644, 4), (16648, 4), (16656, 3), (16672, 4), (16768, 4), (16897, 3), (16900, 4), (16904, 4), (16912, 4), (16928, 3), (17024, 4), (17152, 4), (20481, 3), (20482, 4), (20484, 4), (20488, 4), (20512, 3), (20608, 4), (20736, 4), (24577, 4), (24578, 3), (24580, 4), (24584, 4), (24592, 3), (24704, 4), (25088, 4), (28672, 4), (49153, 4), (49154, 4), (49156, 4), (49160, 4), (49168, 4), (49184, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins3_ok : pins3.all (fun e => okE [] (pr pins4 e.1) e) = true := by decide +kernel
lemma pins3_I : ∀ e ∈ pins3, Imp [] e.1 e.2 := okAll (T := pins4) pins3_ok pins4_I

def pins2 : List (ℕ × ℕ) := [(513, 6), (516, 6), (520, 6), (528, 8), (544, 6), (576, 6), (640, 8), (768, 5), (1536, 5), (2560, 5), (4097, 6), (4098, 8), (4100, 6), (4104, 6), (4128, 6), (4160, 6), (4224, 8), (4352, 5), (5120, 5), (6144, 5), (8704, 5), (12288, 5), (16385, 7), (16386, 7), (16388, 9), (16392, 9), (16400, 7), (16416, 7), (16512, 5), (16640, 5), (16896, 5), (20480, 5), (24576, 5), (49152, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins2_ok : pins2.all (fun e => okE [] (pr (pins3 ++ pins4) e.1) e) = true := by decide +kernel
lemma pins2_I : ∀ e ∈ pins2, Imp [] e.1 e.2 := okAll (T := (pins3 ++ pins4)) pins2_ok (apI pins3_I pins4_I)

def pins1 : List (ℕ × ℕ) := [(512, 9), (4096, 9), (16384, 10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pins1_ok : pins1.all (fun e => okE [] (pr (pins2 ++ (pins3 ++ pins4)) e.1) e) = true := by decide +kernel
lemma pins1_I : ∀ e ∈ pins1, Imp [] e.1 e.2 := okAll (T := (pins2 ++ (pins3 ++ pins4))) pins1_ok (apI pins2_I (apI pins3_I pins4_I))

def pinsAll : List (ℕ × ℕ) := (pins1 ++ (pins2 ++ (pins3 ++ pins4)))
lemma pinsAll_I : ∀ e ∈ pinsAll, Imp [] e.1 e.2 := (apI pins1_I (apI pins2_I (apI pins3_I pins4_I)))
def pinsSelected : List (ℕ × ℕ) := pinsAll.filter (fun e => e.2 ≥ 7)
lemma pinsSelected_I : ∀ e ∈ pinsSelected, Imp [] e.1 e.2 := by
  intro e he
  unfold pinsSelected at he
  exact pinsAll_I e (List.mem_of_mem_filter he)

def rootBounds : List (ℕ × ℕ) := ((rt1 ++ rt).filter (fun a => a.2 ≥ 7)) ++ pinsSelected
lemma rootBounds_I : ∀ a ∈ rootBounds, Imp [] a.1 a.2 := by
  apply apI _ pinsSelected_I
  intro a ha
  exact apI i1 ir a (List.mem_of_mem_filter ha)
lemma rootBounds_p : pOk 0 rootBounds = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root0_res : chk [] rootBounds 0 13 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 0 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root0_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root1_res : chk [] rootBounds 0 13 1 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 1 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root1_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root2_res : chk [] rootBounds 0 13 2 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 2 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root2_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root3_res : chk [] rootBounds 0 13 3 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 3 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root3_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root4_res : chk [] rootBounds 0 13 4 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 4 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root4_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root5_res : chk [] rootBounds 0 13 5 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 5 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root5_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root6_res : chk [] rootBounds 0 13 6 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 6 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root6_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root7_res : chk [] rootBounds 0 13 7 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 7 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root7_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root8_res : chk [] rootBounds 0 13 8 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 8 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root8_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root9_res : chk [] rootBounds 0 13 9 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 9 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root9_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root10_res : chk [] rootBounds 0 13 10 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 10 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root10_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root11_res : chk [] rootBounds 0 13 11 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 11 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root11_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root12_res : chk [] rootBounds 0 13 12 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root12 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 12 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root12_res⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root13_res : chk [] rootBounds 0 13 13 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel
lemma root13 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ a ∈ M, chk [] rootBounds 0 13 13 a.1 a.2 = false :=
  ⟨[(FF,1)], ffull, by
    intro a ha
    have he : a = (FF,1) := by simpa using ha
    simpa [he] using root13_res⟩
lemma iroot : Imp [] 0 14 := imp_ts (Or.inl rfl) rootBounds_p (by norm_num) rootBounds_I (fun t ht => by
  interval_cases t
  · exact root0
  · exact root1
  · exact root2
  · exact root3
  · exact root4
  · exact root5
  · exact root6
  · exact root7
  · exact root8
  · exact root9
  · exact root10
  · exact root11
  · exact root12
  · exact root13)

def sampleWire (i : ℕ) : ℕ := rawP0.getD i 0 &&& mz 0

lemma sampleWire_ok (i : Fin 8) : sampleWire i.val ∈ WZ [] 0 := by
  refine ⟨rawP0.getD i.val 0,?_,rfl⟩
  apply List.mem_append_left
  have hh : i.val < rawP0.length := by simpa [rawP_len0] using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hh]
  exact List.getElem_mem _

def binaryRepresentatives : List (ℕ × ℕ) :=
  [(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,2),(1,4),(1,6),(1,7),(2,3),(2,6),(2,7),(6,7)]

def unaryRepresentatives : List ℕ := [0,1,2,6,7]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma binaryOrbit : ∀ i j : Fin 8, i ≠ j →
    ∃ a : Fin 4, ∃ p ∈ binaryRepresentatives,
      ((permuted a i).val = p.1 ∧ (permuted a j).val = p.2) ∨
      ((permuted a i).val = p.2 ∧ (permuted a j).val = p.1) := by decide +kernel

lemma unaryOrbit : ∀ i : Fin 8, ∃ a : Fin 4, (permuted a i).val ∈ unaryRepresentatives := by decide +kernel

def BinaryCertificates (Q : List (ℕ × ℕ)) : Prop :=
    ∀ p ∈ binaryRepresentatives, ∃ H : ℕ,
      hb H (sampleWire p.1 + sampleWire p.2) = true ∧ chk [] Q 0 14 1 H 0 = false

def UnaryCertificates : Prop :=
    ∀ (i : Fin 8), i.val ∈ unaryRepresentatives →
    ∀ (k : ℕ), k ≤ 13 →
    ∀ S : Finset ℕ, (S : Set ℕ) ⊆ insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)) →
      Live Z0 (mz 0) (tz 0) k 0 S → False

lemma fullLower (lower : Imp [] 0 14) {k : ℕ} (hk : k < 14)
    (hl : Sol Z0 fullMask fullTarget k (C fullMask fullStock)) : False :=
  lower k hk ((hl.mapSignals (pull 0) (pull_target 0) (pull_neg 0) (pull_op 0)).mono le_rfl (pull_initial 0))

set_option maxHeartbeats 0 in
lemma projectBinary {Q : List (ℕ × ℕ)} (pQ : pOk 0 Q = true)
    (lowerQ : ∀ e ∈ Q, Imp [] e.1 e.2) (lower : Imp [] 0 14)
    (certs : BinaryCertificates Q)
    {d : Bool} {i j : Fin 8} (hij : i ≠ j) (U : Finset ℕ) (hU : (U : Set ℕ) ⊆ C fullMask fullStock)
    (tail : Live Z0 fullMask fullTarget 13 1 (insert (op d (fullWire i) (fullWire j)) U)) :
    False := by
  obtain ⟨a,p,hp,hor⟩ := binaryOrbit i j hij
  obtain ⟨H,hhash,hchk⟩ := certs p hp
  let x := sampleWire (permuted a i).val
  let y := sampleWire (permuted a j).val
  let z := op d x y
  have px : pull a (fullWire i) = x := pull_fullWire _ _
  have py : pull a (fullWire j) = y := pull_fullWire _ _
  have pz : pull a (op d (fullWire i) (fullWire j)) = z := by rw [pull_op,px,py]
  have hx : x ∈ WZ [] 0 := sampleWire_ok (permuted a i)
  have hy : y ∈ WZ [] 0 := sampleWire_ok (permuted a j)
  have hash : hb H (x+y) = true := by
    rcases hor with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · simpa only [x,y,hi,hj] using hhash
    · simpa only [x,y,hi,hj,Nat.add_comm] using hhash
  obtain ⟨k,t,ht,hk,V,hV,hLive⟩ := tail.mapSignals (pull a) (pull_target a) (pull_neg a) (pull_op a)
  have kle : k ≤ 13 := by omega
  have lift : (V : Set ℕ) ⊆ insert z (C (mz 0) (WZ [] 0)) := by
    intro u hu
    obtain ⟨w,hw,rfl⟩ := hV hu
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Or.inl pz
    · exact Or.inr (pull_initial a ⟨w, hU hw, rfl⟩)
  have hUsed : z ∈ V := by
    by_contra hz
    refine lower k (by omega) (hLive.sol.mono le_rfl ?_)
    intro u hu
    exact (lift hu).resolve_left (fun eq => hz (eq ▸ hu))
  have hne : x ≠ y := by
    intro eq
    have heq : z = y := by rw [show z=op d x y from rfl,eq,op_self]
    refine lower k (by omega) (hLive.sol.mono le_rfl ?_)
    intro u hu
    rcases lift hu with h | h
    · exact Or.inl (h.trans heq ▸ hy)
    · exact h
  let U' := V.erase z
  let S := insert x (insert y U')
  have hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) := by
    intro u hu
    simp only [S, U', Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hu
    rcases hu with rfl | rfl | ⟨hne,hm⟩
    · exact Or.inl hx
    · exact Or.inl hy
    · exact (lift hm).resolve_left hne
  have hIns : insert z U' = V := Finset.insert_erase hUsed
  have hTail : Live Z0 (mz 0) (tz 0) k t (insert (op d x y) U') := by
    change Live Z0 (mz 0) (tz 0) k t (insert z U')
    rw [hIns]
    exact hLive
  have hNew := Live.bi (d := d) hne (al0 _ _ _) hTail
  have hSize : k = 13 := by
    by_contra hc
    exact lower (k+1) (by omega) (hNew.sol.mono le_rfl hS)
  have hNot : t = 1 := by omega
  subst k
  subst t
  exact imp_of_bi (L := 15) pQ (by decide) lowerQ (by decide) hS hNew hx hy
    ⟨hne,U',rfl,rfl,al0 _ _ _⟩ hTail hash (fun _ h => lower _ h) hchk

lemma projectUnary (certs : UnaryCertificates) {i : Fin 8} (U : Finset ℕ)
    (hU : (U : Set ℕ) ⊆ C fullMask fullStock)
    (tail : Live Z0 fullMask fullTarget 13 0 (insert (fullWire i ^^^ fullMask) U)) : False := by
  obtain ⟨a,ha⟩ := unaryOrbit i
  obtain ⟨k,t,ht,hk,V,hV,hLive⟩ := tail.mapSignals (pull a) (pull_target a) (pull_neg a) (pull_op a)
  have ht : t = 0 := by omega
  subst t
  refine certs (permuted a i) ha k (by omega) V ?_ hLive
  intro u hu
  obtain ⟨w,hw,rfl⟩ := hV hu
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Or.inl (by rw [pull_neg, pull_fullWire]; rfl)
  · exact Or.inr (pull_initial a ⟨w,hU hw,rfl⟩)

set_option maxHeartbeats 0 in
theorem fullExclusion {Q : List (ℕ × ℕ)} (pQ : pOk 0 Q = true)
    (lowerQ : ∀ e ∈ Q, Imp [] e.1 e.2) (lower : Imp [] 0 14)
    (bin : BinaryCertificates Q) (un : UnaryCertificates)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C fullMask fullStock)
    (live : Live Z0 fullMask fullTarget 14 1 S) : False := by
  have min : Min Z0 fullMask fullTarget 14 1 S := ⟨live, fun q hq proof =>
    fullLower lower hq (proof.mono le_rfl (fun x hx => hx.elim (fun a => hS a) Or.inr))⟩
  have hnonzero : fullTarget ≠ 0 := by decide +kernel
  have hnonall : fullTarget ≠ fullMask := by decide +kernel
  obtain ⟨h0,h1⟩ := min.proper fullTarget_mask hnonzero hnonall fun _ hm => fullStock_mask (hS hm)
  have real : ∀ x ∈ S, x ∈ fullStock := by
    intro x hx
    rcases hS hx with hx | hx'
    · exact hx
    · simp at hx'
      rcases hx' with rfl | rfl
      · exact (h0 hx).elim
      · exact (h1 hx).elim
  cases live with
  | @un _ _ a U tail =>
    obtain ⟨i,hi⟩ := fullStock_rows (real a (Finset.mem_insert_self _ _))
    exact projectUnary un U (fun _ hu => hS (Finset.mem_insert_of_mem hu)) (hi ▸ tail)
  | @bi _ _ d a b U hab hal tail =>
    obtain ⟨i,hi⟩ := fullStock_rows (real a (by simp))
    obtain ⟨j,hj⟩ := fullStock_rows (real b (by simp))
    refine projectBinary pQ lowerQ lower bin (d := d) (i := i) (j := j) ?_ U (fun _ hu => hS (by simp [hu])) ?_
    · intro he
      exact hab (hi.trans (he ▸ hj.symm))
    · rw [← hi, ← hj]
      exact tail

def unaryBounds (Q : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  Q.filter fun e =>
    let signal := xw (i,0) &&& mz e.1
    Nat.beq signal 0 || Nat.beq signal (mz e.1)

lemma unary_restriction {Q : List (ℕ × ℕ)} (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (i : ℕ) : ∀ e ∈ unaryBounds Q i, Imp [(i,0)] e.1 e.2 := by
  intro e he k hk hSol
  obtain ⟨inside, hconst⟩ := List.mem_filter.mp he
  simp only [Bool.or_eq_true, Nat.beq_eq] at hconst
  apply hQ e inside k hk
  refine hSol.mono le_rfl ?_
  rintro r (hr | hr)
  · obtain ⟨w,hw,rfl⟩ := hr
    simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩
    · rcases hconst with h | h
      · rw [h]
        exact Or.inr (Set.mem_insert _ _)
      · rw [h]
        exact Or.inr (Set.mem_insert_of_mem _ rfl)
  · exact Or.inr hr

lemma unary_augmented {i : Fin 8}
    (heq : xw (i.val,0) &&& mz 0 = sampleWire i.val ^^^ mz 0) :
    C (mz 0) (WZ [(i.val,0)] 0) ⊆ insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)) := by
  rintro r (hr | hr)
  · obtain ⟨w,hw,rfl⟩ := hr
    simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩)
    · exact Or.inl heq
  · exact Or.inr (Or.inr hr)

lemma unary_ready {i : Fin 8}
    (heq : xw (i.val,0) &&& mz 0 = sampleWire i.val ^^^ mz 0) :
    insert (sampleWire i.val ^^^ mz 0) (C (mz 0) (WZ [] 0)) ⊆ C (mz 0) (WZ [(i.val,0)] 0) := by
  rintro r (rfl | (hr | hr))
  · exact Or.inl ⟨xw (i.val,0),List.mem_append_right _ (by simp),heq.symm⟩
  · obtain ⟨w,hw,rfl⟩ := hr
    simp [rawL] at hw
    exact Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩
  · exact Or.inr hr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def unaryConstant (i z : ℕ) : Bool :=
  let signal := xw (i,0) &&& mz z
  signal == 0 || signal == mz z

def unaryCharge (i : ℕ) (e : ℕ × ℕ) : ℕ × ℕ :=
  if unaryConstant i e.1 then e else (e.1,e.2 - 1)

def unaryBoundsStrong (Q : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  Q.map (unaryCharge i)

lemma unaryCharge_fst (i : ℕ) (e : ℕ × ℕ) : (unaryCharge i e).1 = e.1 := by
  by_cases h : unaryConstant i e.1 = true <;> simp [unaryCharge,h]

lemma unary_pos_strong (Q : List (ℕ × ℕ)) (hp : pOk 0 Q = true) (i : ℕ) :
    pOk 0 (unaryBoundsStrong Q i) = true := by
  simp only [pOk, Bool.and_eq_true, List.all_eq_true] at hp ⊢
  refine ⟨hp.1,?_⟩
  intro e he
  obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp he
  simp only [unaryCharge_fst]
  exact hp.2 original hOriginal

lemma unary_augmented_at {i : Fin 8} (z : ℕ)
    (heq : xw (i.val,0) &&& mz z = (rawP0.getD i.val 0 &&& mz z) ^^^ mz z) :
    C (mz z) (WZ [(i.val,0)] z) ⊆
      insert ((rawP0.getD i.val 0 &&& mz z) ^^^ mz z) (C (mz z) (WZ [] z)) := by
  rintro r (hr | hr)
  · obtain ⟨w,hw,rfl⟩ := hr
    simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w,List.mem_append_left _ hw,rfl⟩)
    · exact Or.inl heq
  · exact Or.inr (Or.inr hr)

set_option maxHeartbeats 0 in
lemma unary_restriction_strong {Q : List (ℕ × ℕ)} (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (i : Fin 8)
    (hEq : ∀ e ∈ Q, xw (i.val,0) &&& mz e.1 = (rawP0.getD i.val 0 &&& mz e.1) ^^^ mz e.1) :
    ∀ e ∈ unaryBoundsStrong Q i.val, Imp [(i.val,0)] e.1 e.2 := by
  intro e he
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
  by_cases hc : unaryConstant i.val original.1 = true
  · simp only [unaryCharge,hc,ite_true]
    apply unary_restriction hQ i.val original
    apply List.mem_filter.mpr
    exact ⟨ho,hc⟩
  · have hoff := Bool.eq_false_iff.mpr hc
    simp only [unaryCharge,hoff,Bool.false_eq_true,ite_false]
    intro k hk hs
    have raw : rawP0.getD i.val 0 &&& mz original.1 ∈ C (mz original.1) (WZ [] original.1) := by
      exact Or.inl ⟨rawP0.getD i.val 0,List.mem_append_left _ (rawP_getD_mem i),rfl⟩
    exact hQ original ho (k+1) (by omega) (.un raw (hs.mono le_rfl (unary_augmented_at _ (hEq original ho))))

set_option maxHeartbeats 0 in
theorem build_unary_strong_certificates {Q : List (ℕ × ℕ)}
    (pQ : pOk 0 Q = true) (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (lower : Imp [] 0 14)
    (hSix : ∀ i ∈ unaryRepresentatives, (i,0) ∈ six)
    (hEq : ∀ i : Fin 8, xw (i.val,0) &&& mz 0 = sampleWire i.val ^^^ mz 0)
    (hCut : ∀ i : Fin 8, i.val ∈ unaryRepresentatives →
      ∀ e ∈ Q, xw (i.val,0) &&& mz e.1 = (rawP0.getD i.val 0 &&& mz e.1) ^^^ mz e.1)
    (hChk : ∀ i ∈ unaryRepresentatives, chk [(i,0)] (unaryBoundsStrong Q i) 0 13 0 FF 1 = false) :
    UnaryCertificates := by
  intro i hi k hk S hS hLive
  have raw : sampleWire i.val ∈ C (mz 0) (WZ [] 0) := Or.inl (sampleWire_ok i)
  by_cases hm : k < 13
  · exact lower (k+1) (by omega) (.un raw (hLive.sol.mono le_rfl hS))
  have kEq : k = 13 := by omega
  subst k
  refine imp_of_live (L := 14) (Or.inr ⟨(i.val,0),hSix _ hi,rfl,lower⟩)
    (unary_pos_strong Q pQ _) (by decide) (unary_restriction_strong hQ i (hCut i hi)) (by decide)
    (hS.trans (unary_ready (hEq i))) hLive ?_ (Or.inr (one (hChk _ hi)))
  intro q hq hSol
  exact lower (q+1) (by omega) (.un raw (hSol.mono le_rfl (unary_augmented (hEq i))))

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
      cases ha : Nat.beq (Nat.mul da dc) 0
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
      (bif Nat.ble v.length 1 then true else
        tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y)) := by
  change Bool.rec (motive := fun _ => Bool)
      (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y) true
          (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1) = _
  simp only [bR]

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

def rootPreparedWords : List W := [
  ⟨0x7fffefc0000000000000000000000000000000000000000000000000000000000000000000000000084a2400300000180000c00006000300060000000000000000040000040000000000008000200000000200000200000000000000000007ff80fdfc007f0010fe0021fc004203f80087f0010847f0010fe002109fc004211fc004211091f80ad6ab6aabfff555fffaafffd57ffebfff7ffe00000000000000000000000000000000000000000000000000000000fc000185278004b9, 0x42000000004010000008000000000042000000000000000000000000000800000000, 0x0, 0x42000000004010000008000000000042000000000000000000000000000800000000, 3⟩,
  ⟨0x7fffe01ffff7fffdeffffbdffff7bd80000000000000000000000000000000000000000000000000ad6ab6002f0000178000bc0005e002f005e0096d256c524d8297e00927e00000000000f8003e00000003e00003e0000000000000000007e0600103f040fc1e81f83d03f07bd80700000e0080000e00801c010000380210803802108000060ad6ab60000000000000000000000000000000d6db56d5b6daad7ffedb7ffe0000000000000000000000000000000083e001c11f614e20, 0x421080000000108421080000000000000000000040000000, 0x800108421080000040000000000000000000000000000000000000000000000000000, 0x800108421080000040000421080000000108421080000000000000000000040000000, 3⟩,
  ⟨0x1ffff7fffde00000000000003fffef7fffdef7000000000000000000000000000000000000a40000aa8ce0000660003300019800cc01980d69b548000000031800031809a2692510670119c00000019800019800000000000000000410188183cc60f31e410600820c010304f8f609f1ef7401c00803808810070100100701084809018ac0000aabfff0000000000000000000000000d6db56c00000000000000000dab6db55afffdbfff00000000000000003dff840d09b9e83, 0x100000000000000000400004200000100000004210840000000000000002000000, 0x0, 0x100000000000000000400004200000100000004210840000000000000002000000, 3⟩,
  ⟨0x1ffff000000ffffbc00000003fffef000000007fffdeffffbdec0000000000000000000000812000a00a9855455c002ac0015600ab01560d4c00015b690002960002960d2b4c000054c015304d34915700015600000000000000000208044143c2108080a1e13c4102200284e4f1010804030939e61273dec800c0080800c0800440804816000a00000555fff8000000000000000000d6c00015b6d8000000000000dab6c0000000000006db6dbfff000000731fc533d12e69c4, 0x2008000000000800008020000010840008000004000002108400000000000100000, 0x40000000004200002000000000000000000000000000000000000000000000000000, 0x42008000004200802008020000010840008000004000002108400000000000100000, 3⟩,
  ⟨0x7fffc0000001ffff7800000007fffc0f000000000000001ffff03c1ffff7801ec00002000900885460002a322152940a98854e0a9802184600004a2c1494d814980802184582a318a8c208248a8e618a9400000000000000000410408088242f0800421050ba2780010442429c80f0020284040304244a4e03c0294e7801ec01042000b008800000000022000140000bfff00000618460000da2c0000d80000180618458000180006186dbfff6180008333acbef42c83ce, 0x40000001000200000008020000010802000001000000800008001004010000000020, 0x2000000000010800100000000000000000000000000000000000000000000000000, 0x42000001000210800108020000010802000001000000800008001004010000000020, 3⟩,
  ⟨0xffff81ffff03c00000000000000000000ffff81e000000001ffff03c1e1c00001008200030a044189000c49106288314062c0040024430c0210c24c30c280080400421850861604161862424862600000000000000000208a04044501114283e28107a503c0082a101054211010542432e81e004130844255b03c1e1c08a0100860000000440000000011000080007ffe00c006c430c0210000c300000280c05420001bfff0c36180006dbfff05095e78da63bb83, 0x80000000000000084200000000000080000040000400080210000000001, 0x0, 0x80000000000000084200000000000080000040000400080210000000001, 3⟩,
  ⟨0x3fffe07fffde007fffde00000001ffff7bdc000000000000000000008a00d45000722a03b0001d000e801d04009001080028401d80001d0da001b50006a001a869a0001c84901d800000000000000001044220222108484810909020c1109246e2048dc5e0028d35e10848040634b7bdc420300402044420008008a00005000002afffc0000000000000c01b00158002ad7ffe000000da001b500000000006db0000006dbfffc2fe323dd067eef3, 0x800000400000000000000001084010000000400000200002000021080000000008000, 0x0, 0x800000400000000000000001084010000000400000200002000021080000000008000, 3⟩,
  ⟨0x7fffc0ffffbc01ffff7801ffff7bdc00000000000000001e45001b2800e95007c003c007800000010120280007449007c40900904a00f8003c6c06c006c6c0074000000000000000008230101118042604084c081038084821904042a042224bb0049763c0052ea780031ea7bdc00023000020000000045000028000157ffe00000000100050103602800000db7ffec0b01b05afffc00006c06c00006c00002bbde9588e747baf, 0x800000020000000000000401000200800000020000010000100020004200000000400, 0x0, 0x800000020000000000000401000200800000020000010000100020004200000000400, 3⟩]
def rootPreparedMask : ℕ := 0x7fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfff00000000000000007fffefdffff7fffdeffffbdffff7bdbfffef7fffdef77fffdeffffbdedffff7bddffff7bddeddffead6ab6aabfff555fffaafffd57ffebfff7ffed6db56d5b6daad7ffedb7ffedab6db55afffdbfff6db6dbfff6dbfffffffffffffffffff
def rootPreparedSlots : ℕ := 0x8421084210842108421084210842108421084210842108421084210842108421084210
def rootPreparedBudget : ℕ := 0xb5ef7bd6b7bdad6b52b5bdaf6b5ef7bdef5ad6b5adad5b5ad6a5ad6adad6aca729ce53

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

noncomputable def opening_0_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_0_and_complete : initialBinary 0x200000000000000000000000000000000000000000 false (frontierMissing opening_0_and) = false := by decide +kernel

noncomputable def opening_0_or : List (ℕ × List W) := [⟨0x9ce55ace74a527294e929ce7394e739d6939ce72952939ce948ce9394e72a465194a11, rootWithGate 4 5 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_0_or_complete : initialBinary 0x200000000000000000000000000000000000000000 true (frontierMissing opening_0_or) = false := by decide +kernel

noncomputable def opening_1_and : List (ℕ × List W) := [⟨0x8d295ace359d294a4e94a46918ca54956b39ce338d291a4a9294a548ca52a465194230, rootWithGate 5 7 255 false⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_1_and_complete : initialBinary 0x10000000000000000000000000000000000000000 false (frontierMissing opening_1_and) = false := by decide +kernel

noncomputable def opening_1_or : List (ℕ × List W) := [⟨0x95295ace55a5294a4e94a4a9294e549d6b39ce5395292a4e9394e7494e53a465194631, rootWithGate 5 7 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_1_or_complete : initialBinary 0x10000000000000000000000000000000000000000 true (frontierMissing opening_1_or) = false := by decide +kernel

noncomputable def opening_2_and : List (ℕ × List W) := [⟨0x8d295ac6759d294a4e94a4e918ca52a56b39c6738d253a4a5494a528d252a465184a30, rootWithGate 5 6 255 false⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_2_and_complete : initialBinary 0x400000000000000000000000000000000000000000000000 false (frontierMissing opening_2_and) = false := by decide +kernel

noncomputable def opening_2_or : List (ℕ × List W) := [⟨0x95295aca75a5294a4e94a4e928ca73a56b39ca7395273a4e7494e738d273a46518ca31, rootWithGate 5 6 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_2_or_complete : initialBinary 0x400000000000000000000000000000000000000000000000 true (frontierMissing opening_2_or) = false := by decide +kernel

noncomputable def opening_3_and : List (ℕ × List W) := [⟨0x9d293ace759d294a4e94a46938ca54a56b19ce738ca5194a9494a948d252a461194a30, rootWithGate 2 5 255 false⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_3_and_complete : initialBinary 0x10000000000000000 false (frontierMissing opening_3_and) = false := by decide +kernel

noncomputable def opening_3_or : List (ℕ × List W) := [⟨0x9d294ace75a5294a4e94a4a9394a54a56b29ce7394e729ca9494e9495273a463194a31, rootWithGate 2 5 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_3_or_complete : initialBinary 0x10000000000000000 true (frontierMissing opening_3_or) = false := by decide +kernel

noncomputable def opening_4_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_4_and_complete : initialBinary 0x20000000000000 false (frontierMissing opening_4_and) = false := by decide +kernel

noncomputable def opening_4_or : List (ℕ × List W) := [⟨0x8d2939c6339d294a4694a4a728ce74a56b294a528d293a4e9494e9495273a425194a31, rootWithGate 1 5 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_4_or_complete : initialBinary 0x20000000000000 true (frontierMissing opening_4_or) = false := by decide +kernel

noncomputable def opening_5_and : List (ℕ × List W) := [⟨0x9ca55ace759ca92a4e9494e938ca54a4e739ce738d293a4a9494a948d2529465194a30, rootWithGate 0 5 255 false⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_5_and_complete : initialBinary 0x100000000000000000000000 false (frontierMissing opening_5_and) = false := by decide +kernel

noncomputable def opening_5_or : List (ℕ × List W) := [⟨0x9ce75ace75a4e93a4e949ce9394e74a52939ce7395293a4e9494e94952739c65194a31, rootWithGate 0 5 255 true⟩, ⟨0x8ce539c6339d272946929ca52952939d69294a51952939d2948d2939ce93a425194a12, rootWithGate 1 4 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_5_or_complete : initialBinary 0x100000000000000000000000 true (frontierMissing opening_5_or) = false := by decide +kernel

noncomputable def opening_6_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_6_and_complete : initialBinary 0x80000000000000000000000000000000000000000000000000 false (frontierMissing opening_6_and) = false := by decide +kernel

noncomputable def opening_6_or : List (ℕ × List W) := [⟨0x94e55ace54ad27294e929ca729d273956939ce529d2929d2938d2739ca73a465194612, rootWithGate 4 7 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_6_or_complete : initialBinary 0x80000000000000000000000000000000000000000000000000 true (frontierMissing opening_6_or) = false := by decide +kernel

noncomputable def opening_7_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_7_and_complete : initialBinary 0x1000000000000000000000000 false (frontierMissing opening_7_and) = false := by decide +kernel

noncomputable def opening_7_or : List (ℕ × List W) := [⟨0x9ca55a4e74aca5294e5294e539d2929529394e729ce939d27384e939ce93a465094a12, rootWithGate 3 4 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_7_or_complete : initialBinary 0x1000000000000000000000000 true (frontierMissing opening_7_or) = false := by decide +kernel

noncomputable def opening_9_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_9_and_complete : initialBinary 0x800000000000000000000000000000000 false (frontierMissing opening_9_and) = false := by decide +kernel

noncomputable def opening_9_or : List (ℕ × List W) := [⟨0x9ca55ace74ace7294e9294e739d2939d2739ce729d2939d2948d2939ce939c65194a12, rootWithGate 0 4 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_9_or_complete : initialBinary 0x800000000000000000000000000000000 true (frontierMissing opening_9_or) = false := by decide +kernel

noncomputable def opening_10_and : List (ℕ × List W) := [⟨0x8d295ac635ad294a4e94a46918ca52956b39c6339d251a5252952528ca54a465184232, rootWithGate 6 7 255 false⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_10_and_complete : initialBinary 0x400 false (frontierMissing opening_10_and) = false := by decide +kernel

noncomputable def opening_10_or : List (ℕ × List W) := [⟨0x8d295aca55ad294a4e94a4a9194e739d6b39ca539d272a52739525394e74a46518c632, rootWithGate 6 7 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_10_or_complete : initialBinary 0x400 true (frontierMissing opening_10_or) = false := by decide +kernel

noncomputable def opening_11_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_11_and_complete : initialBinary 0x8000000000000000000000 false (frontierMissing opening_11_and) = false := by decide +kernel

noncomputable def opening_11_or : List (ℕ × List W) := [⟨0x8d2939c6339d294a4694a4671952749d6b294a3295292a5293952749ce74a425194632, rootWithGate 1 7 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_11_or_complete : initialBinary 0x8000000000000000000000 true (frontierMissing opening_11_or) = false := by decide +kernel

noncomputable def opening_12_and : List (ℕ × List W) := [⟨0x8ca55ace35aca92a4e94946919d25494e739ce339d291a5292952549ca549465194232, rootWithGate 0 7 255 false⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_12_and_complete : initialBinary 0x40000000000000000000000000000000 false (frontierMissing opening_12_and) = false := by decide +kernel

noncomputable def opening_12_or : List (ℕ × List W) := [⟨0x94e75ace55ace93a4e949ca929d2749d2939ce539d292a5293952749ce749c65194632, rootWithGate 0 7 255 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_12_or_complete : initialBinary 0x40000000000000000000000000000000 true (frontierMissing opening_12_or) = false := by decide +kernel

noncomputable def opening_13_and : List (ℕ × List W) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_13_and_complete : initialBinary 0x80000 false (frontierMissing opening_13_and) = false := by decide +kernel

noncomputable def opening_13_or : List (ℕ × List W) := [⟨0x8ce739c6339ce93a46949ca7295294a529294a5295293a5294952949d2949c25194a32, rootWithGate 0 1 255 true⟩, ⟨0x94e74a4a54a4e93a4a949ce939d294a52939ce739d293a5294952949d2949c65194a32, rootWithGate 0 1 253 true⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opening_13_or_complete : initialBinary 0x80000 true (frontierMissing opening_13_or) = false := by decide +kernel

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

lemma pureAt_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : pureAt e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => frontierMissing states)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : frontierMissing states z v
        · exact Bool.noConfusion ((checked _ (frontierMissing_false missed)).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

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
  change tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 _ = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change (bif pureSecond state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1)
    then true else _) = _
  rw [pure, mixed]
  rfl

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

  opening_0_or.getD 0 (0, []),
  opening_1_and.getD 0 (0, []),
  opening_1_or.getD 0 (0, []),
  opening_2_and.getD 0 (0, []),
  opening_2_or.getD 0 (0, []),
  opening_3_and.getD 0 (0, []),
  opening_3_or.getD 0 (0, []),
  opening_4_or.getD 0 (0, []),
  opening_5_and.getD 0 (0, []),
  opening_5_or.getD 0 (0, []),
  opening_5_or.getD 1 (0, []),
  opening_6_or.getD 0 (0, []),
  opening_7_or.getD 0 (0, []),
  opening_9_or.getD 0 (0, []),
  opening_10_and.getD 0 (0, []),
  opening_10_or.getD 0 (0, []),
  opening_11_or.getD 0 (0, []),
  opening_12_and.getD 0 (0, []),
  opening_12_or.getD 0 (0, []),
  opening_13_or.getD 0 (0, []),
  opening_13_or.getD 1 (0, [])]

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

def secondCount : ℕ := 443

def encodedSecond : List ℕ := [0x90228e22cc228c22882286228422d00290028e020e02cc028c028802860284020402c2028202eea18c818c6188618c41884186418c01880186018401c20190e010e090c08ec0aea090608e60cc608c60904010408e400e408c40ca40864090208e208c2086208420900010008e000e00cc008c00ca00860084000400c2008200, 0x820590e490848e8490648e648c64886490441044ce448e448c44884486449024cc2488248624842490041004ce048e04cc048c048804860484040404c2048204aec3eca38e838e6388638e43884386438e038803860384030403c203d0e290e28ec22ec290828e8290628e628c628862d04290428e420e42cc428c4288428642, 0x8ea790878e878c878a8790678e678a678867ae47a64790078e078c078a07880786070607c40790e610e690a68ea690868e868c868a869066ae668e668a66886690268e268c268a2688268626900610068e060e06cc068c068a068806c6068606c20682068ec58e858c858e658c658865ea45882586258e058c0588058605c205, 0x8e0a880a860a060ac40a90e910e990a98ea990898e89cc898c898a89906910698e690e698a69886990498e498a498849864990291029ae298e290e298a298829a62986290629c42984298ec88e888c888e688c6888688e480e488c48884886488e288828862884288e080e088c08ea08ca088808860884080408c208820890a7, 0x864d902d102d8e2d0e2da82d882d862d062dc42d842d90ec10ec904c104c8e4c0e4c902c8e2c842c900c100c8e0c0e0cca0cc80c840c040cc20c820c90ebd06b906b8e6b8c6b904b8e4b0e4bca4b864b902b8e2b862b842bd00b900b8e0b0e0bca0b860b840b040bc20b820bb0aaaeaa908a8e8a8c8a906a8e6a886aa84a900a, 0x8c5188518651ee11ce118c1186118411c2118eb090908e908c908e708a708870a65090108e1088108610c4108e8f906f8e6f8a6f904f504fce4f8e4f884f864fd02fce2fd00f900fce0f8e0f860f840f040fc20feece8a6e884e864e860e840ec20e90ed10edaead908d8e8d8c8d906d106d8e6d0e6dca6d886d904d8e4d884d, 0x8c948e748c748a748e540e548c540c5488548654ac348c340c348634843404348eb390938e938c9390738e738a738873ae53a853a653ae338e338833863306338eb2d09290928e928c92d07290728e720e728a7288728e52885286528e320e328832a63286320632e432a432c43284328c918c718a71]

noncomputable def transitionFromCode (width : ℕ) (parentAt : ℕ → SearchState) (entry : ℕ) : SearchState :=
  let before := parentAt (entry % 2 ^ width)
  let left := (entry >>> width) % 16
  let right := (entry >>> (width + 4)) % 16
  let dropLeft := if entry.testBit (width + 8) then 2 ^ left else 0
  let dropRight := if entry.testBit (width + 9) then 2 ^ right else 0
  let kept := 2 ^ before.2.length - 1 - dropLeft - dropRight
  secondTransition before left right kept (entry.testBit (width + 10))

noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := encodedSecond.getD (i / 64) 0
  transitionFromCode 5 firstAt ((block >>> (16 * (i % 64))) % 65536)

noncomputable def secondSlice (n : ℕ) : List SearchState :=
  (List.range (min 4 (secondCount - 4 * n))).map fun i => secondAt (4 * n + i)

noncomputable def secondGroups : List (List SearchState) :=
  (List.range ((secondCount + 3) / 4)).map secondSlice

def successors0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors0_complete : pureSecond (firstAt 0) (frontierMissing (successors0.map secondAt)) = false := by

  decide +kernel

def successors1 : List ℕ := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors1_complete : pureSecond (firstAt 1) (frontierMissing (successors1.map secondAt)) = false := by

  decide +kernel

def successors2 : List ℕ := [30, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors2_complete : pureSecond (firstAt 2) (frontierMissing (successors2.map secondAt)) = false := by

  decide +kernel

def successors3 : List ℕ := [78, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors3_complete : pureSecond (firstAt 3) (frontierMissing (successors3.map secondAt)) = false := by

  decide +kernel

def successors4 : List ℕ := [29, 79, 94, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors4_complete : pureSecond (firstAt 4) (frontierMissing (successors4.map secondAt)) = false := by

  decide +kernel

def successors5 : List ℕ := [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors5_complete : pureSecond (firstAt 5) (frontierMissing (successors5.map secondAt)) = false := by

  decide +kernel

def successors6 : List ℕ := [19, 66, 67, 115, 135, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors6_complete : pureSecond (firstAt 6) (frontierMissing (successors6.map secondAt)) = false := by

  decide +kernel

def successors7 : List ℕ := [14, 60, 61, 111, 157, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors7_complete : pureSecond (firstAt 7) (frontierMissing (successors7.map secondAt)) = false := by

  decide +kernel

def successors8 : List ℕ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors8_complete : pureSecond (firstAt 8) (frontierMissing (successors8.map secondAt)) = false := by

  decide +kernel

def successors9 : List ℕ := [6, 7, 51, 52, 102, 103, 148, 149, 178, 199, 200, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors9_complete : pureSecond (firstAt 9) (frontierMissing (successors9.map secondAt)) = false := by

  decide +kernel

def successors10 : List ℕ := [59, 110, 134, 156, 206, 233, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors10_complete : pureSecond (firstAt 10) (frontierMissing (successors10.map secondAt)) = false := by

  decide +kernel

def successors11 : List ℕ := [77, 93, 125, 140, 170, 192, 217, 248, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors11_complete : pureSecond (firstAt 11) (frontierMissing (successors11.map secondAt)) = false := by

  decide +kernel

def successors12 : List ℕ := [41, 72, 91, 120, 136, 165, 187, 213, 242, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors12_complete : pureSecond (firstAt 12) (frontierMissing (successors12.map secondAt)) = false := by

  decide +kernel

def successors13 : List ℕ := [5, 36, 50, 86, 101, 130, 147, 177, 198, 225, 271, 295, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors13_complete : pureSecond (firstAt 13) (frontierMissing (successors13.map secondAt)) = false := by

  decide +kernel

def successors14 : List ℕ := [31, 171, 249, 307, 333, 335, 336, 337, 338, 339, 340, 341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors14_complete : pureSecond (firstAt 14) (frontierMissing (successors14.map secondAt)) = false := by

  decide +kernel

def successors15 : List ℕ := [32, 80, 81, 95, 126, 141, 172, 218, 250, 289, 308, 334, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors15_complete : pureSecond (firstAt 15) (frontierMissing (successors15.map secondAt)) = false := by

  decide +kernel

def successors16 : List ℕ := [16, 63, 112, 159, 207, 235, 279, 302, 322, 351, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors16_complete : pureSecond (firstAt 16) (frontierMissing (successors16.map secondAt)) = false := by

  decide +kernel

def successors17 : List ℕ := [10, 106, 152, 202, 229, 298, 317, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors17_complete : pureSecond (firstAt 17) (frontierMissing (successors17.map secondAt)) = false := by

  decide +kernel

def successors18 : List ℕ := [11, 55, 56, 87, 107, 132, 153, 180, 203, 230, 256, 274, 275, 299, 318, 348, 349, 366, 379, 380, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors18_complete : pureSecond (firstAt 18) (frontierMissing (successors18.map secondAt)) = false := by

  decide +kernel

def successors19 : List ℕ := [0, 45, 96, 127, 142, 173, 193, 219, 251, 266, 290, 309, 362, 387, 389, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors19_complete : pureSecond (firstAt 19) (frontierMissing (successors19.map secondAt)) = false := by

  decide +kernel

def successors20 : List ℕ := [1, 33, 46, 82, 97, 128, 143, 194, 220, 267, 291, 310, 335, 342, 375, 388, 390, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma successors20_complete : pureSecond (firstAt 20) (frontierMissing (successors20.map secondAt)) = false := by

  decide +kernel

noncomputable def groupChecked (group : List SearchState) : Bool :=
  group.all fun x => !afterSecond x

def indexValid (i : ℕ) : Bool := decide (i < secondCount)

lemma secondAt_mem (i : ℕ) (valid : indexValid i = true) :
    ∃ group ∈ secondGroups, secondAt i ∈ group := by
  have hi : i < secondCount := of_decide_eq_true valid
  have block : i / 4 < (secondCount + 3) / 4 := by omega
  have hn : i % 4 < min 4 (secondCount - 4 * (i / 4)) :=
    lt_min (Nat.mod_lt _ (by decide)) (by omega)
  refine ⟨secondSlice (i/4), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨i/4, List.mem_range.mpr block, rfl⟩
  · apply List.mem_map.mpr
    refine ⟨i%4, List.mem_range.mpr hn, ?_⟩
    congr 1
    omega

lemma checkIndexTable (tableGood : secondGroups.all groupChecked = true)
    {ids : List ℕ} (wellFormed : ids.all indexValid = true)
    (state : SearchState) (inside : state ∈ ids.map secondAt) :
    afterSecond state = false := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp inside
  obtain ⟨group, hg, member⟩ := secondAt_mem i (List.all_eq_true.mp wellFormed i hi)
  have good := List.all_eq_true.mp tableGood group hg
  have hit := List.all_eq_true.mp good (secondAt i) member
  cases result : afterSecond (secondAt i) <;> simp [result] at hit ⊢

def thirdEncodedSteps : List ℕ := [
0xb020190201ae2018e201cc2018c201ca2018420192e00b0c009280090800ce8008e80092600906008e600cc60088600b2400b0400ae400a8400a6400b220092200b020090200ce2008e200cc20086200, 0x904038e4038840386403b22039220390203ee203ae203ce2038e203cc20390e028e2028c202e400290e0110e0190c018ec01aea01906018e601cc6018c60190401104018e4010e4018c401ca40186401, 0xae804926041260490604106048e604c860492404904048e40486404ec204930031300392e0390e03b0c039280390803ce8038e803b260392603b060390603ae6038e603ec603cc603a86038860392403, 0xb02069020690e0510e0590c058ec05908058e805cc8058c80590605106058e6050e6058c60588605904058e4058c4058840586405902058e205cc2058c205930041300492e0490e04b2804b0804ee804,
0x8e80790607106078e6070e607cc60788607904078e407884078640790207ae2078e20793006b2e06b0e06b0c069280690806ce806926061260690606ce606cc6068860692406ce406884068640692206, 0x8640b8ec0a8e40af000ab30099300992e09d0e09f0c09b0c0992809d080990809ce8098e8099260912609d0609906098e609cc609886099240988409864099220990408ee00890e0710e07aec0790807, 0xce80c8e80cb260cb060c9060c8e60ccc60c8860cb240cae40cd300b9300bd2e0b92e0b90e0bb0c0bd280b9280b9080bce80b8e80bd260b9260b9060b1060b8e60bcc60b8860b9240b9040b8e40b8840b, 0x9281090810ce8108e810906108e610cc61088610b300f9280fce80f9260fcc60f8860fb2e0e9280ece80e9260ecc60e8860e92e0db0c0db280db080d9260d9060d8e60dcc60d92e0cb0c0c9280c9080c,
0xb0c139281390813ce813b061390e1210e1290c128ec12908128e812cc8128c812906128e6128c612930111301192e1190e11b0c11b2811ee811ae81192611906118e611ec611cc611d301092e10b0c10, 0xb0c18b081893017d2e1790e17b0c179281790817ce8178e817d0e16aea168e616cc6168c616f0416b30159301592e15d0e15b0c159281590815ce8158e815926153261592614cc614ee41493013b2e13, 0xaa622a86228e2228a22288222eea21886218842186421882218622184221f0e1fd301e9301e90e1c90c1c9301b92e1b90e1bb0c1b9301a92e1af0c1ab0c1a90e1910e19aec19ae81993018b2e18b0e18, 0x8ea26aa626f0c25cea25ce8258a825ce6258a62588625f0c24aea248e824ca8248e624ca624886248e224f0c238ea23ae823aa8238e6238a623c86238e223aa2238a223f0c228ea228e8228a822ae622,
0x9022eae22e8e22ecc22e8c22e8822e8622e8422e0422e8e82d8a82dd262dce62d8e62d8a62d8862df222dd222dce22d8e22d8a22d8822d8622df0c2bf0c2acea2af0c29f0c288a828f0c278e827f0c26, 0x8e2308a23088230d0e2f8e82f8e62f8862fd002f8e02fcc02f8802f8602fe402fc402fd0e2e8ec2e9082e8e82e9062e8e62e8c62e8862ed042e9042e8e42ecc42e8c42e8842e8642ef022eb022ed022e, 0x92a3090a3092830908308e8308a830f2630b2630d2630b063090630ee630ae630ce630aa6308a630a86308863090430ce4308e4308a43088430f2230b2230d2230922309023010230ee230ae230ce230, 0x92a3190a31b2831b0831ae831aa831d2631926319063110631ce6318e6318a631c86319243190431ce4318e4318a43186431d2231922319023110231ce2318e231aa2318a231d30309303090e3030e30,
0x90e3230e32b2a32b0a3292832908328e832ca832d2632926329063210632ce6328e632ca632886329243290432ce4328e4328843286432d2232922329023210232ce2328e232d30319303190e3130e31, 0x8843486434d023490234ae2348e2340e234d303393033b0e3392a3390a339283390833ce8338a833d263390633ce6338a6338863392433ce4338a4338843386433d223392233b023390233d303293032, 0xd063690636ce6368e6368a63688636d22369223688635d0435cc4358843586435d0035ee035ce035d0e3490e3490a348ea34908348e8348a834d0634906348e6340e6348a63488634904348e4348a434, 0x8e4388a4388843886438d303790e37d2a3790a37d2837908378e8378a837d263790637ce6378a63788637d2437f3036b3036d3036d0e3692a36d0a3690a3692836d0836908368e8368a836d263692636,
0xce83c8a83cd263cce63c8a63c8863c8e83bd263bce63b8e63b8863bd263ace63a8e63a8a63a8e8398a839f263990e3830e3890a38908388e8388a8389063810638ce6388e6388a6388863890438ce438, 0xb2a4192841908418e841d264190641ce641d30409304090e4030e4092a4090a40b2840ae840d264090640ce640aa6408a6408e83f8a83ff303e8a83ed263ece63e8a63e8863e8a83dd063d8a63d8863d, 0xd3045d0e4592a4590a4592845908458e8458a845d264588644ee444d0e4390e4390a438ea43908438e8438a843d0643ae6438e643d3042b0e4290a4290842ce8428a842b0642d30419304190e4130e41, 0xd304cd304b90e4bd2a4b90a4bd304a92a4ad0a4a90a4ad30499304992a4990a49b0849d30489304890e4830e4890e4730e4790a47908478e8478a847d3046d2a4690a46d2846908468a846f3045b3045,
0x8a255b0e54eec5490a54908548a854b0654aa6548a654a865488654b0254902548a25488254eca53886538805386053e4053c4053eca5288652884528645288252862528425204252eec4ed304d90e4d, 0xeec5890a58b0858aa6588a658f0e57eec57d0a57d08578a857d06578a65788657b0e56eec56b0a5690856ca85690656ca6568865690256b0e55eec5590a55b0855aa855906558a655c865590255aa255, 0xae261ce2618e261cc2618c261882618626184261042618a860d06608a66088660f0260d0260ce2608a260882608626006260eec5deec5cd0a5cb0e5beec5beec5a8a85ab0e59eec59b0a5990859b0e58, 0xce2638e2638a26388263908629066288662cc262882628626290062ce062cc0628806286062e4062c4062908618e861906618e6618c6618866190461ce4618e4618c4618846186461b026190261ee261,
0x8e264aa2648a2649306392a6390a6392863908638e8638a863b266392663f0663b0663d0663ae663aa6638a663a86638866392463ce4638a4638846386463b22639226312263d026390263ee263ae263, 0xce46588465864659226512265d026590265ce2658e2659306492a6490a64b2864b0864ae864aa8649266412664d0664906648e6648a664c866492464ce4648a464864649226412264d026490264ce264, 0xee267ae267ce2678e26792a6692866ce8668a86692666d0666ce6668a666886669226612266f0266d026693065b2a65b0a6592865908658e865ca8659266512665d0665906658e665ca6658866592465, 0x864699026910269b306892a68d0a6892868d08688a86892668d06688a668886689226890e6790a678ea67908678e8678a8679066710667ce6678e6678a66788667904678a46788467864679026710267,
0xd286b9286b9086b8e86b8a86bd266b9266bd066b9066b8e66b8a66b8866b8c66a8866ace46a8846a8646af006ad006a90a69908698e8698a86990669106698e6698a6698866990469ce4698a46988469, 0x92672d06729307192a7190a71b2871ae87192671d0671aa6718a6718a870d06708a670886708a86fce66f8a66f8866fd066e8866ed066d8a66d8a86cf066cd066c8a66c8866cd306bd2a6b92a6b90a6b, 0xd0a7a92a799307892a7790a7792877908778e8778a87788676f047690a75908758e8758a8759067530675b307492a74d0a7492874d08748a87492a73928738a873f067393072b2a7292872908728e872, 0xb0881ae881aa881ec6818a481902818e281aa2818a2818ec808e8808c8808e6808c68088680ea480ae2808e280ac2808c28088280862808a87fec67faa47fa847f8a27f8827fd2a7b92a7b90a7b92a7a,
0x88687ec686ec685aa485d0e84d0a848ea84d08848e8848a884ec684b0e8390a83cea8390883ce8838a883ec6839028390e82b0a82aea82908828e882ca882ec68288482902828e28290e8190a818ea81, 0x8ea8e8ca8eb088e9088e8c88e8a88eb248eb048eae48eac48eaa48ea848eb228e9228eb028e9028ece28e8e28e8c28e8a28ec828e8828ed0a8a8ea8a90a89cea8990e888ca878c8878a8878c6878a687, 0x8e2908c2908a29090e8f10e8f90a8f8ea8f9088f8e88f8c88f8a88f9068fae68f8e68f8a68f8868fb028f9028f1028fae28f8e28f0e28fcc28f8c28f8a28f8828fc628f8628f92c8e90c8e92a8e90a8e, 0x90291102918e2910e291ec291ac291cc2918c2918a291882919309092c9090c9092a9090a908ea908ca90b2890b0890ac890aa890904908e4908c4908a490c8490b22909229090290ee290ae290ce290,
0x92892b0892908928c892ca89292492904928e4928c4928849292292122929029210292ce2928e292ac2928c29290e9110e9190a918ea91908918e8918c8918a891904918e4918c4918a49188491b0291, 0x9309313093b2c93b0c9392a9390a938ea93cca9392893b089390893cc8938a89392493904938e4938a4938849392293122939029310293ce2938e293930921309292c9290c92b2a92b0a92aea92aca92, 0xae8958e8958c8958a895904958e4958c4958a495884959029510295ae2958e2950e2959309492c9490c9492a9490a94cea948ca94b08948c8948a89492494ce4948c4948a4948849492294b029490294, 0x90c9792a97d0a9790a978ea978ca9792897f0897b0897d08978c8978a897924978c4978a49788497922971229790a96908968a89690096ee096ce09690e9510e9590c958ec9590a958ea958ca9590895,
0x8ca9ab089aae49ad309993099d2c9992c9990c99d2a9992a9990a998ea998ca99d2899b0899908998c8998a899904998e4998c4998a4998ea988e8988a898ae698f0098d0098b30979309792c97d0c97, 0x8ca9fb089fb309e92c9e92a9e8ca9e8c89e8a89e92c9d92a9d8ca9d8c89d8a89db2c9cb0c9c92a9c90a9c8ea9cb089c9089c8a89c92c9b90c9bb2a9bb0a9bb089b9089b8c89bac49b90c9a90a9a8ea9a, 0x90aa48caa4b0ea390ea390aa38eaa3908a38e8a38c8a38a8a3b30a292ca292aa28caa2b28a2930a1b2ca192aa190aa18eaa1b08a1930a092ca090ca0b2aa0aeaa0b08a0ac8a0d309f90c9f90a9f8ea9f, 0x8c0ae8a0ae880aee60aec60ae8c8ad8a8ad8a6ad886ad8c2ad8a2ad882ad862ad062adf0eab930aa930a9930a8d2ca892ca890ca8930a792ca7d0ca790ca7930a692ca690ca6b0aa6930a5130a590ca4,
0x902b08e2b0ac2b08c2b092caf90caf92aaf90aaf8eaaf8caafb28afb08af908afac8af8c8afaa8af8a8afb06afa86afb22af922af902afae2af8e2af8c2af8a2af8eaae8e8ae8c8ae8a8aeae4ae8e0ae, 0x8c8b28a8b2a86b2922b2b2cb1b0cb192ab190ab18eab1ccab1928b1908b1cc8b18a8b1b06b1a86b1922b1902b18e2b192cb090cb0b2ab0b0ab0aeab0acab0928b0908b08c8b0ca8b0b06b0a86b0922b0, 0x92cb790cb7b2ab7aeab7908b7ac8b78c8b78a8b68a6b6886b68c8b58a8b58a6b5886b5d2cb4d2ab48eab48cab4d28b48c8b48a8b4d0cb3d0ab38cab3d08b38c8b38a8b392cb292ab2ceab28cab2928b2, 0xea0c3e40c38ecc28e4c20e4c28c4c2ae2c28e2c2ac2c28c2c2ea2c2ca2c2842c2906c1b04c1a64c1b02c1902c1ec2c1cc2c1862c1d2cbed0cbd92cbc8eaba8caba8cab9b2cb892ab890ab88eab8908b8,
0x8c6c78e4c7864c7ae2c78e2c72e2c7ac2c78c2c790ec6906c6106c68e6c6904c6864c6ec2c690ec5906c5106c58e6c5904c5864c5ec2c590ec4b06c4ae6c4904c4864c4b02c4902c48e2c4ec2c4cc2c4, 0x8a6cc886ccb04ccd0ecb90ecbd06cb8e6cb904cb864cbee0cab0ec9906c9ce6c9902c98cac88c8c88a8c88c6c88a6c8886c88c4c80c4c88a4c8884c8864c88c2c8882c8862c8842c88ecc78e6c70e6c7, 0xb04db904db8c4db8a4dba84db884db084db90ed990ed790ed58ead48e8d48a8d4886d3ee4d3b0ed290ad2908d28a8d290ed190ed090acf908cf8a8cf8a6cf886cf906ce906cd90acc908cc8a8ccb06cc, 0xe6dc8a6dc886dcb04dc904dc104dcae4dc8e4dc0e4dc8a4dc884dca64dc864dc064dc92cdb90cdb92adb90adbceadb8eadb8cadb928db908db8c8db8a8dbb26dbb06dbac6dbaa6dba86dbb24db924db,
0x886deb24de924de324de124deb04de904de304de104deac4de8c4deaa4de8a4de90edd8e4dd902ddae2dd8e2dde62ddc62dd90edc10edc90adc8eadc908dc8e8dccc8dc8c8dc8a8dc906dc106dc8e6dc, 0xae6df8e6dfaa6df8a6dfa86df886df904df8e4df8a4df884df864df930de130de92cde90cde92ade90adeceade8eade8cadeb28de928deb08de908deac8de8c8deaa8de8a8de926de906de8c6de8a6de, 0xb04e1904e1930e0130e0b2ae0b0ae0eeae0aeae0acae0928e0128e0908e0108e0ca8e0926e0906e0886e0924e0b04e0904e0ac4e090edf10edf90adf8eadf908df8e8dfcc8df8c8df8a8dfb06df906df, 0x928e3128e3d08e3908e38c8e38a8e3926e38c6e38a6e3886e3b24e3924e3324e3124e3906e2902e2ee2e2ce2e2930e1130e1b2ce1b0ce1ccae1928e1128e1908e1108e1cc8e1926e1906e1886e1924e1,
0xb0ee490ee490ae4ceae48eae4908e4ce8e48e8e4cc8e48c8e48a8e4906e4106e4ce6e48e6e48a6e4886e4904e48a4e4884e4864e4b30e3930e392ce3d0ce390ce392ae3d0ae390ae3ceae38eae38cae3, 0x8cae7b28e7b08e7908e78c8e78a8e7b26e7d30e6930e6d2ce692ce690ce6d2ae692ae690ae6ceae68eae68cae6d28e6928e6908e6108e68c8e68a8e6926e6906e68c6e68a6e6886e68e6e5f02e5d02e5, 0x8a8ebb30ea92cea92aeaceaea8caea928ea8c8ea8a8eab2ce9b0ce992ae990ae9ceae98eae9928e9908e98a8e992ce890ce8b2ae8b0ae8928e8908e88c8e8ac6e892ce790ce792ae790ae7ceae78eae7, 0x8a8eeee6ee930ed130edb2ced92aed90aedceaed8eaed928ed908ed930ec130ec92cec90cecb2aeceeaecaeaec928ec908ecac8ec8c8ecd30eb92ceb90ceb92aeb90aebceaeb8eaeb8caeb908eb8c8eb,
0xb0af3930f2130f2930f192cf190cf192af190af1ceaf18eaf18caf1d0ef08eaf08e8f0cc8f08c8f08a8f0f06f0b30ef930ef92cef90cef92aef90aefceaef8eaef8caef928ef328ef92aee928eecc8ee, 0xb28fdb08fd908fdaa8fd8a8fdaa6fdb22fd922fd902fde60fc8c8fb886fb862fbf0ef9930f8930f7930f6d2cf692cf690cf6930f592cf5d0cf590cf590ef410ef490cf48ecf4aeaf4930f392cf390cf3, 0xf0d06b2d05b0d05b0b058eb048eb03b2d02b0d02b2b02aeb0290902f2d00d2b008eb00d29008a900f0cffd0aff8eaffd08ff8a8ffb2afeb0afeaeafe928fe908feca8feb2cfdb0cfd92afd90afd8eafd, 0xf230db230dd230d9230d9030dcc30de410cd070b9070b8e70b8c70b9050b8e50bca50b8650bf030bb030bd030b9030bae30b8e30bca30b8430bd290a8e90acc70a8870af230ad230acc30a8630af2d07,
0x8850f8650fd030f9030f8e30f9310ef290eb290eb090eae90e9270e9070e1070ec870e9250e9050e8650eec30e9310dd290d9290d9090d8e90db270db070d9070dec70dcc70da870d8870d9050d8850d, 0x909128e912d271290712cc71288712d2512b3111d291192911d0911909118e91192711d071190711cc71188711d231192311ee11090f0fd090f9090f8e90f8c90f9070f8e70f0e70f8870f9050f8e50f, 0x909198e9198c9198e71993118f2918b2918ae91890718ec718cc718d29178e917d29168e916cc71688716f2915cc715d29148e914909138e9139071310713cc71388713905138851386513d3112d2912, 0x8e323ca323c8323843239272290722b2522b0522a6522b232292322b032290322cc322ca32286322d311f9311db091dd291c9091c8e91cb311bd291b9291b9091b8e91bd271a8c71aee51a90f19d0919,
0x8e52686526903268e326ea326ca3269312513125b272592725b072590725925259052586525b23259232590325cc325ca32590f248e324e412490f2310f2390523105238e5230e523b032390323ae323, 0x8e52af012ab3129931299272912729d0729907299252990529865299232990528ee12890f2710f2790727107278e7270e727905278e52786527903278e32790f2610f2690726107268e7260e72690526, 0x92535b053590535aa53588535f0f3393132d0f31f0531b3130931309273032730ee52fd312e9072eb312d9272d9072db272cb072c9072cb252cd312b9312bd272b9272b9072b1072b9252b9052b8652b, 0x927389073888738b25389253890538aa53890f378e537e633790f3610f36aeb3690736107368e7360e736ca736b053690536ae5368e536a853686536b0d359293590935cc935b2735b0735a8735b2535,
0xb093aae93aac93a9073a1073a8e73a0e73aca73ac873a9053a8e53a8653a931391313992939129399093910939927399073988739b2539b05399313813138b0d38b293892938b093890938ec938cc938, 0xb273fd313e9313eb0d3ed293e9293e9093e1093ecc93e9273e9073e8873e8e73df033db313c9313cf0d3cb0d3c9293c1293cd093c9093ccc93c9273c9073c8873c9253c9073bee33b90f3a10f3aaeb3a, 0xec943cc943d3142b0d4292b4290b428eb4290942cc9428a942b3141b0d4192b4190b418eb419294190941cc9418a941b0d409294090940cc940b0d3f92b3f90b3f8eb3fb293fb093f9093fcc93f8a93f, 0xb0d4892b4890b488eb48d0f47aeb478e9478c947f0747b314693146b0d4692b4690b468eb469294632946929458c945ee74590f4410f4490b448eb448cb44909448e9449314313143b0d439294390943,
0xf0f54f0f538c953f0f52ac952aa752f0f51ac9518a751c8751f0f508c950aa750a875088350eed4f8a74f8854f8654f8634f8434ff0f4d90f4c9314bb0d4b9314af0d4ab0d4a9314913149b0d4993148, 0x8a758a875888758d2558d0558f2358b2358d235892358d035890358883588e9578e7578a757d0157ce1578e15786157e4157c41578a756ce5568855686556f0356d0356ee356ce356863568435604356, 0xd095a8c95ad075a8a75a8875ad235a90b59b2959b0959ac9599275952759d0759907598a759c8759d2559d0559d235992359d03599035990b5892958909588c958b2758f0758b0758d075890758aa758, 0x8a7608c95fd075f8a75f8875f8c95e8a75e8875e90b5d9095d8c95dd075d9075d8a75d8875dd055dd295c8c95cd275cd075c8a75c8875c9095b8c95b9075b5075b8a75b8875bd055bd035b9035bd0b5a,
0xb096bac96baa96b9036b8a36b8c96a8a76a8876a8836a8636ad0b6790b66b09668c9658a764909638c96370763d0b62d09628c96292961909618c961d07619076190b60b2960ac960d076090760aa760, 0x84377d0d7490d73b0b738eb7290b718eb7190d70aeb70ac9708c96fd2b6e8eb6ed0d6dd0b6d8eb6dd096d8c96d8a96d90d6cb2b6cb0b6caeb6c9096c8c96cca96ca876c9236c9036c90d6b90b6b8eb6b, 0xa6584865842658406584d2b838eb83d29838c9838a983aa5838a583a8583885838c97f8c97c8c77c8a77c8c57c8857c8657c8e77bce77af037ad037a8e779f0379ae778f0378d03788e378ee377ce377, 0x8e387e6387c63878c986ce7868e7868c7868a786ce5868e5868c5868858686586d09858c985d07858a785887858eb84d0984909848e9848c984d0784907848e7848a78488784ae5848e584a858488584,
0xb0789d0789ae7898e789aa7898a789a8789887898e5898858990d88d2b8892b8890b888eb88f2988b2988d2988b098890988ac9888c988aa9888a988907888a788b0588905883058810588aa5888a588, 0xd2b8c92b8cd0b8c90b8c8eb8cd298c9298cd098c9098c8c98c8a98cd078bee38bce38bf2b8ab2b8ab0b8aaeb8ad298a9298a9098a1098aca98a9078a8878a9058a8eb89d0989909898e9898c989f0789, 0x8eb93d2993d29928c992ee792d2b9192b9190b918eb91d29919099190d90f2b90b2b90aeb90d299090990ac9908c990d2b8f8eb8fd298f8c98f8a98ff2b8ed298e8c98ed2b8d8eb8df298dd0d8c90d8c, 0xac99c8c99caa99c8a99cb079caa79ca879cb059c9059c8a59cae59bae39b8e39be639bc639b90d9990d98d0d9790d9790d96b0b9690d9590b958eb9590d94d2b9490b948eb9490d93d2b9392b9390b93,
0x8c9a08a7a0887a0ceb9fce99f8c99fce79f8a79f8879fd0d9ed0b9e8eb9ed099e8c99e8a99eb2b9db0b9daeb9d9299d9099dca99db079da879db059d9059d90d9c92b9c90b9c8eb9cb299cb099c9099c, 0x8e7acaa7ac8a7aca87ac887acae5ac8e5ac0e5ac885acac3ab8c3abe43abc43abd0da890da7b0ba78eba68eba592ba490ba48eba4909a490da3b2ba3aeba3909a3ac9a38c9a38c9a28a7a2887a28a7a1, 0x885b0865b0cebaf8ebaf909afce9af8e9af8c9af907afce7af8e7af8a7af887afec3aecc3aeb09adae9adac9ad907ad107ad8e7ad0e7adc87adae5ad8e5ad8ebac909ac8e9ac8c9acb07ac907acae7ac, 0x8e9b68c9b68a7b5ee5b58ebb4909b48e9b48c9b4907b48a7b3ec5b3909b28e9b28c9b2907b28e7b28ebb1b09b1ac9b1907b18e7b1aa7b18a7b1cc9b08c9b08e7b0cc7b08c7b08a7b08e5b0cc5b08c5b0,
0x8ebb9cebb88ebb88ebb7ae9b78ebb6909b6,
]

def thirdEncodedRows : List ℕ := [
0x18ff, 0x17ff19, 0x3ff31, 0x1fff04181801,
0x12ff55, 0x16ff13201b1802, 0x13ff1730021b1803, 0x11ff2a30021b1804,
0x1a5, 0x15ff021101130115301c01170105, 0x101bd, 0x16ff03161214162f011b01170107,
0xdff171812141616193409, 0x7ff24181214162f340a, 0x5ff16153e1617180d270b, 0x5ff302b2917180d270c,
0xaff21141a1114151718340d, 0xcff0b060614141a11141517170121130e, 0xaff0c010a0606090b141a1114420122130f, 0x6ff0b0b0b150b141a2516171401231310,
0x1015b2c29173824, 0xaff03070a0b0b150a01130b0f01111415171401231411, 0x5ff0b76121415173826, 0x7ff060a140b1306070a1301190b071415171401231512,
0x4ff08050a0b090b0c0d11131a26151714241513, 0x3ff0c050a050f0b0c0816131a3b1714241514, 0x3ff040506050a0c081716081319011413141714241515, 0x3ff120f0606080c0b090607081201191513141714241516,
0x104030103050506090c140b160812190115133f241517, 0xc050f150b3b130629151713242d, 0x102020408050f0d080b0c10060810011929151713241618, 0xe2c0b6c261713242f,
0x3ff02040404050806010d070b0d0b220119011712141713200430, 0x6ff0155fe, 0x9ff070155fe, 0x9ff0a060156fe,
0x7ff090109060157fe, 0x6ff08080a015efe, 0x1010707080a070158fe, 0x1030607080a070159fe,
0x10a07080a0161fe, 0x20907080a08015afe, 0x1050607080a0163fe, 0x2070307080a0164fe,
0x1020102020307080a0a015bfe, 0xdff0172fe18, 0x1aff3d012dfe2e, 0xaff1b0198fe,
0x26ff0a011a0f250113fe52, 0x1fff27091b0f1c010afe65, 0x1dff1f0126091b0f15fb7c, 0x16ff1e1e2502240ffc91,
0x16ff341e25020a1a0f018efe, 0x7ff17331e2501c4fe, 0x15ff0701150117011b1e250d190120c4ba, 0xdff161c181c1e23022402cdd3,
0x11ff230715181c1e23020e16021101bbd4, 0x101123e181c1e0109fee4, 0x3ff143e181c42deec, 0x4ff173e183b2301cbfe,
0x5ff1b561d1e23daf2, 0x3ff20731e2301cdfe, 0x5ff2340331e2301cefe, 0x13c2c181b1ef00102fe,
0xcff080406051313150710181b1e23012b131073010efe, 0xaff0c010704060a0e13150710181b1e22012c130f6a0119fe, 0x6ff2806040e282f1b1e212e13720121fe, 0x9ff120b080f040e141408421e21022c130194fe,
0x14f41311e01f7fe, 0xaff020901070a0b281513011818191e21012e2357012efe, 0x5ff6f1319311e203001a9fe, 0x5ff110a120b0905050504062d0b0e19181e20022e1558013dfe,
0x3ff06060a0208091b0205050f0714120b0e19181e20210f15100186fe, 0x4ff0910130a0b060c060907141232181e203015550142fe, 0x3ff050807090b080a331411011a18181e20220e253e014afe, 0x3ff17090b120c3b111b18181e203060014efe,
0x40301040806090b0915281310011b18181e20230d26390150fe, 0x10403050e090b130b3b101c18181e203001b0fe, 0x14022c0b296e1e2001e1fe, 0x30e020f15080b29131034171e203101b1fe,
0x3090509070d110b3c0f1e17171e20910152fe, 0x305040510020b0a070b0f3c021c17171e20270b5f0153fe, 0x7ff0304fe, 0x5ff080304fe,
0xdff0501070124fe01e1fe, 0xaff0e04080105fe0201fe, 0x8ff0a010d0408e8021ffe, 0x7ff09090d0187028dfe,
0x5ff0808090c010e5202b6fe, 0x3ff05010708090b010f4802c1fe, 0x11008090b2d02edfe, 0x1020f08090b0b061b02effe,
0x108040608090b031cfe, 0x207040608090b031dfe, 0x1030103040608090b0d06030bfe, 0x4040608090b1c0303fe,
0xaff034dfe, 0x17ff4d015afe0184fe2d, 0xcff180b3c0311fe, 0x20ff0c01170b30013cfe0191fe51,
0x19ff210b180b260127fe019efe64, 0x17ff1901200b180b1e0112fe01a5fe7b, 0xcff18181f02230125fe01a7fe90, 0x15ff24181f020c170c0351fe,
0xaff140223181f2302035efe, 0xfff1e020d0115181f0f14020c01e701b2feb9, 0x6ff101d0f16181f02c6febf, 0xfff06010f0c110f16181e0110130128ac1301a9fed2,
0x4ff251d25181e0388fe, 0x1291d2536120377fe, 0x12a1d3e1d120378fe, 0x3ff2b43181d120379fe,
0x3ff2e1e25181d038cfe, 0x8ff0404020710050b110d1312181c012910148901aafe010dfe, 0x6ff08010304050410050b110d1312181b012a10118201aafe0118fe, 0x3ff2f103112181b2b9c02cafe,
0x5ff32220d24181a2c0367fe, 0x5ff0a07070404030203010e07281311181a022a127701b2fe012dfe, 0x106481d241803affe, 0x5ff020511071e0111120b1410181a012c225901b2fe013cfe,
0x6010508031204080d0909120b1410181a1d10130f5802f0fe, 0x60612071d09093110181a2d022afe0141fe, 0x1060f0924250b23181a2d036cfe, 0x1010707080405081b0113120b140f181a1f0e224d01b1fe014dfe,
0x2040f111b260b23181a2d036efe, 0x102020208070505071a0115110b150e181a200d234b0301fe, 0xf0a071a270b23181a039dfe, 0x5ff0465fe,
0xcff046bfe, 0xbff0d060465fe, 0x9ff0b010c060466fe, 0x7ff0a0a0c01046dfe,
0x6ff08090a0b01046ffe, 0x1171f0467fe, 0x221140468fe, 0x7ff0807080a0c080469fe,
0x60907080a0c08046afe, 0x1060907080a0c0473fe, 0x1070907080a0c0474fe, 0x2040907080a0c0475fe,
0x2040907080a0c0476fe, 0x10907080a0c0477fe, 0x19ff4202d5fe010183fe10, 0x18ff54010bfe01bffe010183fe23,
0x18ff191a02d8fe018dfe46, 0x17ff311a011bfe01bcfe01018dfe47, 0x19ff1819171a30d101b6fe01019afe5b, 0x17ff19011719171a27c301b0fe0101a1fe72,
0x11ff181816021702171ad901a8fe01a6fe88, 0x15ff291816021702171a04b0fe, 0x5ff16281816320275fe0256fe, 0x15ff0501140112011518161a17011a01228801a9fe0101b0fead,
0x5ff16192918163104cefe, 0x12ff050115051414151815011a0115011b011d7f0191fe011301abfec7, 0x5ff2d19141518303203dafedb, 0x7ff19191914152e1a3218020afe0101adfee6,
0x7ff08181919142e151a32180207fe010297fe, 0x4ff1611461618151a32021bfe029dfe, 0x5ff2b332918151a320212fe02a7fe, 0x5ff4b18141518154c03bffefb,
0x6ff0c05081d1a18141518301b16020cfe01a9fe0106fe, 0x5ff070b0510151a18141518301b160202fe01a9fe0111fe, 0x4ff06061907070e1a182918301b1601f1fe02ccfe, 0x7ff181107150b0e01181514184b16780179fe0801a9fe011cfe,
0x1010d3f19192918311a0207fe02cefe, 0x1030804130505160c0c0d0f0a1613181a171a171f590178fe0902c6fe, 0x3ff0c0b0606120e0c192f13181a171a1701f9fe01aafe011dfe, 0x3ff0404070b0c1208060c0d0b011a1513181a171a172001d1fe0801aafe011efe,
0x3ff120605070c05060811011812091513181a171a17205a0177fe01b2fe011ffe, 0x4030103040612061108070a0f09011b1513181a171a172001d1fe0901a9fe0120fe, 0x30103040a0705060d05050810011814081513181a171a17205b0176fe02d3fe, 0x107b28181a3104dcfe,
0x3ff04040405010705060706210118011b1612181a18193801d0fe010901a9fe0122fe, 0x8ff013bfe04adfe0b, 0xaff09027afe0347fe32, 0x15ff0a0108f01a015ffe01befe01018dfe3f,
0x10ff160909dc0171fe01b8fe010198fe57, 0xeff1001150909c50171fe01b2fe01019ffe6e, 0x8ff0f0f15010909b0031dfe01a6fe84, 0x5ff170f150a01fefe0403fe,
0x6ff0f0d0f14017f030cfe0101befec2, 0x3ff150d0f147004c7fed7, 0x101250f140d0602fe, 0x6ff03040706070c0f130118440186fe018dfe0601aefeed,
0x4ff060102040706070c0f120119440186fe018dfe0601aefeee, 0x50514130f110101e4fe0430fe, 0x1190d0b0f110373fe0501affeef, 0x10d040606070b0f111409440185fe018dfe05029ffe,
0x1060507060d0b0f111409035bfe01b0fef0, 0x719110f11140605fe, 0x7060d0d0a0f116304c6fef1, 0xb14100f11150606fe,
0x204050e0d090f116405b8fe, 0x7ff066cfe, 0xaff0674fe, 0x1067ffe,
0x9ff020b08066cfe, 0x6ff068bfe, 0x6ff0692fe, 0xaff07070901010a010701066dfe,
0xeff06a4fe, 0x3ff1901160b010677fe, 0x1c069bfe, 0x6ff04160117010a010901066ffe,
0x6ff0614060b0706150671fe, 0x2006a5fe, 0x2006a6fe, 0x4ff090512080b0706150672fe,
0x5081706a8fe, 0x5081706a9fe, 0x3ff14060a0a0b07060d067bfe, 0x1270a0b0713067cfe,
0x101020c01040606090a0b07070c0a0673fe, 0x3010505071506adfe, 0x2706aefe, 0x905071406affe,
0x2606b0fe, 0x905071306b1fe, 0x1010604010f0106040f0b07070c067efe, 0x18ff6c01760147fe01015efe01c3fe010189fe0103,
0x19ff7d0101abfe01016cfe0101bffe010180fe011b, 0x6ff1a195a80028cfe01bdfe01b7fe, 0x21ff060118011801590178010ffe0118010160fe0101befe010189fe0136, 0x15ff012cfe010efe0118010160fe0101befe010189fe0138,
0x12ff37011e19526c010dfe010170fe0101b8fe0101e7fe, 0xfff1335011f194c640104fe010170fe0101b2fe01019cfe0168, 0x3ff56012001a5fe0319fe023afe, 0x18ff03010f01110132010a011501190145010145fe130163fe010d0195fe180190fe147f,
0x14ff0237fe130162fe010e0195fe180190fe1480, 0x1012d01560121600145fe0175fe0f03d2fe, 0x15ff02012b0104101230010d14011a0144015fe6140161fe0f0195fe0117010190fe1481, 0xcff16181515121a163d3f0660e6140161fe01a4fe180191fe1482,
0x7ff22181541163d3f014cfe140161fe01a4fe180191fe1483, 0x8ff0821181541163d3f014cfe140161fe01a4fe180229fe, 0x7ff3144121816112c018bfe0319fe01aafe98, 0xaff26121915161218163d40080143fe140162fe01a3fe180192fe1485,
0xaff0b080914121915281701150127164069e2140162fe130190fe180192fe1486, 0x8ff0a010a08110c121915172701150128164069e2140162fe130190fe180192fe1487, 0x4ff5445125404bafe01aafe9c, 0xaff0509090b12070b011109100114011612150115012817400a0140fe01140161fe01120190fe180192fe1489,
0x6ff0b7015171254570a02b6fe034dfe148a, 0x7ff070a0e091409070b110118150e09121501150128183f0a61e00175fe14018ffe01180191fe148b, 0x108060a061d081b1119151712151629183f6be016015ffe14018ffe190231fe, 0x3ff09060a0f090b12111119152915162918aaf60173fe01a8fe01a6fe8c,
0x4ff0c060a0708090b090911111915291516291806eefe, 0x3ff050407060a0f141209081118011401291516291841014bfe150160fe01a3fe180193fe138d, 0x3ff131008070a0a0a080908100118152a15162918416be0150160fe14018ffe180193fe138e, 0x403010404060709190a12090810180114011c2316291841014bfe150160fe01a3fe180193fe138f,
0x30103050406100907090a0b0709080f0118151d23162918416cdf150160fe15018efe180236fe, 0xc092109871013162901a4fe04c4fea3, 0x3ff04040504020807010f090b0b2601180114011c10131622075a0f013bfe160160fe01a2fe0116010194fe1292, 0x101014ffe022efe4f0468fe,
0x4bffe0378fe, 0xeff03fc16021ffe1a015ffe01bffe01cbfe, 0x5ff032efe9cd501b9fe01eefe, 0x4ff14aa150206fe0171fe0402fe,
0x4ff170193021afe030dfe027ffe, 0x740223fe0107fe049dfe, 0x4ff050506090107660223fe0180fe0196fe0296fe, 0x5090608016e0222fe010180fe042dfe,
0xa0a086f010bfe042dfe0299fe, 0x4ff04040505080b63010223fe0315fe029afe, 0x30e05086e0224fe05b0fe, 0x90409086e0224fe05b1fe,
0x205090c6e0224fe05b2fe, 0x20505106e0224fe05b3fe, 0x7ff0170fe022efe04c4fe, 0xfff0160fe022ffe650107fe01bffe01b0fe,
0x4fefe037cfe, 0x14ff10081dfc160117fe0110fe170159fe7f013dfe01e0fe, 0xcff0262fe0107fea4cc8e0128fe0200fe, 0xfff0d141008f70130fe00fefeb2be9d0113fe021efe,
0x33efe056efe, 0xdff10200f01ce150207feee87110192fe026afe, 0x8ff0d101e020d02b8021cfe0178fe01a8fe027afe, 0x8ff15101e020d020a010f9e0165feb70100fe78ea0339fe,
0x109240fca0102fe06c4fe, 0x10a241fb30223fe05abfe, 0x3ff0b24100fa40221fe05bdfe, 0x11a1810a9011efe06cbfe,
0x6ff060a0b0c0c100f01110c0c670193fe96018dfe00fefe8a02b5fe, 0x5ff06010503070b0c2a01120c6b0197fe95018cfe0101fe8302c0fe, 0x1011b2410910803fe, 0x4ff0306050f0c0b010c100d011368013cfef4070180fe070170fe02defe,
0x1012d0b0d100d145903bffe0176fe02e7fe, 0x10305020605050206020b0b0d100d140e09390401b9fe830187fe016afe02f5fe, 0x20508140b0a010d100d144c0241fe0142fe470167fe02fafe, 0x305080605140a0e100d144a0241fe018afe0166fe02fdfe,
0x40406080402150e100d1410083201c4fe7d0144fe46011afe034afe, 0x10508061a090e100d5c0159fee802effe0302fe, 0xbff0205fef2013bfe550113fe01c1fe0196fe, 0xcff01f9fe022efe640108fe60015ffe51015afe,
0x1010307fe0289fe6a0156fe01bafe, 0xdff030d0c01aefe160116fe0110fe170159fe7c0140fe790162fe, 0xcff0e0f0c019afe0130fe0107fea3cd8b012bfe8f016cfe, 0xaff0c010d0f0c0189fe0133fe00fefeb1bf9a0116fea50174fe,
0x103c7fe0314fe0258fe, 0x9ff020b0b0e0e010b01015efe150138feceeb86120195fee8017bfe, 0x103b7fe0175fe0413fe, 0x8ff020a0c0b0d010d010b010147fe0160febbfd7be5ae140275fe,
0x3ff090b0c0b0d1a0138fe00fefe6db50177fe0199fe0290fe, 0x1010c0b0c0b0d0812011efe0182fe9e0312fe02a9fe, 0x107070b0c0b0d1a0117fe011afe0109fe018bfe018afe02abfe, 0xf170b1e0104fe0529fe02d7fe,
0x4ff02030201060506010b0b0d01100af50138fe688f040181fe080171fe0155fe0184fe, 0x104190c0b1ef6013dfe027cfe0457fe, 0x203060206010a08040b0d01100be60142fe6d880187fe0112fe5d0602e3fe, 0x2a0b0d11ea023cfe05e2fe,
0x1010201040207010a010b0b0d0e03ea0148fef4013dfe480115fe570102f1fe, 0xcff69900185fee80148fe480116fe01c4fe018afe02, 0xdff6a940174fe022ffe5c0111fe54016cfe44013dfe1a, 0x1010378fe028cfe640159fe01b6fe,
0xfff030e0d4e930164fe01010efe0110fe190161fe6b0154fe620128fe35, 0xaff10100d4201cffe012ffe010efe97da7e013bfe7f0166fe, 0xeff798d0271fe010efe97da7e013bfe7f0112fe55, 0x10479fe0324fe0207fe,
0xcff021a0f0f010c01368c013cfe010130fe0103fea8c90101b2fe980106fe6a, 0x10486fe0171fe03bcfe, 0xaff020d1b0e010e010c01378b01013cfe0131fe0102fea9c8920121fe01019efe6b, 0x9ff0b0e12090e1c388b013dfecf620102fe0171fe01b3fe019ffe6c,
0x3ff012afe0370feaac701b3fe019ffe6d, 0x8ff180e12090e0715388a013efe0131fe0100fe0323fe01a0fe6f, 0x7ff17090e12090e1c388a013efed00161fe0172fe01b1fe01a0fe70, 0x6ff08090d29f50270fe00fffe0172fe96011bfea00100fe71,
0x6ff0601070905080a0e111701120a0200fe0131fe00fffe0172fe96011bfea00172fe, 0x101341f0b1f4389013efe0551fe01a2fe73, 0x7ff030705080905070109060801100b0c01120b3889013efed26000fefe010170fe0101affea300fffe74, 0x4ff0843110b1f4301c7fed202cffe0352fe75,
0x4ff05070a0511050709010d09080b0c01120c378a013dfed26100fefe0170fe9a0116fe0101a1fe76, 0x10105040704060e080c28f7026ffe00fefe0170fe01b0fe01a2fe0177, 0x1010704070a0e080c28f7026ffe00fefeb2be01b0fea6fc79, 0x1090b05050e080c28f601026ffe00fefeb2be9c0114fe01a2fe7a,
0x202010302050612060808040c0d010e1a130c01fdfe0130fe00fefeb2be01b0fea70176fe, 0x81807420f0b134401c4fe022efe04c2fe7d, 0x1010203030505010a07070817010c010e0f0b10034487013dfed60158feb3be9c0111fe0101a3fe7e, 0x5ff976d01fdfe022ffe04adfe2f,
0x4ff06846f01cffe160227fe04bafe53, 0x3ff05056b0f6d01c9fe0236fe04c1fe66, 0x1010404052a01f0fe06e5fe010ffe, 0x1030304052401eefe06e3fe011afe,
0x2020304050d01dcfe06e1fe0146fe, 0x10203040506b00128fe0241fe049efe0154fe, 0xaff109b6d01fdfe8e01a1fe6602c5fe0182fe30, 0x8ff0ba86d01f9fe0556fe0189fe34,
0x15ff08010a0c8d6f8c0143fe16ab017cfe180159fe7e013bfe01018ffe54, 0xfff16070b09770f6d8c013dfecd0169fea5cc8d0126fe01019cfe67, 0x6ff1015077e74019efe150207fe0186fe0191fe01b1febb, 0x8ff1615070b017274850119fe15d50132feef0227fe0101b1febc,
0x5ff091513027a7686010afefc0120fe0320fe01a7fed5, 0x7ff0e080d1302080a0167760190fefc0120fe0101fe78e90265fed6, 0x10108221366860171fe0221fe0314fe01b2fef8, 0x3ff1814135f8c0168fe0226fe04c1fe0103fe,
0x6ff0403070706090b1201160b380109fee70129fe0101fe018dfefd880101a8fe0110fe, 0x4ff06010303070706090b1101170a33010afee40131fefc018cfe0100fe810101a8fe011bfe, 0x10105050e160b0f024ca00149fe0230fe018efe016ffe01b1fe012ffe, 0x1010705050908190f021933a06ddc013dfef30802f4fe0101b1fe0130fe,
0x3281259a30144fe06dffe0136fe, 0x2506121045a7013dfe0535fe01aafe013efe, 0x3ff0204030505040507060a081015070b1c0115fec705023cfe02f0fe0101affe040143fe, 0x2070313170810152c01dbfe0241fe02f0fe01b0fe014bfe,
0x60615061110400119fec00158fee902f0fe01b0fe014ffe, 0x107080e170710162a01d9fe0241fe02f0fe01affe0151fe, 0x4ff0133fe6a0213fe7501b8fe04adfe0d, 0x7ff055abd6c01dafe169d0181fe017afe034bfe41,
0x9ff080448b9096d8f0140fec50172fe0172fe01b7fe0199fe59, 0x5ff0a0739bb7101a9fe150206fe0170fe035afeaa, 0x10fee74890112feef044afe01abfec4, 0x10e6760190fefc05e6fed8,
0x101090709051da501f7fe0119fe0295fe0339fef9, 0x103080709051da501f7fe0119fe0295fe0339fefa, 0xc070922a588016ffe0223fe018bfe0338fefc, 0x10102020202030709061ca50106feef010223fe0315fe01aefe01fd,
0x202090709c701f5fe0224fe04c3fe00fffe, 0x9d00107feee011dfe05cafe0100fe, 0x10506060ac601f5fe0225fe04c2fe0101fe, 0x10103c5fe022dfe04cefe,
0x3ff0303a3fe01021dfe017afe0385fe, 0x105b2fe0171fe03a4fe, 0x10106034ffe010204fe0171fe03fefe, 0x20102020103010efe0211fe01021cfe0177fe040efe,
0x5ff018efe03b9fe0177fe0352febd, 0x6bdfe0410fe, 0x6bdfe0411fe, 0x4030103020112fe74019dfe021cfe0175fe0354febe,
0x306bcfe0414fe, 0x548fe0589fe, 0x548fe058afe, 0x8ff0173fe016a920182fe01710101bcfe0324fe0188fe07,
0x11ff1b019bb8016b93010171fe01820101aafe60010dfe01c1fe010181fe1f, 0x4ff01f8fe9203b1fe0324fe0188fe08, 0x9ffcd0124fe920103a0fe60010dfe01c0fe010182fe20, 0x1012001ac0320fe039bfe01bdfe01b9fe,
0x15ff02011e010a010f018b01bb016c920144011afe01990178010cfe1b015ffe72014dfe01018bfe3b, 0xfffdc010129fe910145022dfe010cfe1b015ffe72014cfe01018cfe3c, 0xbff25011f010a010f225701c26d01cffe012efe010bfe9bd6830136fe0101ebfe, 0x1012f010392fe0206fe0318fe0253fe,
0xcff02010c2101051c011901660107b57187010137fe01c20143fee28f0c0199fe0101b2fea7, 0x1011b0173fe747e011ffeec043bfe01bdfec0, 0x1012f100243fe011ffe021afe030dfe01bdfec1, 0x4ff20111097bb747d011efe0219fe030cfe01bffec3,
0x7ff05130c10010f0115050a0d0b5b0701a5fe0b6aa8015dfebd017afee1b11301abfec5, 0x5ff070104040f1b010f0116050a0d0b5b07b4f10b0112fe015dfebd017afee1b11301abfec6, 0x101310172fe757c011dfe0524fe01bffec8, 0x5ff03060617010c0e010f01170f1803570107b3757c0c0111fef20128fe010178fe010190fe1501aafec9,
0x3ff2b0d0d10190f7ab375880111fe0393fe01a6fe01aafeca, 0x1010a08060604040806070d020e021707080f011efe75f5a4f36dbb0178fee5026bfecb, 0x10304050305060608080d0d101907080f0b1c3e0701a5fe0b6ca2010160febb0178fe0193fe1401a9fe01cc, 0x102020405081b010d0d10190f1a5a01acfe0b010efe021cfe00fefe7a0193fe1401a9fece,
0x9050807140e0d10190f374501affe010efe021cfe0178fe01a7fe01a9fecf, 0xe050307070503050e0d10190906110288fea00163feb900fffe79e80268fed0, 0x4ff0203040f13011b10190f1c5abb0208fe021cfe00fffe790195fe1301a8fed1, 0x4ff0498fee702a6fe034dfe,
0x10ff04019d013d013bfe6b8f2e0158fe016f780148fe01015dfe01c4fe0189fe01, 0x9ff11a0013e013bfe6b0215fee80148fe480116fe01c4fe018bfe, 0x5ff09010f0103010215fe016a0214fe01022efe015ffe034dfe05, 0x5ff02a3fe0443fe015ffe034dfe06,
0x10114100218fe6a0215fe7201bcfe04acfe09, 0x260497fe022efe4f045dfe0a, 0x101170f060213fe6a0213fe022dfe04adfe0c, 0x5ff03040606060e018e173f0233fe31014dfef0013dfe0167fe01c3fe0183fe0e,
0x3ff0501020202060613018f173f0135fe00fefe017efef0013dfe0167fe01c3fe0183fe0f, 0x4040d06070b01021bfe6b0211fe022cfe010167fe0345fe11, 0x220b92170173fe6b0211fe7804defe0183fe12, 0x3ff030404040506060b9217400233fe320148fe01f2013bfe0329fe0183fe0113,
0x2041106060b0496fe022efe04acfe15, 0x5180b93170273fe0179fe022efe04acfe16, 0x1080d0610021ffe0277fe022efe04acfe17, 0x3ffd601bc032efe039bfe54016cfe0198fe,
0xfff0301d4011f9e16a36c930175fe018001aefe01016cfe54016cfe44013cfe19, 0x9ff10d601be16a36c0208fe022ffe5c0111fe54016cfe440156fe, 0x11904c1fe022dfe04cbfe, 0xcff09010d010301d201bfb8016b940172fe01810101abfe5f010efe0101c0fe0181fe1d,
0xaff01bafe0124fe9403a0fe5f010dfe0101c1fe0181fe1e, 0x6ff0b0b0a0d01c80fbd1a019cfe0174fe022dfe016dfe5c0164fe4c0137fe21, 0x4ff06010a0b1601c90fbd1aa0fc0174fe022dfe016dfe5c0164fe4c0137fe22, 0x12b025bfe6c0204fe06dcfe24,
0x4ff0205050a010a010a0b01ca0fbdb96c910173fe8601a7fe01016bfe0101bffe0183fe25, 0x130025bfe6c0204fe860656fe26, 0x3ff020506050a0b0a0b01ca010e010175fe6c920172fe8601a8fe016cfe01bffe010182fe27, 0x10401050204050a0b0a0bcb0fbf1b019afe0170fe01022efe016cfe01bffe0183fe0128,
0x1020306060e010a010a0bcb0f0274fe0170fe022ffe650107fe01bffe0183fe2a, 0x6060606080b0b0bca010e010273fe010170fe022ffe650107fe01bffe0183fe2b, 0x3ff02060c07010a0116ca0f017afe026bfe022ffe650107fe01bffe0183fe2c,
]

def thirdCount : ℕ := 3079

def decodeDeltas (fuel : ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ) (fun _ _ => [])
    (fun _ rest before data =>
      let lead := data % 256
      if lead = 0 then []
      else if lead = 255 then
        let count := (data >>> 8) % 256
        List.range' before count ++ rest (before + count) (data >>> 16)
      else if lead = 254 then
        let following := before + (data >>> 8) % 65536
        (following - 1) :: rest following (data >>> 24)
      else
        let following := before + lead
        (following - 1) :: rest following (data >>> 8)) fuel

def thirdSuccessors (state : ℕ) : List ℕ :=
  decodeDeltas 64 0 (thirdEncodedRows.getD state 0)

noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdEncodedSteps.getD (i / 32) 0
  let entry := (block >>> (20 * (i % 32))) % 1048576
  transitionFromCode 9 secondAt entry

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
  change tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 _ = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change (bif pureAt 11 state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1)
    then true else _) = _
  rw [pure, mixed]
  rfl

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

lemma checkedSecondGroups
    (ready : rangeCheck readyForThird 0 secondCount = true)
    (mixed : rangeCheck secondMixedTest 0 secondCount = true)
    (third : rangeCheck thirdTest 0 thirdCount = true) :
    secondGroups.all groupChecked = true := by
  apply List.all_eq_true.mpr
  intro group member
  obtain ⟨block, _, rfl⟩ := List.mem_map.mp member
  apply List.all_eq_true.mpr
  intro state found
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp found
  have hb := List.mem_range.mp hi
  have bound : 4*block+i < secondCount := by omega
  simp only [checkedAfterSecond _ bound ready mixed third, Bool.not_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk0 : rangeCheck readyForThird 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk1 : rangeCheck readyForThird 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk2 : rangeCheck readyForThird 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk3 : rangeCheck readyForThird 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk4 : rangeCheck readyForThird 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk5 : rangeCheck readyForThird 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk6 : rangeCheck readyForThird 96 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk7 : rangeCheck readyForThird 112 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk8 : rangeCheck readyForThird 128 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk9 : rangeCheck readyForThird 144 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk10 : rangeCheck readyForThird 160 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk11 : rangeCheck readyForThird 176 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk12 : rangeCheck readyForThird 192 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk13 : rangeCheck readyForThird 208 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk14 : rangeCheck readyForThird 224 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk15 : rangeCheck readyForThird 240 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk16 : rangeCheck readyForThird 256 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk17 : rangeCheck readyForThird 272 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk18 : rangeCheck readyForThird 288 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk19 : rangeCheck readyForThird 304 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk20 : rangeCheck readyForThird 320 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk21 : rangeCheck readyForThird 336 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk22 : rangeCheck readyForThird 352 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk23 : rangeCheck readyForThird 368 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk24 : rangeCheck readyForThird 384 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk25 : rangeCheck readyForThird 400 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk26 : rangeCheck readyForThird 416 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunk27 : rangeCheck readyForThird 432 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coverageChunkAll : rangeCheck readyForThird 0 secondCount = true := by
  exact (@rangeAppend readyForThird 0 224 219
    (@rangeAppend readyForThird 0 112 112
     (@rangeAppend readyForThird 0 48 64
      (@rangeAppend readyForThird 0 16 32
       coverageChunk0
       (@rangeAppend readyForThird 16 16 16
        coverageChunk1
        coverageChunk2))
      (@rangeAppend readyForThird 48 32 32
       (@rangeAppend readyForThird 48 16 16
        coverageChunk3
        coverageChunk4)
       (@rangeAppend readyForThird 80 16 16
        coverageChunk5
        coverageChunk6)))
     (@rangeAppend readyForThird 112 48 64
      (@rangeAppend readyForThird 112 16 32
       coverageChunk7
       (@rangeAppend readyForThird 128 16 16
        coverageChunk8
        coverageChunk9))
      (@rangeAppend readyForThird 160 32 32
       (@rangeAppend readyForThird 160 16 16
        coverageChunk10
        coverageChunk11)
       (@rangeAppend readyForThird 192 16 16
        coverageChunk12
        coverageChunk13))))
    (@rangeAppend readyForThird 224 112 107
     (@rangeAppend readyForThird 224 48 64
      (@rangeAppend readyForThird 224 16 32
       coverageChunk14
       (@rangeAppend readyForThird 240 16 16
        coverageChunk15
        coverageChunk16))
      (@rangeAppend readyForThird 272 32 32
       (@rangeAppend readyForThird 272 16 16
        coverageChunk17
        coverageChunk18)
       (@rangeAppend readyForThird 304 16 16
        coverageChunk19
        coverageChunk20)))
     (@rangeAppend readyForThird 336 48 59
      (@rangeAppend readyForThird 336 16 32
       coverageChunk21
       (@rangeAppend readyForThird 352 16 16
        coverageChunk22
        coverageChunk23))
      (@rangeAppend readyForThird 384 32 27
       (@rangeAppend readyForThird 384 16 16
        coverageChunk24
        coverageChunk25)
       (@rangeAppend readyForThird 416 16 11
        coverageChunk26
        coverageChunk27)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk0 : rangeCheck secondMixedTest 0 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk1 : rangeCheck secondMixedTest 7 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk2 : rangeCheck secondMixedTest 18 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk3 : rangeCheck secondMixedTest 34 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk4 : rangeCheck secondMixedTest 50 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk5 : rangeCheck secondMixedTest 56 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk6 : rangeCheck secondMixedTest 69 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk7 : rangeCheck secondMixedTest 81 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk8 : rangeCheck secondMixedTest 88 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk9 : rangeCheck secondMixedTest 97 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk10 : rangeCheck secondMixedTest 113 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk11 : rangeCheck secondMixedTest 129 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk12 : rangeCheck secondMixedTest 138 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk13 : rangeCheck secondMixedTest 147 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk14 : rangeCheck secondMixedTest 163 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk15 : rangeCheck secondMixedTest 179 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk16 : rangeCheck secondMixedTest 195 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk17 : rangeCheck secondMixedTest 211 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk18 : rangeCheck secondMixedTest 223 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk19 : rangeCheck secondMixedTest 227 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk20 : rangeCheck secondMixedTest 237 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk21 : rangeCheck secondMixedTest 244 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk22 : rangeCheck secondMixedTest 250 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk23 : rangeCheck secondMixedTest 266 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk24 : rangeCheck secondMixedTest 282 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk25 : rangeCheck secondMixedTest 298 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk26 : rangeCheck secondMixedTest 314 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk27 : rangeCheck secondMixedTest 326 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk28 : rangeCheck secondMixedTest 341 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk29 : rangeCheck secondMixedTest 347 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk30 : rangeCheck secondMixedTest 353 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk31 : rangeCheck secondMixedTest 360 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk32 : rangeCheck secondMixedTest 376 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk33 : rangeCheck secondMixedTest 390 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk34 : rangeCheck secondMixedTest 394 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk35 : rangeCheck secondMixedTest 407 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk36 : rangeCheck secondMixedTest 423 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk37 : rangeCheck secondMixedTest 432 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunk38 : rangeCheck secondMixedTest 439 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixedChunkAll : rangeCheck secondMixedTest 0 secondCount = true := by
  exact (@rangeAppend secondMixedTest 0 227 216
    (@rangeAppend secondMixedTest 0 97 130
     (@rangeAppend secondMixedTest 0 50 47
      (@rangeAppend secondMixedTest 0 18 32
       (@rangeAppend secondMixedTest 0 7 11
        mixedChunk0
        mixedChunk1)
       (@rangeAppend secondMixedTest 18 16 16
        mixedChunk2
        mixedChunk3))
      (@rangeAppend secondMixedTest 50 19 28
       (@rangeAppend secondMixedTest 50 6 13
        mixedChunk4
        mixedChunk5)
       (@rangeAppend secondMixedTest 69 12 16
        mixedChunk6
        (@rangeAppend secondMixedTest 81 7 9
         mixedChunk7
         mixedChunk8))))
     (@rangeAppend secondMixedTest 97 66 64
      (@rangeAppend secondMixedTest 97 32 34
       (@rangeAppend secondMixedTest 97 16 16
        mixedChunk9
        mixedChunk10)
       (@rangeAppend secondMixedTest 129 9 25
        mixedChunk11
        (@rangeAppend secondMixedTest 138 9 16
         mixedChunk12
         mixedChunk13)))
      (@rangeAppend secondMixedTest 163 32 32
       (@rangeAppend secondMixedTest 163 16 16
        mixedChunk14
        mixedChunk15)
       (@rangeAppend secondMixedTest 195 16 16
        mixedChunk16
        (@rangeAppend secondMixedTest 211 12 4
         mixedChunk17
         mixedChunk18)))))
    (@rangeAppend secondMixedTest 227 120 96
     (@rangeAppend secondMixedTest 227 55 65
      (@rangeAppend secondMixedTest 227 17 38
       (@rangeAppend secondMixedTest 227 10 7
        mixedChunk19
        mixedChunk20)
       (@rangeAppend secondMixedTest 244 6 32
        mixedChunk21
        (@rangeAppend secondMixedTest 250 16 16
         mixedChunk22
         mixedChunk23)))
      (@rangeAppend secondMixedTest 282 32 33
       (@rangeAppend secondMixedTest 282 16 16
        mixedChunk24
        mixedChunk25)
       (@rangeAppend secondMixedTest 314 12 21
        mixedChunk26
        (@rangeAppend secondMixedTest 326 15 6
         mixedChunk27
         mixedChunk28))))
     (@rangeAppend secondMixedTest 347 47 49
      (@rangeAppend secondMixedTest 347 13 34
       (@rangeAppend secondMixedTest 347 6 7
        mixedChunk29
        mixedChunk30)
       (@rangeAppend secondMixedTest 360 16 18
        mixedChunk31
        (@rangeAppend secondMixedTest 376 14 4
         mixedChunk32
         mixedChunk33)))
      (@rangeAppend secondMixedTest 394 29 20
       (@rangeAppend secondMixedTest 394 13 16
        mixedChunk34
        mixedChunk35)
       (@rangeAppend secondMixedTest 423 9 11
        mixedChunk36
        (@rangeAppend secondMixedTest 432 7 4
         mixedChunk37
         mixedChunk38))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk0 : rangeCheck thirdTest 0 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk1 : rangeCheck thirdTest 80 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk2 : rangeCheck thirdTest 160 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk3 : rangeCheck thirdTest 240 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk4 : rangeCheck thirdTest 320 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk5 : rangeCheck thirdTest 400 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk6 : rangeCheck thirdTest 480 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk7 : rangeCheck thirdTest 560 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk8 : rangeCheck thirdTest 640 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk9 : rangeCheck thirdTest 720 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk10 : rangeCheck thirdTest 800 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk11 : rangeCheck thirdTest 880 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk12 : rangeCheck thirdTest 960 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk13 : rangeCheck thirdTest 1040 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk14 : rangeCheck thirdTest 1120 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk15 : rangeCheck thirdTest 1200 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk16 : rangeCheck thirdTest 1280 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk17 : rangeCheck thirdTest 1360 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk18 : rangeCheck thirdTest 1440 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk19 : rangeCheck thirdTest 1520 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk20 : rangeCheck thirdTest 1600 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk21 : rangeCheck thirdTest 1680 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk22 : rangeCheck thirdTest 1760 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk23 : rangeCheck thirdTest 1840 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk24 : rangeCheck thirdTest 1920 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk25 : rangeCheck thirdTest 2000 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk26 : rangeCheck thirdTest 2080 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk27 : rangeCheck thirdTest 2160 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk28 : rangeCheck thirdTest 2240 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk29 : rangeCheck thirdTest 2320 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk30 : rangeCheck thirdTest 2400 62 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk31 : rangeCheck thirdTest 2462 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk32 : rangeCheck thirdTest 2542 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk33 : rangeCheck thirdTest 2622 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk34 : rangeCheck thirdTest 2702 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk35 : rangeCheck thirdTest 2782 47 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk36 : rangeCheck thirdTest 2829 45 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk37 : rangeCheck thirdTest 2874 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk38 : rangeCheck thirdTest 2954 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunk39 : rangeCheck thirdTest 3034 45 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem thirdChunkAll : rangeCheck thirdTest 0 thirdCount = true := by
  exact (@rangeAppend thirdTest 0 1600 1479
    (@rangeAppend thirdTest 0 800 800
     (@rangeAppend thirdTest 0 400 400
      (@rangeAppend thirdTest 0 160 240
       (@rangeAppend thirdTest 0 80 80
        thirdChunk0
        thirdChunk1)
       (@rangeAppend thirdTest 160 80 160
        thirdChunk2
        (@rangeAppend thirdTest 240 80 80
         thirdChunk3
         thirdChunk4)))
      (@rangeAppend thirdTest 400 160 240
       (@rangeAppend thirdTest 400 80 80
        thirdChunk5
        thirdChunk6)
       (@rangeAppend thirdTest 560 80 160
        thirdChunk7
        (@rangeAppend thirdTest 640 80 80
         thirdChunk8
         thirdChunk9))))
     (@rangeAppend thirdTest 800 400 400
      (@rangeAppend thirdTest 800 160 240
       (@rangeAppend thirdTest 800 80 80
        thirdChunk10
        thirdChunk11)
       (@rangeAppend thirdTest 960 80 160
        thirdChunk12
        (@rangeAppend thirdTest 1040 80 80
         thirdChunk13
         thirdChunk14)))
      (@rangeAppend thirdTest 1200 160 240
       (@rangeAppend thirdTest 1200 80 80
        thirdChunk15
        thirdChunk16)
       (@rangeAppend thirdTest 1360 80 160
        thirdChunk17
        (@rangeAppend thirdTest 1440 80 80
         thirdChunk18
         thirdChunk19)))))
    (@rangeAppend thirdTest 1600 800 679
     (@rangeAppend thirdTest 1600 400 400
      (@rangeAppend thirdTest 1600 160 240
       (@rangeAppend thirdTest 1600 80 80
        thirdChunk20
        thirdChunk21)
       (@rangeAppend thirdTest 1760 80 160
        thirdChunk22
        (@rangeAppend thirdTest 1840 80 80
         thirdChunk23
         thirdChunk24)))
      (@rangeAppend thirdTest 2000 160 240
       (@rangeAppend thirdTest 2000 80 80
        thirdChunk25
        thirdChunk26)
       (@rangeAppend thirdTest 2160 80 160
        thirdChunk27
        (@rangeAppend thirdTest 2240 80 80
         thirdChunk28
         thirdChunk29))))
     (@rangeAppend thirdTest 2400 382 297
      (@rangeAppend thirdTest 2400 142 240
       (@rangeAppend thirdTest 2400 62 80
        thirdChunk30
        thirdChunk31)
       (@rangeAppend thirdTest 2542 80 160
        thirdChunk32
        (@rangeAppend thirdTest 2622 80 80
         thirdChunk33
         thirdChunk34)))
      (@rangeAppend thirdTest 2782 92 205
       (@rangeAppend thirdTest 2782 47 45
        thirdChunk35
        thirdChunk36)
       (@rangeAppend thirdTest 2874 80 125
        thirdChunk37
        (@rangeAppend thirdTest 2954 80 45
         thirdChunk38
         thirdChunk39))))))

theorem completeSecondTable : secondGroups.all groupChecked = true :=
  checkedSecondGroups coverageChunkAll mixedChunkAll thirdChunkAll

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first0_mixed : mixedSecond (firstAt 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first0_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 0).1 (firstAt 0).2 = false := by
  apply afterFirst_false (firstAt 0) (by decide +kernel) (by decide +kernel) first0_mixed
  apply pureSecond_from_frontier _ (successors0.map secondAt) successors0_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first1_mixed : mixedSecond (firstAt 1) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first1_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 1).1 (firstAt 1).2 = false := by
  apply afterFirst_false (firstAt 1) (by decide +kernel) (by decide +kernel) first1_mixed
  apply pureSecond_from_frontier _ (successors1.map secondAt) successors1_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first2_mixed : mixedSecond (firstAt 2) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first2_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 2).1 (firstAt 2).2 = false := by
  apply afterFirst_false (firstAt 2) (by decide +kernel) (by decide +kernel) first2_mixed
  apply pureSecond_from_frontier _ (successors2.map secondAt) successors2_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first3_mixed : mixedSecond (firstAt 3) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first3_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 3).1 (firstAt 3).2 = false := by
  apply afterFirst_false (firstAt 3) (by decide +kernel) (by decide +kernel) first3_mixed
  apply pureSecond_from_frontier _ (successors3.map secondAt) successors3_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first4_mixed : mixedSecond (firstAt 4) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first4_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 4).1 (firstAt 4).2 = false := by
  apply afterFirst_false (firstAt 4) (by decide +kernel) (by decide +kernel) first4_mixed
  apply pureSecond_from_frontier _ (successors4.map secondAt) successors4_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first5_mixed : mixedSecond (firstAt 5) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first5_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 5).1 (firstAt 5).2 = false := by
  apply afterFirst_false (firstAt 5) (by decide +kernel) (by decide +kernel) first5_mixed
  apply pureSecond_from_frontier _ (successors5.map secondAt) successors5_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first6_mixed : mixedSecond (firstAt 6) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first6_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 6).1 (firstAt 6).2 = false := by
  apply afterFirst_false (firstAt 6) (by decide +kernel) (by decide +kernel) first6_mixed
  apply pureSecond_from_frontier _ (successors6.map secondAt) successors6_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first7_mixed : mixedSecond (firstAt 7) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first7_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 7).1 (firstAt 7).2 = false := by
  apply afterFirst_false (firstAt 7) (by decide +kernel) (by decide +kernel) first7_mixed
  apply pureSecond_from_frontier _ (successors7.map secondAt) successors7_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first8_mixed : mixedSecond (firstAt 8) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first8_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 8).1 (firstAt 8).2 = false := by
  apply afterFirst_false (firstAt 8) (by decide +kernel) (by decide +kernel) first8_mixed
  apply pureSecond_from_frontier _ (successors8.map secondAt) successors8_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first9_mixed : mixedSecond (firstAt 9) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first9_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 9).1 (firstAt 9).2 = false := by
  apply afterFirst_false (firstAt 9) (by decide +kernel) (by decide +kernel) first9_mixed
  apply pureSecond_from_frontier _ (successors9.map secondAt) successors9_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first10_mixed : mixedSecond (firstAt 10) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first10_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 10).1 (firstAt 10).2 = false := by
  apply afterFirst_false (firstAt 10) (by decide +kernel) (by decide +kernel) first10_mixed
  apply pureSecond_from_frontier _ (successors10.map secondAt) successors10_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first11_mixed : mixedSecond (firstAt 11) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first11_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 11).1 (firstAt 11).2 = false := by
  apply afterFirst_false (firstAt 11) (by decide +kernel) (by decide +kernel) first11_mixed
  apply pureSecond_from_frontier _ (successors11.map secondAt) successors11_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first12_mixed : mixedSecond (firstAt 12) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first12_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 12).1 (firstAt 12).2 = false := by
  apply afterFirst_false (firstAt 12) (by decide +kernel) (by decide +kernel) first12_mixed
  apply pureSecond_from_frontier _ (successors12.map secondAt) successors12_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first13_mixed : mixedSecond (firstAt 13) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first13_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 13).1 (firstAt 13).2 = false := by
  apply afterFirst_false (firstAt 13) (by decide +kernel) (by decide +kernel) first13_mixed
  apply pureSecond_from_frontier _ (successors13.map secondAt) successors13_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first14_mixed : mixedSecond (firstAt 14) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first14_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 14).1 (firstAt 14).2 = false := by
  apply afterFirst_false (firstAt 14) (by decide +kernel) (by decide +kernel) first14_mixed
  apply pureSecond_from_frontier _ (successors14.map secondAt) successors14_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first15_mixed : mixedSecond (firstAt 15) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first15_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 15).1 (firstAt 15).2 = false := by
  apply afterFirst_false (firstAt 15) (by decide +kernel) (by decide +kernel) first15_mixed
  apply pureSecond_from_frontier _ (successors15.map secondAt) successors15_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first16_mixed : mixedSecond (firstAt 16) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first16_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 16).1 (firstAt 16).2 = false := by
  apply afterFirst_false (firstAt 16) (by decide +kernel) (by decide +kernel) first16_mixed
  apply pureSecond_from_frontier _ (successors16.map secondAt) successors16_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first17_mixed : mixedSecond (firstAt 17) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first17_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 17).1 (firstAt 17).2 = false := by
  apply afterFirst_false (firstAt 17) (by decide +kernel) (by decide +kernel) first17_mixed
  apply pureSecond_from_frontier _ (successors17.map secondAt) successors17_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first18_mixed : mixedSecond (firstAt 18) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first18_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 18).1 (firstAt 18).2 = false := by
  apply afterFirst_false (firstAt 18) (by decide +kernel) (by decide +kernel) first18_mixed
  apply pureSecond_from_frontier _ (successors18.map secondAt) successors18_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first19_mixed : mixedSecond (firstAt 19) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first19_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 19).1 (firstAt 19).2 = false := by
  apply afterFirst_false (firstAt 19) (by decide +kernel) (by decide +kernel) first19_mixed
  apply pureSecond_from_frontier _ (successors19.map secondAt) successors19_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first20_mixed : mixedSecond (firstAt 20) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first20_checked :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt 20).1 (firstAt 20).2 = false := by
  apply afterFirst_false (firstAt 20) (by decide +kernel) (by decide +kernel) first20_mixed
  apply pureSecond_from_frontier _ (successors20.map secondAt) successors20_complete
  exact checkIndexTable completeSecondTable (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_0_and : chkPairPicked [] rootBounds 0 14 1 0x200000000000000000000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x200000000000000000000000000000000000000000 false opening_0_and opening_0_and_complete
  intro state member
  simp [opening_0_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_0_or : chkPairPicked [] rootBounds 0 14 1 0x200000000000000000000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x200000000000000000000000000000000000000000 true opening_0_or opening_0_or_complete
  intro state member
  simp only [opening_0_or, List.mem_singleton] at member
  subst state
  exact first0_checked

theorem caseBinary_0 : chk [] rootBounds 0 14 1 0x200000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_0_and
  · exact caseBinary_0_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_1_and : chkPairPicked [] rootBounds 0 14 1 0x10000000000000000000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x10000000000000000000000000000000000000000 false opening_1_and opening_1_and_complete
  intro state member
  simp only [opening_1_and, List.mem_singleton] at member
  subst state
  exact first1_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_1_or : chkPairPicked [] rootBounds 0 14 1 0x10000000000000000000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x10000000000000000000000000000000000000000 true opening_1_or opening_1_or_complete
  intro state member
  simp only [opening_1_or, List.mem_singleton] at member
  subst state
  exact first2_checked

theorem caseBinary_1 : chk [] rootBounds 0 14 1 0x10000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_1_and
  · exact caseBinary_1_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_2_and : chkPairPicked [] rootBounds 0 14 1 0x400000000000000000000000000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x400000000000000000000000000000000000000000000000 false opening_2_and opening_2_and_complete
  intro state member
  simp only [opening_2_and, List.mem_singleton] at member
  subst state
  exact first3_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_2_or : chkPairPicked [] rootBounds 0 14 1 0x400000000000000000000000000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x400000000000000000000000000000000000000000000000 true opening_2_or opening_2_or_complete
  intro state member
  simp only [opening_2_or, List.mem_singleton] at member
  subst state
  exact first4_checked

theorem caseBinary_2 : chk [] rootBounds 0 14 1 0x400000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_2_and
  · exact caseBinary_2_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_3_and : chkPairPicked [] rootBounds 0 14 1 0x10000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x10000000000000000 false opening_3_and opening_3_and_complete
  intro state member
  simp only [opening_3_and, List.mem_singleton] at member
  subst state
  exact first5_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_3_or : chkPairPicked [] rootBounds 0 14 1 0x10000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x10000000000000000 true opening_3_or opening_3_or_complete
  intro state member
  simp only [opening_3_or, List.mem_singleton] at member
  subst state
  exact first6_checked

theorem caseBinary_3 : chk [] rootBounds 0 14 1 0x10000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_3_and
  · exact caseBinary_3_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_4_and : chkPairPicked [] rootBounds 0 14 1 0x20000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x20000000000000 false opening_4_and opening_4_and_complete
  intro state member
  simp [opening_4_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_4_or : chkPairPicked [] rootBounds 0 14 1 0x20000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x20000000000000 true opening_4_or opening_4_or_complete
  intro state member
  simp only [opening_4_or, List.mem_singleton] at member
  subst state
  exact first7_checked

theorem caseBinary_4 : chk [] rootBounds 0 14 1 0x20000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_4_and
  · exact caseBinary_4_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_5_and : chkPairPicked [] rootBounds 0 14 1 0x100000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x100000000000000000000000 false opening_5_and opening_5_and_complete
  intro state member
  simp only [opening_5_and, List.mem_singleton] at member
  subst state
  exact first8_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_5_or : chkPairPicked [] rootBounds 0 14 1 0x100000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x100000000000000000000000 true opening_5_or opening_5_or_complete
  intro state member
  simp only [opening_5_or, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact first9_checked
  · exact first10_checked

theorem caseBinary_5 : chk [] rootBounds 0 14 1 0x100000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_5_and
  · exact caseBinary_5_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_6_and : chkPairPicked [] rootBounds 0 14 1 0x80000000000000000000000000000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x80000000000000000000000000000000000000000000000000 false opening_6_and opening_6_and_complete
  intro state member
  simp [opening_6_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_6_or : chkPairPicked [] rootBounds 0 14 1 0x80000000000000000000000000000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x80000000000000000000000000000000000000000000000000 true opening_6_or opening_6_or_complete
  intro state member
  simp only [opening_6_or, List.mem_singleton] at member
  subst state
  exact first11_checked

theorem caseBinary_6 : chk [] rootBounds 0 14 1 0x80000000000000000000000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_6_and
  · exact caseBinary_6_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_7_and : chkPairPicked [] rootBounds 0 14 1 0x1000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x1000000000000000000000000 false opening_7_and opening_7_and_complete
  intro state member
  simp [opening_7_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_7_or : chkPairPicked [] rootBounds 0 14 1 0x1000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x1000000000000000000000000 true opening_7_or opening_7_or_complete
  intro state member
  simp only [opening_7_or, List.mem_singleton] at member
  subst state
  exact first12_checked

theorem caseBinary_7 : chk [] rootBounds 0 14 1 0x1000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_7_and
  · exact caseBinary_7_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_9_and : chkPairPicked [] rootBounds 0 14 1 0x800000000000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x800000000000000000000000000000000 false opening_9_and opening_9_and_complete
  intro state member
  simp [opening_9_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_9_or : chkPairPicked [] rootBounds 0 14 1 0x800000000000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x800000000000000000000000000000000 true opening_9_or opening_9_or_complete
  intro state member
  simp only [opening_9_or, List.mem_singleton] at member
  subst state
  exact first13_checked

theorem caseBinary_9 : chk [] rootBounds 0 14 1 0x800000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_9_and
  · exact caseBinary_9_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_10_and : chkPairPicked [] rootBounds 0 14 1 0x400 0 false = false := by
  apply initialBinary_from_frontier 0x400 false opening_10_and opening_10_and_complete
  intro state member
  simp only [opening_10_and, List.mem_singleton] at member
  subst state
  exact first14_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_10_or : chkPairPicked [] rootBounds 0 14 1 0x400 0 true = false := by
  apply initialBinary_from_frontier 0x400 true opening_10_or opening_10_or_complete
  intro state member
  simp only [opening_10_or, List.mem_singleton] at member
  subst state
  exact first15_checked

theorem caseBinary_10 : chk [] rootBounds 0 14 1 0x400 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_10_and
  · exact caseBinary_10_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_11_and : chkPairPicked [] rootBounds 0 14 1 0x8000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x8000000000000000000000 false opening_11_and opening_11_and_complete
  intro state member
  simp [opening_11_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_11_or : chkPairPicked [] rootBounds 0 14 1 0x8000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x8000000000000000000000 true opening_11_or opening_11_or_complete
  intro state member
  simp only [opening_11_or, List.mem_singleton] at member
  subst state
  exact first16_checked

theorem caseBinary_11 : chk [] rootBounds 0 14 1 0x8000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_11_and
  · exact caseBinary_11_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_12_and : chkPairPicked [] rootBounds 0 14 1 0x40000000000000000000000000000000 0 false = false := by
  apply initialBinary_from_frontier 0x40000000000000000000000000000000 false opening_12_and opening_12_and_complete
  intro state member
  simp only [opening_12_and, List.mem_singleton] at member
  subst state
  exact first17_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_12_or : chkPairPicked [] rootBounds 0 14 1 0x40000000000000000000000000000000 0 true = false := by
  apply initialBinary_from_frontier 0x40000000000000000000000000000000 true opening_12_or opening_12_or_complete
  intro state member
  simp only [opening_12_or, List.mem_singleton] at member
  subst state
  exact first18_checked

theorem caseBinary_12 : chk [] rootBounds 0 14 1 0x40000000000000000000000000000000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_12_and
  · exact caseBinary_12_or

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_13_and : chkPairPicked [] rootBounds 0 14 1 0x80000 0 false = false := by
  apply initialBinary_from_frontier 0x80000 false opening_13_and opening_13_and_complete
  intro state member
  simp [opening_13_and] at member

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caseBinary_13_or : chkPairPicked [] rootBounds 0 14 1 0x80000 0 true = false := by
  apply initialBinary_from_frontier 0x80000 true opening_13_or opening_13_or_complete
  intro state member
  simp only [opening_13_or, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact first19_checked
  · exact first20_checked

theorem caseBinary_13 : chk [] rootBounds 0 14 1 0x80000 0 = false := by
  apply chkPair_picked
  intro kind
  cases kind
  · exact caseBinary_13_and
  · exact caseBinary_13_or

theorem binaryCertificates : BinaryCertificates rootBounds := by
  intro p hp
  simp only [binaryRepresentatives,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0x200000000000000000000000000000000000000000, by decide +kernel,caseBinary_0⟩
  · exact ⟨0x10000000000000000000000000000000000000000, by decide +kernel,caseBinary_1⟩
  · exact ⟨0x400000000000000000000000000000000000000000000000, by decide +kernel,caseBinary_2⟩
  · exact ⟨0x10000000000000000, by decide +kernel,caseBinary_3⟩
  · exact ⟨0x20000000000000, by decide +kernel,caseBinary_4⟩
  · exact ⟨0x100000000000000000000000, by decide +kernel,caseBinary_5⟩
  · exact ⟨0x80000000000000000000000000000000000000000000000000, by decide +kernel,caseBinary_6⟩
  · exact ⟨0x1000000000000000000000000, by decide +kernel,caseBinary_7⟩
  · exact ⟨0x100000000000000000000000, by decide +kernel,caseBinary_5⟩
  · exact ⟨0x800000000000000000000000000000000, by decide +kernel,caseBinary_9⟩
  · exact ⟨0x400, by decide +kernel,caseBinary_10⟩
  · exact ⟨0x8000000000000000000000, by decide +kernel,caseBinary_11⟩
  · exact ⟨0x40000000000000000000000000000000, by decide +kernel,caseBinary_12⟩
  · exact ⟨0x80000, by decide +kernel,caseBinary_13⟩

def subChoices (nn : ℕ) (d : Bool) (l : ℕ) (words : List W) : ℕ → List (List W) :=
  List.rec (fun _ => [[]]) (fun w rest later bits =>
    (later (Nat.lor bits (spC nn d l w.s))).map (w :: ·) ++
      if Nat.beq (Nat.lor bits (covC nn d l rest)) l then later bits else []) words

lemma anySub_choices (nn : ℕ) (d : Bool) (l : ℕ) (words : List W) (bits : ℕ)
    (test : List W → Bool) :
    anySubC nn d l words bits test = (subChoices nn d l words bits).any test := by
  induction words generalizing bits test with
  | nil => simp [anySubC, subChoices]
  | cons w rest ih =>
    let included := Nat.lor bits (spC nn d l w.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l rest)) l
    change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l rest bits test) skip)
        true (st included fun c => anySubC nn d l rest c (fun r => test (w :: r)))) =
      (((subChoices nn d l rest included).map (w :: ·)) ++
        if skip then subChoices nn d l rest bits else []).any test
    simp only [bR, st_eq, ih, List.any_append, List.any_map, Function.comp_def]
    cases skip <;> cases (subChoices nn d l rest included).any (fun r => test (w :: r)) <;> simp

lemma startvC_hasP (nn aa hx hy l m g B K t p H ph : ℕ) (v : List W) :
    startvC nn aa hx hy l m g B K t p H ph v =
      (hasP p v && startvC nn aa hx hy l m g B K t 0 H ph v) := by
  unfold startvC
  rw [show hasP 0 v = true from rfl]
  cases hasP p v <;> rfl

lemma chk_preselected (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (v : List W)
    (chosen : ((subChoices I.NN (pos t) (lz Z) (avl (PZ Q) (mz Z) (rawL E)) 0).filter
      (hasP (pwr E Z))) = [v]) :
    chk E Q Z K t H ph = startvC I.NN I.AA I.HX I.HY (lz Z) (mz Z)
      (pL (Q.map fun _ => 16)) (pL (Q.map fun e => 16 + (K - e.2))) K t 0 H ph v := by
  simp only [chk, frc_eq, st_eq, anySub_choices]
  simp_rw [startvC_hasP _ _ _ _ _ _ _ _ _ _ (pwr E Z)]
  rw [← List.any_filter, chosen]
  simp only [List.any_cons, List.any_nil, Bool.or_false]

abbrev rawNegBounds := rootBounds

def rawNegCofactors (i : ℕ) : List (ℕ × ℕ) := rawNegBounds.map (unaryCharge i)

noncomputable def rawNegWords (i : ℕ) : List W :=
  avl (PZ (rawNegCofactors i)) rootPreparedMask (rawL [(i,0)])

noncomputable def rawNegSlots : ℕ := rootPreparedSlots

noncomputable def rawNegRoot (i : ℕ) : SearchState :=
  (pL ((rawNegCofactors i).map fun e => 16 + (13 - e.2)) - sumc (rawNegWords i), rawNegWords i)

noncomputable def rawNegOpen (i : ℕ) (next : ℕ → List W → Bool) : Bool :=
  nodeC I.NN next false I.AA rootPreparedMask rawNegSlots 13 (rawNegWords i).length
    (rawNegRoot i).1 (rawNegWords i) (fun h xs => pairsC FF h (fs xs))

noncomputable def rawNegAfterOpen : ℕ → List W → Bool :=
  look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 13 12 0

lemma noMixedRaw (nn aa hx hy l m g k z : ℕ) (v : List W)
    (F : ℕ → ℕ → ℕ → List W → Bool) (raw : ∀ w ∈ v, w.r ≠ 0) :
    mvC nn aa hx hy F l m g k 0 z v 0 = false := by
  have noInternal : fr (mkXC nn false l (wstC nn false l v) v) = [] := by
    rw [fr_eq_filter, List.filter_eq_nil_iff]
    intro a ha
    rw [mkXC_map] at ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    exact fun h => raw w hw (Nat.eq_of_beq_eq_true h)
  simp only [mvC, pos, prd, Nat.sub_zero, bR]
  rw [nodeC_as_mode]
  simp [pairsN, noInternal, pairs, scan]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawNegSlots_eq (i : ℕ) : pL ((rawNegCofactors i).map fun _ => 16) = rawNegSlots := by
  simp only [rawNegCofactors, List.map_map, Function.comp_def]
  rfl

lemma rawNegSelection (i : ℕ)
    (selected : ((subChoices I.NN false I.AA (rawNegWords i) 0).filter
      (hasP (pwr [(i,0)] 0))) = [rawNegWords i])
    (hlen : (rawNegWords i).length = 9) (hraw : ∀ w ∈ rawNegWords i, w.r ≠ 0) :
    chk [(i,0)] (rawNegCofactors i) 0 13 0 FF 1 =
      (bif Nat.beq (Nat.land (rawNegRoot i).1 rawNegSlots) rawNegSlots
        then rawNegOpen i rawNegAfterOpen else false) := by
  have hselected : ((subChoices I.NN (pos 0) (lz 0)
      (avl (PZ (rawNegCofactors i)) (mz 0) (rawL [(i,0)])) 0).filter
      (hasP (pwr [(i,0)] 0))) = [rawNegWords i] := by
    rw [show pos 0 = false from rfl, rootPreparedL_eq, rootPreparedMask_eq]
    exact selected
  rw [chk_preselected _ _ _ _ _ _ _ _ hselected, rootPreparedL_eq, rootPreparedMask_eq, rawNegSlots_eq]
  simp only [startvC, hasP, bR, Nat.beq_refl, Bool.cond_true, hlen, child, st_eq]
  simp only [show Nat.ble 9 (Nat.sub 14 0) = true from rfl, Bool.cond_true]
  change (bif Nat.beq (Nat.land (rawNegRoot i).1 rawNegSlots) rawNegSlots then
    topCC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 FF 1 13 0 (rawNegRoot i).1
      (rawNegWords i) else false) = _
  simp only [topCC, hlen, pos, bR, show Nat.ble 9 1 = false from rfl, Bool.cond_false]
  simp only [tstC, hlen, bR, show Nat.beq 9 (Nat.sub 14 0) = false from rfl,
    show Nat.beq 10 (Nat.sub 14 0) = false from rfl, Bool.cond_false]
  have toBool (b : Bool) : (bif b then true else false) = b := by cases b <;> rfl
  simp only [noMixedRaw _ _ _ _ _ _ _ _ _ _ _ hraw, Bool.cond_false,
    Bool.cond_self, toBool, rawNegOpen, rawNegAfterOpen, hlen]
  rfl

lemma rawNegHashFull (x : ℕ) : hb FF x = true := by
  have hm : x % MM < MM := Nat.mod_lt _ (by decide)
  have bit : FF.testBit (x % MM) = true := by simpa [FF] using hm
  have positive : (1 &&& (FF >>> (x % MM))) ≠ 0 := by simpa [Nat.testBit] using bit
  have small : 1 &&& (FF >>> (x % MM)) ≤ 1 := Nat.and_le_left
  rw [hb, Nat.beq_eq]
  change (FF >>> (x % MM)) &&& 1 = 1
  rw [Nat.and_comm]
  omega

lemma rawNegPairs (f : XW → XW → Bool) (xs : List XW) : pairsC FF f xs = pairs f xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [pairsC_eq, ih]
    simp only [rawNegHashFull, Bool.true_and]
    simp only [pairs, bR, scan_eq_any]
    cases rest.any (f a) <;> rfl

noncomputable def rawNegPure (e : ℕ) (state : SearchState) (next : ℕ → List W → Bool) : Bool :=
  nodeC I.NN next false I.AA rootPreparedMask rawNegSlots e state.2.length state.1 state.2 pairsS

lemma rawNegOpening_eq (i : ℕ) (next : ℕ → List W → Bool) :
    rawNegOpen i next = rawNegPure 13 (rawNegRoot i) next := by
  unfold rawNegOpen rawNegPure pairsS
  simp only [rawNegPairs, rawNegRoot]

lemma rawNegPure_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : rawNegPure e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    rawNegPure e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [rawNegPure, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rawNegSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => frontierMissing states)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : frontierMissing states z v
        · exact Bool.noConfusion ((checked _ (frontierMissing_false missed)).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

noncomputable def rawNegMixed (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13)
      I.AA rootPreparedMask rawNegSlots 12 0 z v 0))

noncomputable def rawNegAfterTwo (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 12 11 0 z v))

lemma rawNegAfterOpen_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : rawNegMixed state = false)
    (pure : rawNegPure 12 state (fun z v => rawNegAfterTwo (z,v)) = false) :
    rawNegAfterOpen state.1 state.2 = false := by
  have hl : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [rawNegAfterOpen, show (13 : ℕ) = Nat.succ 12 from rfl, look1C_step, hl, Bool.cond_false]
  change tstC I.NN I.AA I.HX I.HY false I.AA 13 state.2 _ = _
  rw [choose0]
  simp only [rawNegAfterTwo, frc_eq, st_eq] at pure
  simp only [rawNegMixed, frc_eq, st_eq] at mixed
  change (bif rawNegPure 12 state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rawNegSlots 13 12 11 0)
    then true else _) = _
  rw [pure, mixed]
  rfl

noncomputable def rawNegStoredWords (index : ℕ) : List W :=
  let word := rootPreparedWords.getD index ⟨0,0,0,0,3⟩
  addS ⟨rootPreparedMask ^^^ word.s, word.b, word.a, word.c, 3⟩ rootPreparedWords

noncomputable def rawNegStarts : List SearchState := [⟨0x9d295ace759d294a4e94a4e938ca54a56b39ce738d293a4a9494a948d252a465194a30, rawNegStoredWords 5⟩, ⟨0x8d295ace35ad294a4e94a46919d254956b39ce339d291a5292952549ca54a465194232, rawNegStoredWords 7⟩, ⟨0x9ca55ace75aca92a4e9494e939d294a4e739ce739d293a5294952949d2949465194a32, rawNegStoredWords 0⟩]
def rawNegFirstCodes : List ℕ := [
0x10860c8604861202020211c201c2118201821142110210c200c21842104211d911d5119511d11191115111cd118d114d110d11c5118501851145110510c5188505c1058104c10441121c121411d4121011d01150120c020c11cc114c110c12081148110810c81204020411c41144110410c400c418841084060005c004c00440, 0x121e021e121a021a11da01da121611d61196121211d211921152120e020e11ce01ce118e018e114e110e160a120a060a020a15ca11ca05ca01ca158a118a058a018a154a114a150a110a14ca10ca04ca00ca120611c611861146110610c61886,
]

def rawNegSecondCodes : List ℕ := [
0x8e0062801880071001c2006080190e0242808ea0242008e8022a009060041808e60229808860241008a402210086402400010002b8008e0022800880029800860001800c40021000, 0x8c40e21038640f38038c00e20038600e1003c200e42029060a21829040b31028840a19029000b30028800a18028400b080290e0642818ea0642018e8062a01ae4062881882064001, 0x8a6162185b0416410510416b9058e4162905884161905064164b0492a1232849281232048a812c984ac612a984a8612c9049241231048a4122104084133b038c80e31838860f3903, 0x90a1e3287b281ec207ac81e3207aa81e2a079261e31878a61e2187b241e49079041e31078a41e2a068a41a21068a21a2086c621a438590a163a85908163a058a8164185106163985,
0x9082732098a82649898a6262189924244909904264c0892c224308b2a22c288aca224a081282242088c8232a08926223188886224908124224108ac42231089301e4b0790c1e4a87, 0x8ca334a0c90832320c8a832498c8c632298c886323a8b8e82e2a0bb302a4b0ad0c2a4a8ad0a2a328a9282b420a8c82a2a0a92428490a93026cb09b0c264a8990a273289928244a09, 0xb2a46b2118c8464b1092a4232908c8422a10b2c3e4a8f9283e2a0f92c3aca8e9283a320eac63a4b0d92a36328db2836320d8a836c98dd30324c0cd2c324b0c90c334a8c92a32428c, 0x8e072301c0c072281c88072981c86073901cc40724c1a930634b1892c62431892c5f43179305a431590a5632958a852cc1392c4e4a938ca4e4c12b2c4a4a9290a4a4c1192c464311,
0x8e47b291e8847a191e8e07b281e8807a181e8407b081e8ec763a9d8ca763a1d8c8762a1d8e076301d8a076201dc4077081d8ec723a9c8ca723a1c8c8722a1c8e672319c8a672219c, 0xaa8864121ae48639218c48629218ca8232208a88231a08a68221a08c48031208a4822120864822a1f8a67e219fcc47e291f8847e191fcc07e281f8807e181f8407e3a1e8e67a219e, 0xcca8e42238e88f32238a88e41238e48c392390e8a43228ec8ac2a2aea8ab2a29088a3a228c88b2a229048a39220e48ab1228c48a43a190c863b2190a863aa18ca86c221ae886b221, 0xd0a9a3aa68ca9b42268e89a32268a89ac3a590e964325cec963b2590a973aa58ea9632a5908973a258c8962a25b049641258ea923a248a89238a4cc29243a3b0c8ebb2390a8e3aa3,
0x8e2c620b190ebac32ed0cb63b2d90eb2432ccecb23b2cb0ab243abd0eaa3b2a8eaaa32aa90ca642a98caa6c22990ea2bb2890aa23aa890e9e43278ec9ebaa7ac89f43a6d0c9a3b26, 0x64cac0b2902cab8b28e2ca30b2862ca4bb190ec64a31908c63a310e8c6c9b1b06c6b9b12e6c439b1ac6c6a9b1a86c4a1b1086c6c931b04c6b931a84c79931b22c648b1b02c640b1, 0x8eccc3b332e4ccb1338e2ce30b3642ce43b210eca433210cca3b320ecca41b2106ca39b20e6ca31b20c6cac132304c84132ae4c8b9320e4cab1322c4c83132aa4caa132a64c89932, 0x928d2c234908d2ba348e8d2c9b4326d049b4b06d0c1b4106d2b9b42e6d039b4ac6d2a9b4e86d2a1b4924d241348e4d22134c64d19934264d2c8b4922d240b4ae2d238b490ece4333,
0x8e4da2136664da4c35130d64bb512ed643b510ed64a35128d64235108d63a350e8d4c9b5306d4b9b5ea6d4a1b5924d641358e4d62135664d64c34130d24bb412ed243b410ed2ca34, 0x264e248b8b02e240b890ede41b7106de39b7304dc9937902de18b7642de4c36130da4bb612eda43b610eda4a36128da4236108da3a360e8d8c9b6306d8b9b6ec6d8a1b6924da4136, 0x642e64c38130e2cbb892ee2c3b890ee24a38128e24238108e33a388e8e2c9b8326e049b8b06e0c1b8106e3b9b8ae6e2b1b8aa6e2a1b8286e021b8924e241388e4e22138c64e19938, 0x90eea4a3a128eb423a908ea3a3a0e8eac9ba326e849baf06eac1baae6e8b9ba0e6eab1baaa6eaa1ba286e821ba924ea413a8e4ea213ac64e9993a264ea48ba90ce641b98c6e49939,
0x8e8f03a3cf26f2c9bcb06f0c1bc106f2b9bc2e6f039bcac6f2a9bca86f0a1bc086f2493c904f2393c884f3193c664f0993c8ecee39bb8c6ecb13b642eecc3a930ea4bba12eeb43ba, 0x8ecf43b3d906f441bd8e6f439bd8c6f431bdb02f4c0bd102f6b8bd2e2f438bdac2f4b0bd0c2f6a8bda82f698bd262f418bdd30f24c3cd2ef24bbc90ef043bcd28f24a3c908f0423c, 0x90efe4a3f908fe3a3f0e8fcb9bf286fe3b3e0ecfa3abe0eafa32be0cafa3a3e8c8fa2a3e8e6fa31be8a6fa21be8e4f8393e8c4f8313e8a4f8293e884fa193e90ef443bd90cf4433d, 0x90b063ac18cb06ca41b090642418e90632418a906c9c192706c1c190706b9c18e704b9c10e706b1c18c706a9c18a706a1c188706c941ae50643408ed0241c08e70231c00c7024bbf,
0x8e712b1c48c712a9c48a712a1c488710a1c408712c14492f0e43c39290e42438e90c3a432e70ca1c392f0a43c29290a42428e9083a422e708a1c292f0643c192d0643418ed064ac1, 0xb071641c5ae71639c5ac71631c5aa71629c5a871621c52871421c5b2f124bc4b0f124b4490d123b4492b1242c48eb1232c49291242448e91232448a912c9c492712c1c490712b9c4, 0x8c91a2a46b271a49c6b071a41c6ae71a39c62e71839c6ac71a31c6aa71a29c6a871a21c6b31164bc592d1643458ed164ac590b163ac58cb164a45909163a458c9162a45b271649c5, 0xac522a948a85224c4792f1e43c710f1ec9c7b071eb9c7b251ec1473051c4147ae51cb9470e51eb147aa51f9947d311a4bc690f1a4b4690d1a3b4692b1a42c68eb1a32c69091a3a46,
0x90d28434a8ed283b4a9072a39ca8c72a4c49131264bc912f2643c910f264a49909263a4932724c1c92e72643c890d223b480ed2242c88eb2232c8909223a488c9222a48b0522b948, 0x32734c1cd2e73643cc10f32434c10d323b4c0ed3241cc1073239cc0e73231cc0c7324c4b1312e4bcb12f2e43cb10f2e4a4b1292e424b1092e3a4b0e92cc9cb3072cb9cb90f2843ca, 0x1273e41cfcc73ec94f3253c494fb053fb14f90f3843ce90d38434e8ed383b4e9073841ce8e73839ce8c73831ce931344c4d92f344bcd90f3443cd929344a4d90934424d8e9343a4d, 0x8c74a4c51131464bd190f464a51129464251109463a5132744c1d190f42c2d0aeb4242508e9432a509074239d0ca74221d09054041508e54329508854219509313ecb4fb0d3e49cf,
0x32756c35490b5332d49095332548a95241d4cc75229d4887524154cc5522954885521954b2f4e4b53ced4e49d3ce74e31d3b254fb95390f4843d290d4a3b529074841d28e74839d2, 0x8a76221d8ce56231588a56221588656343d7d0d5e3b57d075e39d78c75fc15790f5a435610d5a3b569075841d68e75a31d60c75a4c5592f544bd590f564a551295642558e9543a55, 0x12f6e43db10f6e4a5b9096e3a5b90f6a435a8ed683b5a9076a39da0e76a31da0c76a4c5992f6643d910f664a599096442598e9643a59ced633ad88cb633a588c9622a58ce76231d8, 0x1317acbde92f7a43de92d7a435e8ed7a4ade90b7a3ade8cb7a4a5eb097a425e90f7642dd8eb76425d8e9762a5d931704c5c92f704bdc90f7043dc92972425c8e9724c5b1316e4bdb,
0x90b8a3ae28cb8b43e18ed863ae18cb863a618c9862a61b31824c6092f804be0d0f8243e092d8243608ed824ae090b823ae08cb824a60329824b5f92b7e32df9297e325f8a97e4c5e, 0x90fa24c671319e4be790f9e4c6692f9a43e610f9a4c6592f944be590f964c64131924be490f924c631318e4be312f8e43e310f8e4c62d2f8a4be290f8843e292d8a43628ed8a4ae2, 0x34c6d931b64c6b92faec3eab0daa4c6992fa643e910fa64c6892fa04be8,
]

def rawNegSecondRows : List ℕ := [
0x1aff, 0xfff1b, 0xcff2b, 0xdff38,
0xfff2b1a01, 0x13ff1e0d0f1a02, 0x5ff14104303, 0x14ff0613100e0d0f180104,
0x12ff150513100e0d0f1806, 0x10ff1201140513100e0d0f1807, 0xbff11111517011e0d0f170108, 0x1010c10112c520a,
0x10ff0e10111501150112010d0d0f160b, 0x6ff111d111529400c, 0x4ff171d2609202b150d, 0x3ff05162f1409202b150e,
0x4ff100e1e111429400f, 0x5ff05040b0e110d1113011a0f120d2110, 0x3ff05010409060e110d1112011b0f120d2111, 0x3ff2a110d11121c210d0f1212,
0x4b112e4f13, 0x1011704060d110c11131b11110d2014, 0x301040d0e0d0b060c1113100b11110d101015, 0x1030a230b060c11131b221d1016,
0x3ff0a0405040504050b01110c11131b121e0f1017, 0x2020e1d0d050c11131b231c1018, 0x20102080404050504050901120c11131b131e0e1019, 0x1060504041b01130c11131b241b101a,
0x12fff8, 0xbff010bfe, 0xcff0117fe, 0xbff0124fe,
0xaff190c1201f8, 0xeff0b0c0c0c1101fa, 0xeff0f0a0c0c0c11fc, 0xcff0e010e0a0c0c0c11fd,
0x4ff0d0d193500fefe, 0xeff050c0d0f01090d0c0c1000fffe, 0x9ff0e01040c0d0f170c0c100100fe, 0x4ff0a0d110d0f0b0c0c1c0101fe,
0x3ff05090d110d0f0b0c0c1c0102fe, 0x3ff110d110d0f0b0c0c1c0103fe, 0x3ff04100d110d0f170c1c0104fe, 0x403100d09080d0f0c0b0c100c0105fe,
0x4ff040904060c01110d0f0c0b1c0c0106fe, 0x10507050a0c0b070d0f240f0c0107fe, 0x1020301040805050b01120d0f0d0b1b0c0108fe, 0x1030909050b0d060d0f250e0c0109fe,
0x405010804050a01130d0f330c010afe, 0x1aff019ffe, 0x1fff01bafe, 0x8ff01dafe,
0x24ff291b019ffe, 0x15ff0208fe, 0x15ff021efe, 0x8ff0234fe,
0x22ff5901281b01a0fe, 0x4ff0260fe, 0x20ff27015828011a0101a1fe, 0x4ff0286fe,
0x1fff2626580127011a0101a3fe, 0x19ff2025265801e8fe, 0x14ff39061f071f0d16161f0f01dafe, 0x7ff02dafe,
0x5ff552526584501a5fe, 0x1eff5a25260e16161e4501a6fe, 0x7ff0307fe, 0x7ff030ffe,
0x1dff2f59252624161e113401a7fe, 0x1bff1e87252624161e113401a8fe, 0x1bff685825261014161e4501a9fe, 0x10ff381d3e2e01192526871601aafe,
0xfff481d0a0874250d191114164c1601abfe, 0xbff211c1a1d303d02adfe, 0x8ff481a1d3057252659012d1601acfe, 0xeff351b1a1d303e02aefe,
0xbff5e1a1d305825263c1d2e1601adfe, 0xeff4f1a1a1d303f02affe, 0xbff771a1d3059252627322e1601aefe, 0xbff1b1b151d011967152a0119257f2e1601affe,
0xfff8d4808175911144e161b17171601b0fe, 0xaff1c67191c1d2e4002b2fe, 0x8ffa61c1d2e5a252701572e1601b1fe, 0x7ff14361b151b01bf01194c582e01c8fe,
0xeff0176fe4c291619191501c9fe, 0x9ff172f651a1c1d2e3f02b5fe, 0x8ffce1c1d2e59260125582e1801b2fe, 0x6ff132a1a011b1b15d9013f26582e01cbfe,
0xeff01c2fe261a1116172e01ccfe, 0x8ff16292d67191c1d2e3e02b8fe, 0x8fff41c1d2e59012426582e1a01b3fe, 0x8ff21292c671f1c1d2e3302c5fe,
0x8ff29292c671f1c1d2e3302c6fe, 0x5ff1b091f09540c0f0c95082706150e1a255216441a01b4fe, 0xeff0f0908090e0809090f080b091009100c0f0c0d091109161c1d1608101706150e1a180d190d012b1616012d1a01b5fe, 0x5ff2e094a09290c0f0cdf0e1a4b2c164401d0fe,
0xeff14010e0907090f0809090f080a0911090f0c0f0c0e091109161c1d16080f011706140e1a190c01251e0e1616012d1b01b6fe, 0x6ff0f5b09210911090f0c0f0cdf0e3f261e0e164401d2fe, 0xbff15140f0907090f0808091008090911090f0c0f0c0f091109321d16080f1806130e1a01241c0a1e0e1616012d1c01b7fe, 0x5ff0c070d080c092e292b68201b1d2d3102cdfe,
0x3ff11070d080c37292b68201b1d2d3102cefe, 0x3ff14070d140a2d292b68201b1d2d3102cffe, 0x3ff1714090b0a2d292b68201b1d2d3102d0fe, 0x3ff1a080c090b37292b68201b1d2d3102d1fe,
0x3ff1d080c140b2c292b68201b1d2d3102d2fe, 0x3ff20140a0a0b2c292b68201b1d2d3102d3fe, 0x1040c0e053e0907097b0c0f0c0f090a10a6151a771616230b01d4fe, 0x105050403050405050a0a011415090709090f0809090f09090a100e0c0f0c0f090a1011381d08081f060b151a1c090125012b1616230b1d01b8fe,
0xc09192a093009520c0f0c0f09c0153f5216162e01d6fe, 0x10202020405030405040501130d080114090809090f07090a0f09090a100d0c0f0c0f090b10111c1b011d08081f060a151a01241f07012b1616240a1e01b9fe, 0xc042e15095b09270c0f0c0f09c015652c16162e01d8fe, 0x1010202040404040404060c0701140f06090909090f07090a0f08090b100c0c0f0c0f090c10111c77151a0124012523091616250901d9fe,
]

noncomputable def rawNegStart (i : ℕ) : SearchState := rawNegStarts.getD i (0, [])

noncomputable def rawNegFirst (i : ℕ) : SearchState :=
  let block := rawNegFirstCodes.getD (i / 64) 0
  transitionFromCode 2 rawNegStart ((block >>> (16 * (i % 64))) % 65536)

noncomputable def rawNegSecond (i : ℕ) : SearchState :=
  let block := rawNegSecondCodes.getD (i / 32) 0
  transitionFromCode 7 rawNegFirst ((block >>> (18 * (i % 32))) % 262144)

def rawNegSuccessors (i : ℕ) : List ℕ := decodeDeltas 64 0 (rawNegSecondRows.getD i 0)

noncomputable def rawNegCover (i : ℕ) : Bool :=
  let state := rawNegFirst i
  let ids := rawNegSuccessors i
  (!rawNegPure 12 state (frontierMissing (ids.map rawNegSecond))) &&
    ((ids.all fun j => decide (j < 1229)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def rawNegMixedTest (i : ℕ) : Bool := !rawNegMixed (rawNegFirst i)
noncomputable def rawNegSecondTest (i : ℕ) : Bool := !rawNegAfterTwo (rawNegSecond i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegStored0 : rawNegRoot 0 = rawNegStart 0 := Eq.refl _

noncomputable def rawNegOpening0 : List SearchState := (List.range' 0 28).map rawNegFirst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegOpening0_complete :
    rawNegPure 13 (rawNegStart 0) (frontierMissing rawNegOpening0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegStored2 : rawNegRoot 2 = rawNegStart 1 := Eq.refl _

noncomputable def rawNegOpening2 : List SearchState := (List.range' 28 21).map rawNegFirst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegOpening2_complete :
    rawNegPure 13 (rawNegStart 1) (frontierMissing rawNegOpening2) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegStored7 : rawNegRoot 7 = rawNegStart 2 := Eq.refl _

noncomputable def rawNegOpening7 : List SearchState := (List.range' 49 63).map rawNegFirst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegOpening7_complete :
    rawNegPure 13 (rawNegStart 2) (frontierMissing rawNegOpening7) = false := by decide +kernel

lemma rawNegFirst_checked (i : ℕ) (hi : i < 112)
    (coverage : rangeCheck rawNegCover 0 112 = true)
    (mixed : rangeCheck rawNegMixedTest 0 112 = true)
    (second : rangeCheck rawNegSecondTest 0 1229 = true) :
    rawNegAfterOpen (rawNegFirst i).1 (rawNegFirst i).2 = false := by
  have h := rangeCheck_at coverage hi
  simp only [rawNegCover, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨complete, valid, htwo, hsmall⟩ := h
  refine rawNegAfterOpen_false (rawNegFirst i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine rawNegPure_from_frontier 12 (rawNegFirst i) ((rawNegSuccessors i).map rawNegSecond)
    rawNegAfterTwo (boolOfNeg complete) ?_
  intro state member
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
  have bound : j < 1229 := of_decide_eq_true (List.all_eq_true.mp valid j hj)
  exact boolOfNeg (rangeCheck_at second bound)

lemma rawNeg_checked (i root start count : ℕ)
    (selected : ((subChoices I.NN false I.AA (rawNegWords i) 0).filter
      (hasP (pwr [(i,0)] 0))) = [rawNegWords i])
    (len : (rawNegWords i).length = 9) (raw : ∀ w ∈ rawNegWords i, w.r ≠ 0)
    (stored : rawNegRoot i = rawNegStart root) (bound : start+count ≤ 112)
    (opening : rawNegPure 13 (rawNegStart root)
      (frontierMissing ((List.range' start count).map rawNegFirst)) = false)
    (coverage : rangeCheck rawNegCover 0 112 = true)
    (mixed : rangeCheck rawNegMixedTest 0 112 = true)
    (second : rangeCheck rawNegSecondTest 0 1229 = true) :
    chk [(i,0)] (rawNegCofactors i) 0 13 0 FF 1 = false := by
  rw [rawNegSelection i selected len raw, rawNegOpening_eq, stored]
  have result := rawNegPure_from_frontier 13 (rawNegStart root)
    ((List.range' start count).map rawNegFirst) (fun s => rawNegAfterOpen s.1 s.2) opening (by
      intro state h
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      have hbound := (List.mem_range'_1.mp hj).2
      exact rawNegFirst_checked j (by omega) coverage mixed second)
  rw [result]
  cases Nat.beq (Nat.land (rawNegStart root).1 rawNegSlots) rawNegSlots <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover0 : rangeCheck rawNegCover 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover1 : rangeCheck rawNegCover 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover2 : rangeCheck rawNegCover 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover3 : rangeCheck rawNegCover 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover4 : rangeCheck rawNegCover 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover5 : rangeCheck rawNegCover 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCover6 : rangeCheck rawNegCover 96 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negCoverAll : rangeCheck rawNegCover 0 112 = true :=
  (@rangeAppend rawNegCover 0 48 64
    (@rangeAppend rawNegCover 0 16 32
     negCover0
     (@rangeAppend rawNegCover 16 16 16
      negCover1
      negCover2))
    (@rangeAppend rawNegCover 48 32 32
     (@rangeAppend rawNegCover 48 16 16
      negCover3
      negCover4)
     (@rangeAppend rawNegCover 80 16 16
      negCover5
      negCover6)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed0 : rangeCheck rawNegMixedTest 0 56 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixed1 : rangeCheck rawNegMixedTest 56 56 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negMixedAll : rangeCheck rawNegMixedTest 0 112 = true :=
  (@rangeAppend rawNegMixedTest 0 56 56
    negMixed0
    negMixed1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond0 : rangeCheck rawNegSecondTest 0 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond1 : rangeCheck rawNegSecondTest 96 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond2 : rangeCheck rawNegSecondTest 192 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond3 : rangeCheck rawNegSecondTest 288 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond4 : rangeCheck rawNegSecondTest 384 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond5 : rangeCheck rawNegSecondTest 480 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond6 : rangeCheck rawNegSecondTest 576 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond7 : rangeCheck rawNegSecondTest 672 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond8 : rangeCheck rawNegSecondTest 768 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond9 : rangeCheck rawNegSecondTest 864 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond10 : rangeCheck rawNegSecondTest 960 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond11 : rangeCheck rawNegSecondTest 1056 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecond12 : rangeCheck rawNegSecondTest 1152 77 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem negSecondAll : rangeCheck rawNegSecondTest 0 1229 = true :=
  (@rangeAppend rawNegSecondTest 0 576 653
    (@rangeAppend rawNegSecondTest 0 288 288
     (@rangeAppend rawNegSecondTest 0 96 192
      negSecond0
      (@rangeAppend rawNegSecondTest 96 96 96
       negSecond1
       negSecond2))
     (@rangeAppend rawNegSecondTest 288 96 192
      negSecond3
      (@rangeAppend rawNegSecondTest 384 96 96
       negSecond4
       negSecond5)))
    (@rangeAppend rawNegSecondTest 576 288 365
     (@rangeAppend rawNegSecondTest 576 96 192
      negSecond6
      (@rangeAppend rawNegSecondTest 672 96 96
       negSecond7
       negSecond8))
     (@rangeAppend rawNegSecondTest 864 192 173
      (@rangeAppend rawNegSecondTest 864 96 96
       negSecond9
       negSecond10)
      (@rangeAppend rawNegSecondTest 1056 96 77
       negSecond11
       negSecond12))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase0 : chk [(0,0)] (rawNegCofactors 0) 0 13 0 FF 1 = false := by
  have noInternal : (rawNegWords 0).all (fun w => !Nat.beq w.r 0) = true := by decide +kernel
  refine rawNeg_checked 0 0 0 28 rfl rfl ?_ rawNegStored0
    (by decide) rawNegOpening0_complete negCoverAll negMixedAll negSecondAll
  intro w hw h
  have bad := List.all_eq_true.mp noInternal w hw
  simp [h] at bad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase2 : chk [(2,0)] (rawNegCofactors 2) 0 13 0 FF 1 = false := by
  have noInternal : (rawNegWords 2).all (fun w => !Nat.beq w.r 0) = true := by decide +kernel
  refine rawNeg_checked 2 1 28 21 rfl rfl ?_ rawNegStored2
    (by decide) rawNegOpening2_complete negCoverAll negMixedAll negSecondAll
  intro w hw h
  have bad := List.all_eq_true.mp noInternal w hw
  simp [h] at bad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase7 : chk [(7,0)] (rawNegCofactors 7) 0 13 0 FF 1 = false := by
  have noInternal : (rawNegWords 7).all (fun w => !Nat.beq w.r 0) = true := by decide +kernel
  refine rawNeg_checked 7 2 49 63 rfl rfl ?_ rawNegStored7
    (by decide) rawNegOpening7_complete negCoverAll negMixedAll negSecondAll
  intro w hw h
  have bad := List.all_eq_true.mp noInternal w hw
  simp [h] at bad

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase1 : chk [(1,0)] (rawNegCofactors 1) 0 13 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawNegCase6 : chk [(6,0)] (rawNegCofactors 6) 0 13 0 FF 1 = false := by
  rw [← chkFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unaryCertificates : UnaryCertificates :=
  build_unary_strong_certificates rootBounds_p rootBounds_I iroot
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by
      intro i hi
      simp only [unaryRepresentatives,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact rawNegCase0
      · exact rawNegCase1
      · exact rawNegCase2
      · exact rawNegCase6
      · exact rawNegCase7
    )

theorem onFinal : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfit hone hev
  have hf : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x :=
    fun x => (hev x).trans (f_graph x).symm
  by_cases hnot : ∃ g ∈ gates, g.op = .not
  · have hc : notCount gates = 1 := Nat.le_antisymm (count_le_one hone) (count_pos hnot)
    have hge : 15 ≤ gates.length := by
      by_contra hlt
      obtain ⟨k,t,ht,hk,S,hS,hl⟩ := fullBridge gates o (fanInTwo_of hfit) hf
      by_cases hsmall : k < 14
      · exact fullLower iroot hsmall (hl.sol.mono le_rfl hS)
      have he : k = 14 := by omega
      have ht1 : t = 1 := by omega
      subst k
      subst t
      exact fullExclusion rootBounds_p rootBounds_I iroot binaryCertificates unaryCertificates hS hl
    have hw : witness.length = 15 := rfl
    exact ⟨witness, 22, witness_basis, by omega, fun x => (witness_eval x).trans (f_graph x)⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨ho, hlen⟩ := hfit g hg
    refine ⟨?_, hlen⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim

end inst_data
end PEqualNP.Outside.L_meta_35240_aux

theorem PEqualNP.Outside.L_meta_35240 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_35240_aux.onFinal
