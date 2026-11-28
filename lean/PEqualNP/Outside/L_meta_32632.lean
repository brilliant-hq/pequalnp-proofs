import PEqualNP.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn

namespace PEqualNP.Outside.L_meta_32632
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
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 694
def AA : Nat := 0x1ffff7dffff7def7fffeffffbdf77fffdf7deffffbdffff77dbfffef7ddffff77afbbdffeb6d5ad56afff6d6b5afff5b5ffefff5b5b555abffdb6fff6dbffdaad6b6aafff5ffefff6db6dbffdb6fff0000000000000000
def HX : Nat := 0x1492a52a950009294a5000a4a001000a4a4aaa540024900092400255294955000a001000924924002490000000000000000000
def HY : Nat := 0x200008200008210800010000420880002082100004200008824000108220000885044200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
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
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
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
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
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
def segsX : List (ℕ × ℕ) := [(63, 76), (76, 79), (79, 82), (82, 85), (85, 98), (98, 101), (101, 104), (104, 107), (107, 110), (110, 113), (113, 116), (116, 119), (119, 132), (132, 145), (145, 147), (147, 160), (160, 162), (162, 164), (164, 166), (166, 168), (168, 171), (171, 174), (174, 176), (176, 179), (179, 181), (181, 184), (184, 186), (186, 188), (188, 190), (190, 193), (193, 206), (206, 209), (209, 212), (212, 215), (215, 228), (228, 231), (231, 234), (234, 237), (237, 250), (250, 252), (252, 254), (254, 257), (257, 259), (259, 261), (261, 263), (263, 265), (265, 267), (267, 270), (270, 273), (273, 275), (275, 278), (278, 281), (281, 283), (283, 296), (296, 309), (309, 311), (311, 314), (314, 317), (317, 319), (319, 332), (332, 334), (334, 337), (337, 339), (339, 342), (342, 344), (344, 347), (347, 349), (349, 352), (352, 355), (355, 368), (368, 370), (370, 372), (372, 375), (375, 377), (377, 379), (379, 381), (381, 384), (384, 386), (386, 389), (389, 391), (391, 393), (393, 396), (396, 399), (399, 402), (402, 404)]
def segsY : List (ℕ × ℕ) := [(404, 417), (417, 422), (422, 426), (426, 432), (432, 434), (434, 439), (439, 443), (443, 461), (461, 465), (465, 471), (471, 476), (476, 494), (494, 497), (497, 503), (503, 507), (507, 525), (525, 530), (530, 548), (548, 553), (553, 559), (559, 565), (565, 583), (583, 587), (587, 593), (593, 598), (598, 616), (616, 635), (635, 640), (640, 645), (645, 651), (651, 669), (669, 675), (675, 693)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
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
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
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
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
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
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
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
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
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
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
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
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
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
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
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
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
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
  simp only [cv, bR, hcov, cond_true] at h
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
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
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
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
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
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
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
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
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
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : L_meta_32632.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
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
    {go : (L_meta_32632.X → L_meta_32632.X → Bool) → List L_meta_32632.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_32632.X.s e
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
  | zero => intro k t z v S h; simp [look] at h
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_32632.X → L_meta_32632.X → Bool) → List L_meta_32632.X → Bool,
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
  | zero => intro k t z v S h; simp [look1] at h
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32632.X.s e))
end sound
def rawP : List ℕ := [0x7fffc1f0000000007fffc1e3e0f00000000000000280084000490500a0058000001020120000489201600808008805100a0058105860242480980000000000000000112504092504210424a08328411044941042088a84999d07c022261044539b078f83c24a000021000000006300000434000fff000040408000000006dbffc0a0600a20004000fff0c3618001b6fffe7fc7c7f7366f997, 0x3fffe07c00000000000000000000000ffff81f07fffdc03ee00000000210000218000108229210470230010404081066184298610c0000208a043108704308209210e6184500000000000000000220a08120a08420841496a501f008128208410150820261049495c07c062ae700fb8041400018c000000010842000585ffe00000430102000186000618000201086280005ffe0006186dbffd860007ad7c5a4339e763f, 0x7fffc07fffc078000003fffef000000000003fffe07fffdc00ffffbc007fffdde8000000218468040b2798581632e96c65e32f001204560d366c34e9b0d3c2090240ab4f869e34f1b01b0d6c6c35d00000000000000001f01001b81001e00082086a83c0000240410844660088cc70010994f00042ca77a00000208611a01020006160580005b0000000005811580001b00006c000182c0b02afff00000006c06c0001b0000e043fb3db69a4b40, 0x1ffff01f03fffef00000000ffffbdf70000000000000000000010201509001281b00003401a1040050000642481b0000686a002da002a005402a1a68000c84903600000000000000000444110244110841108220c0882252b8407c06546bc420900818d16f7dc840300808048820014004080006c005afff000000000430014000001b6fff000001a800b68000000000006db000001b6ffff2cadff78dfc99f9, 0x7fffdf0000000000000001ffff7c003fffef7fffddf600000000000000000000000090001581161b5ac011c00023811c1200051224780011c0004706ab5800012c025812c134d244f00013800000000000000000808221b8827c00021040301104443389f00046473c8c8e77d810180080080c100108010406c0005600006d6b000000000000005800155abffc00000000001aad6000000000000006db6dbffc00000bdd98fd45fbddbce, 0x1ffff800000001ffff7df780000000000000000000000000000000000004000010a0580000000500000a005016c490000240000900002404a2509200b001600b0000000280000a000000000000000001081c40c01c210863e38440e2080623f1f7de80780100f0210201e0210100f02122109038b0000056afff0000000000000000005b5b4000000000000000001aad6b6aafff5ffefff0000000000000079f7fb78e3cfe7f9, 0x7fffdf000000001ffffbfffef7dc000000000000000000000000000000000000000000002d256b4002600000002600004c02600496d0448b80492e0124b80000000002c005802c0000000b00002c000000000000000001f0e07d00e0400043fc087f03df703c0082000780100f0042101e0042080f0002040101c0b6d5ad0000000000000000000000005b5b555abffdb6fff6dbffc00000000000000000000000000000000cfca7e9bbcbbbebc, 0x7fffdf7fffdf7bc00000000000000000000000000000000000000000000000000000000029b54a450b80125284380048700380000000000c0000300000c00000000003000600300000000c000030000000000000000001ff007dff007def7c000f80001007c0010410f80021f0000403e0008411f0004408221e00b6d5ad56afff6d6b5afff5b5ffefff0000000000000000000000000000000000000000000000000000000d72c1f6eedc164ff]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x1ffff7dffff7def7fffeffffbdf77fffdf7deffffbdffff77dbfffef7ddffff77afbbdffeb6d5ad56afff6d6b5afff5b5ffefff5b5b555abffdb6fff6dbffdaad6b6aafff5ffefff6db6dbffdb6fffffffffffffffffff
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
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
  have h := List.all_eq_true.1 raw_good w hw
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
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
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
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
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
    have : Std.Symm (fun a b : L_meta_32632.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32632.X.s e)) hpb
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
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
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
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
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
lemma apI {A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp [] e.1 e.2) (hb : ∀ e ∈ B, Imp [] e.1 e.2) : ∀ e ∈ A ++ B, Imp [] e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
noncomputable def okS (T : List (ℕ × ℕ)) (Z K : ℕ) (p : ℕ × ℕ × ℕ) : Bool := !chk [] (pr T Z) Z K p.1 p.2.1 p.2.2
def selT (M : List (ℕ × ℕ × ℕ)) (t : ℕ) : List (ℕ × ℕ) := (M.filter (fun p => Nat.beq p.1 t)).map Prod.snd
def okP (T : List (ℕ × ℕ)) (Z L : ℕ) (M : List (ℕ × ℕ × ℕ)) : Bool := pOk Z (pr T Z) && Nat.ble L 15 && (List.range L).all (fun t => mFull (selT M t))
lemma imp_run {T : List (ℕ × ℕ)} {Z L : ℕ} (M : List (ℕ × ℕ × ℕ)) (hT : ∀ e ∈ T, Imp [] e.1 e.2) (hp : okP T Z L M = true) (h : M.all (okS T Z (L - 1)) = true) : Imp [] Z L := by
  simp only [okP, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp
  refine imp_of (Or.inl rfl) hp.1.1 (Nat.le_of_ble_eq_true hp.1.2) (fun e he => hT e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ⟨selT M t, hp.2 t ht, fun p hq => ?_⟩)
  simp only [selT, List.mem_map, List.mem_filter] at hq
  obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hq
  have h1 := List.all_eq_true.1 h q hq1
  have h2 : q.1 = t := Nat.eq_of_beq_eq_true hq2
  simp only [okS, Bool.not_eq_true'] at h1
  rw [← h2]; exact h1
lemma appS {T : List (ℕ × ℕ)} {Z K : ℕ} {A B : List (ℕ × ℕ × ℕ)} (ha : A.all (okS T Z K) = true) (hb : B.all (okS T Z K) = true) : (A ++ B).all (okS T Z K) = true := by
  rw [List.all_append, ha, hb]; rfl
lemma one1 {Z L : ℕ} (h : Imp [] Z L) : ∀ e ∈ [(Z, L)], Imp [] e.1 e.2 := fun e he => by
  simp only [List.mem_singleton] at he; subst he; exact h
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
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 5 && x 7)
def EF : ℕ := ((((((((((((rawP.getD 0 0 &&& rawP.getD 3 0) ||| (rawP.getD 1 0 &&& rawP.getD 4 0)) ||| (rawP.getD 0 0 &&& rawP.getD 5 0)) ||| (rawP.getD 1 0 &&& rawP.getD 5 0)) ||| (rawP.getD 2 0 &&& rawP.getD 5 0)) ||| (rawP.getD 0 0 &&& rawP.getD 6 0)) ||| (rawP.getD 3 0 &&& rawP.getD 6 0)) ||| (rawP.getD 4 0 &&& rawP.getD 6 0)) ||| (rawP.getD 0 0 &&& rawP.getD 7 0)) ||| (rawP.getD 1 0 &&& rawP.getD 7 0)) ||| (rawP.getD 3 0 &&& rawP.getD 7 0)) ||| (rawP.getD 5 0 &&& rawP.getD 7 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
inductive Steps (m T : ℕ) : ℕ → ℕ → Set ℕ → Prop
  | done {S} : T ∈ S → Steps m T 0 0 S
  | un {q u S a} : a ∈ S → Steps m T q u (insert (a ^^^ m) S) → Steps m T (q+1) (u+1) S
  | bi {q u S d a b} : a ∈ S → b ∈ S → Steps m T q u (insert (op d a b) S) → Steps m T (q+1) u S

lemma Steps.widen {m T q u S} (h : Steps m T q u S) :
    ∀ {S'}, S ⊆ S' → Steps m T q u S' := by
  induction h with
  | done h => intro _ hs; exact .done (hs h)
  | un ha _ ih => intro _ hs; exact .un (hs ha) (ih (Set.insert_subset_insert hs))
  | bi ha hb _ ih => intro _ hs; exact .bi (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

lemma Steps.liveCount {m T q u S} (h : Steps m T q u S) :
    ∃ k t, ∃ S0 : Finset ℕ, k ≤ q ∧ t ≤ u ∧ u + k ≤ q + t ∧
      (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  induction h with
  | @done S h => exact ⟨0, 0, {T}, le_rfl, le_rfl, le_rfl, by simpa using h, .stop⟩
  | @un q u S a ha _ ih =>
    obtain ⟨k,t,S1,hk,ht,hc,hs,hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k+1, t+1, insert a (S1.erase (a ^^^ m)), by omega, by omega, by omega, ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1,h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩
  | @bi q u S d a b ha hb _ ih =>
    obtain ⟨k,t,S1,hk,ht,hc,hs,hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).elim (fun e => e ▸ ha) id,hl⟩
      refine ⟨k+1,t,insert a (insert b (S1.erase (op d a b))),by omega,by omega,by omega,?_,.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩

section countProjection
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.stepIm {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S')
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) (q+1) (u+1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.widen (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.stepIm {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S')
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) (q+1) u (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.widen (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.stepKill {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a)
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) q u (C n (Im n S)) :=
  hs.widen (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.stepKill {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) q u (C n (Im n S)) :=
  hs.widen (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)

lemma Min.projectCount (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q u, u ≤ t ∧ q + (S.filter (Cst n)).card + t ≤ k + u ∧ Steps n (T &&& n) q u (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, 0, le_rfl, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q,u,hu',hq,hs⟩ := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q,u,by omega,?_,hu.stepKill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left ((Cst_neg hn).2 hc), Finset.card_insert_of_notMem (by simp [hf])] at hq
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q+1,u+1,by omega,?_,hu.stepIm hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q,u,hu',hq,hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q,u,hu',?_,hu.stepKill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q,u,hu',?_,hu.stepKill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q+1,u,hu',?_,hu.stepIm hs⟩
        rw [ite_eq_right hcb]; omega
end countProjection
lemma minimumInputLive {Z q : ℕ}
    (h0 : tz Z ≠ 0) (h1 : tz Z ≠ mz Z)
    (hs : Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ [] Z))) :
    ∃ k ≤ q, ∃ t, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] Z ∧
      Live Z0 (mz Z) (tz Z) k t S ∧
      ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) := by
  classical
  have hex : ∃ j, Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) := ⟨q,hs⟩
  obtain ⟨k,hk,t,S,hS,hl⟩ := (Nat.find_spec hex).live
  have heq := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have lower : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) :=
    fun j hj => Nat.find_min hex (by omega)
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl,fun j hj h => lower j hj (h.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w,_,rfl⟩ | h
    · rw [Nat.and_assoc,Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  obtain ⟨hz,ho⟩ := hm.proper hT h0 h1 hbd
  refine ⟨k, hk.trans (Nat.find_min' hex hs),t,S,?_,hl,lower⟩
  intro x hx
  rcases hS hx with h | h
  · exact h
  · simp at h; rcases h with rfl | rfl
    · exact absurd hx hz
    · exact absurd hx ho
namespace BinarySearch
noncomputable section core
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st z (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
def Cl (P : List ℕ) (T k t : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ j < P.length, ∀ q u, u ≤ t → q + b j + t < k + u →
    ¬ Steps (P.getD j 0) (T &&& P.getD j 0) q u (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k t z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k t b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k t b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q,u,hu,hq,hs⟩ := hm.projectCount p1 p2 p3
  have hqb : ¬ q + b j + t < k + u := fun h => hc j hj q u hu h hs
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
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k t z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k t z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have hcl' : Cl P T k t b' S' := by
    intro j hj q u hu hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q u hu ?_ (hb.stepKill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q+1) u hu ?_ (hb.stepIm hsol)
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
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k t z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
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
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
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
lemma hit_ht {k t z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k t z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
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
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
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
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
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
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k t z v S) (hl : Live R m T k' t S)
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
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
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
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
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
      r.length = S'.card ∧ StOk P T l k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) (t + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k t (z - (bif ka then a.c else 0)) r S' := by
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
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := b
  have hcl' : Cl P T k t b' S' := by
    intro j hj q u hu hq hsol
    by_cases hkill : a.c.testBit (5*j) = true
    · exact hcl j hj q u (by omega) (by dsimp [b'] at hq; omega)
        (hb.stepKill (X.hP j hj).1 (wa.cst hj hkill) hsol)
    · exact hcl j hj (q+1) (u+1) (by omega) (by dsimp [b'] at hq; omega)
        (hb.stepIm (X.hP j hj).1 hsol)
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    rw [pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st z (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) (t + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
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
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c) <;> simp
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
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) z = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) z <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_32632.X → L_meta_32632.X → Bool) → List L_meta_32632.X → Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k t z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
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
        have : a.s = c.s := congrArg L_meta_32632.X.s e
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
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k t z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_32632.X → L_meta_32632.X → Bool) → List L_meta_32632.X → Bool,
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
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32632.X.s e))
end sound
noncomputable section
end
noncomputable section
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
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
    have : Std.Symm (fun a b : L_meta_32632.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32632.X.s e)) hpb
end sound
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - t - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma rejectMinimum {Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hp : pOk Z Q = true) (hL : L ≤ 15) (hk : k < L)
    (hI : ∀ e ∈ Q, ∀ q u, u ≤ t → q < e.2 + u → ¬ Steps (mz e.1) (tz e.1) q u (C (mz e.1) (WZ [] e.1))) (hSW : (S : Set ℕ) ⊆ WZ [] Z)
    (hl : Live Z0 (mz Z) (tz Z) k t S)
    (lower : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)))
    (M : List (ℕ × ℕ)) (hMf : mFull M = true)
    (hchk : ∀ p ∈ M, chk [] Q Z (L-1) t p.1 p.2 = false) : False := by
  classical
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0,hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  have hE6 : ∀ e ∈ ([] : List (ℕ × ℕ)), e ∈ six := by simp
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl,fun j hj hs => lower j hj (hs.mono le_rfl (C_mono hSW))⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := hSW hx
    rw [Nat.and_assoc,Nat.and_self]
  obtain ⟨h0,h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q u, u ≤ t → q < e.2 + u →
      ¬ Steps (mz e.1) (tz Z &&& mz e.1) q u (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q u hu hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q u hu hq (hs.widen (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
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
  have hcl : Cl (PZ Q) (tz Z) (L - 1) t (fun j => L - 1 - t - (Q.getD j (0, L - 1 - t)).2) S := by
    intro j hj q u hu hq
    obtain ⟨e1,e2⟩ := hPget j hj
    have memj : j < Q.length := by simpa [PZ] using hj
    have eqj : Q.getD j (0,L-1-t) = Q.getD j (0,L-1) := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem memj]
    change q + (L-1-t-(Q.getD j (0,L-1-t)).2) + t < L-1+u at hq
    rw [eqj] at hq
    rw [e1]
    exact hno _ e2 q u hu (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - t - e.2)) - sumc v) v S := by
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
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - t - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R [] Z) (RZ_R2 [] Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine lower q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

end BinarySearch
lemma Steps.signCount {m T q u S} (h : Steps m T q u S) : u ≤ q := by
  induction h <;> omega

def gradedRow (t : ℕ) (e : ℕ × ℕ) : ℕ × ℕ := (e.1,e.2+1-t)
def HasGrade (t : ℕ) (g : ℕ × ℕ) : Prop :=
  ∀ q u, u ≤ t → q < g.2 + u → ¬ Steps (mz g.1) (tz g.1) q u (C (mz g.1) (WZ [] g.1))

lemma gradeFromFloor {z h t : ℕ} (floor : Imp [] z h) (h0 : tz z ≠ 0) (h1 : tz z ≠ mz z)
    (no : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] z → Live Z0 (mz z) (tz z) h t S → False) :
    HasGrade t (gradedRow t (z,h)) := by
  intro q u hu hq steps
  change q < h+1-t+u at hq
  change Steps (mz z) (tz z) q u (C (mz z) (WZ [] z)) at steps
  have huq := steps.signCount
  by_cases cap : t ≤ h+1
  · obtain ⟨k,v,S,hk,hv,count,hS,hl⟩ := steps.liveCount
    have hlow : h ≤ k := by
      by_contra short
      exact floor k (by omega) (hl.sol.mono le_rfl hS)
    have ek : k = h := by omega
    have ev : v = t := by omega
    subst k v
    have hm : Min Z0 (mz z) (tz z) h t S := by
      refine ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl ?_)⟩
      rintro x (hx | hx)
      · exact hS hx
      · exact Or.inr hx
    have hbd : ∀ x ∈ S, x &&& mz z = x := by
      intro x hx
      rcases hS hx with ⟨w,_,rfl⟩ | c
      · rw [Nat.and_assoc,Nat.and_self]
      · simp at c; rcases c with rfl | rfl <;> simp
    obtain ⟨ha,hb⟩ := hm.proper (by simp only [tz,nl,Nat.and_assoc,Nat.and_self]) h0 h1 hbd
    apply no S _ hl
    intro x hx
    rcases hS hx with h | c
    · exact h
    · simp at c; rcases c with rfl | rfl
      · exact absurd hx ha
      · exact absurd hx hb
  · omega

noncomputable def gradeTest (t : ℕ) (before : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  let Q := pr (before.map (gradedRow t)) e.1
  pOk e.1 Q && (e.2+1 ≤ 15) &&
    (e.2 < t || !BinarySearch.chk [] Q e.1 e.2 t FF 1)

lemma checkedGrade {t : ℕ} {before : List (ℕ × ℕ)} {e : ℕ × ℕ}
    (floor : Imp [] e.1 e.2)
    (prior : ∀ x ∈ before, HasGrade t (gradedRow t x))
    (tested : gradeTest t before e = true) : HasGrade t (gradedRow t e) := by
  rcases e with ⟨z,h⟩
  let Q := pr (before.map (gradedRow t)) z
  change pOk z Q && decide (h+1 ≤ 15) && (decide (h < t) || !BinarySearch.chk [] Q z h t FF 1) = true at tested
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true'] at tested
  obtain ⟨⟨hp,hlim⟩,branch⟩ := tested
  have pn := hp
  simp only [pOk,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at pn
  obtain ⟨⟨p0,p1⟩,_⟩ := pn
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e,Nat.beq_refl] at h; simp at h
  apply gradeFromFloor floor (nb p0) (nb p1)
  intro S sw hl
  have hm : Min Z0 (mz z) (tz z) h t S :=
    ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl (C_mono sw))⟩
  rcases branch with lt | chk
  · have := hm.size.2; omega
  · refine BinarySearch.rejectMinimum (Q := Q) (L := h+1) hp hlim (by omega) ?_ sw hl floor [(FF,1)] ffull ?_
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hx)
      exact prior y hy
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      simpa using chk

lemma addGrades {t : ℕ} {before group : List (ℕ × ℕ)}
    (lower : ∀ e ∈ group, Imp [] e.1 e.2)
    (prior : ∀ e ∈ before, HasGrade t (gradedRow t e))
    (checks : group.all (gradeTest t before) = true) :
    ∀ e ∈ group, HasGrade t (gradedRow t e) :=
  fun e he => checkedGrade (lower e he) prior (List.all_eq_true.1 checks e he)

lemma joinGrades {t : ℕ} {a b : List (ℕ × ℕ)}
    (h1 : ∀ e ∈ a, HasGrade t (gradedRow t e))
    (h2 : ∀ e ∈ b, HasGrade t (gradedRow t e)) :
    ∀ e ∈ a ++ b, HasGrade t (gradedRow t e) :=
  fun e he => (List.mem_append.1 he).elim (h1 e) (h2 e)

lemma gradeWeak {z h t : ℕ} (floor : Imp [] z h) : HasGrade t (z,h-t) := by
  intro q u hu hq st
  change Steps (mz z) (tz z) q u (C (mz z) (WZ [] z)) at st
  change q < h-t+u at hq
  have huq := st.signCount
  obtain ⟨k,v,S,hk,_,_,hS,hl⟩ := st.liveCount
  exact floor k (by omega) (hl.sol.mono le_rfl hS)
open PEqualNP.CircuitLowerBounds
def cert0 : List (ℕ × ℕ) := []
lemma good0 : ∀ e ∈ cert0, Imp [] e.1 e.2 := by simp [cert0]
lemma grades0 : ∀ e ∈ cert0, HasGrade 1 (gradedRow 1 e) := by simp [cert0]
def g6p0 : List (ℕ × ℕ) := [(95,1), (119,1), (125,1), (126,1), (175,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6p0Check : g6p0.all (fun e => okE [] (pr cert0 e.1) e) = true := by decide +kernel
lemma g6p0Good : ∀ e ∈ g6p0, Imp [] e.1 e.2 := okAll g6p0Check good0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6p0CheckedGrade : g6p0.all (gradeTest 1 cert0) = true := by decide +kernel
lemma g6p0Gr : ∀ e ∈ g6p0, HasGrade 1 (gradedRow 1 e) := addGrades g6p0Good grades0 g6p0CheckedGrade
def g6p1 : List (ℕ × ℕ) := [(183,1), (190,1), (221,1), (222,1), (237,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6p1Check : g6p1.all (fun e => okE [] (pr cert0 e.1) e) = true := by decide +kernel
lemma g6p1Good : ∀ e ∈ g6p1, Imp [] e.1 e.2 := okAll g6p1Check good0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6p1CheckedGrade : g6p1.all (gradeTest 1 cert0) = true := by decide +kernel
lemma g6p1Gr : ∀ e ∈ g6p1, HasGrade 1 (gradedRow 1 e) := addGrades g6p1Good grades0 g6p1CheckedGrade
def g6p2 : List (ℕ × ℕ) := [(246,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6p2Check : g6p2.all (fun e => okE [] (pr cert0 e.1) e) = true := by decide +kernel
lemma g6p2Good : ∀ e ∈ g6p2, Imp [] e.1 e.2 := okAll g6p2Check good0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6p2CheckedGrade : g6p2.all (gradeTest 1 cert0) = true := by decide +kernel
lemma g6p2Gr : ∀ e ∈ g6p2, HasGrade 1 (gradedRow 1 e) := addGrades g6p2Good grades0 g6p2CheckedGrade
def cert1 : List (ℕ × ℕ) := (g6p0 ++ (g6p1 ++ g6p2)) ++ cert0
lemma good1 : ∀ e ∈ cert1, Imp [] e.1 e.2 := apI (apI g6p0Good (apI g6p1Good g6p2Good)) good0
lemma grades1 : ∀ e ∈ cert1, HasGrade 1 (gradedRow 1 e) := joinGrades (joinGrades g6p0Gr (joinGrades g6p1Gr g6p2Gr)) grades0
def g5p0 : List (ℕ × ℕ) := [(31,1), (47,1), (55,2), (61,1), (62,2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p0Check : g5p0.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p0Good : ∀ e ∈ g5p0, Imp [] e.1 e.2 := okAll g5p0Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p0CheckedGrade : g5p0.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p0Gr : ∀ e ∈ g5p0, HasGrade 1 (gradedRow 1 e) := addGrades g5p0Good grades1 g5p0CheckedGrade
def g5p1 : List (ℕ × ℕ) := [(79,1), (87,2), (93,4), (94,4), (103,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p1Check : g5p1.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p1Good : ∀ e ∈ g5p1, Imp [] e.1 e.2 := okAll g5p1Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p1CheckedGrade : g5p1.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p1Gr : ∀ e ∈ g5p1, HasGrade 1 (gradedRow 1 e) := addGrades g5p1Good grades1 g5p1CheckedGrade
def g5p2 : List (ℕ × ℕ) := [(109,2), (110,1), (117,2), (118,4), (124,2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p2Check : g5p2.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p2Good : ∀ e ∈ g5p2, Imp [] e.1 e.2 := okAll g5p2Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p2CheckedGrade : g5p2.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p2Gr : ∀ e ∈ g5p2, HasGrade 1 (gradedRow 1 e) := addGrades g5p2Good grades1 g5p2CheckedGrade
def g5p3 : List (ℕ × ℕ) := [(143,1), (151,1), (157,1), (158,2), (167,2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p3Check : g5p3.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p3Good : ∀ e ∈ g5p3, Imp [] e.1 e.2 := okAll g5p3Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p3CheckedGrade : g5p3.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p3Gr : ∀ e ∈ g5p3, HasGrade 1 (gradedRow 1 e) := addGrades g5p3Good grades1 g5p3CheckedGrade
def g5p4 : List (ℕ × ℕ) := [(173,2), (174,2), (181,1), (182,4), (188,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p4Check : g5p4.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p4Good : ∀ e ∈ g5p4, Imp [] e.1 e.2 := okAll g5p4Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p4CheckedGrade : g5p4.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p4Gr : ∀ e ∈ g5p4, HasGrade 1 (gradedRow 1 e) := addGrades g5p4Good grades1 g5p4CheckedGrade
def g5p5 : List (ℕ × ℕ) := [(205,2), (206,1), (213,1), (214,2), (220,2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p5Check : g5p5.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p5Good : ∀ e ∈ g5p5, Imp [] e.1 e.2 := okAll g5p5Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p5CheckedGrade : g5p5.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p5Gr : ∀ e ∈ g5p5, HasGrade 1 (gradedRow 1 e) := addGrades g5p5Good grades1 g5p5CheckedGrade
def g5p6 : List (ℕ × ℕ) := [(229,1), (230,1), (236,1), (244,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p6Check : g5p6.all (fun e => okE [] (pr cert1 e.1) e) = true := by decide +kernel
lemma g5p6Good : ∀ e ∈ g5p6, Imp [] e.1 e.2 := okAll g5p6Check good1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5p6CheckedGrade : g5p6.all (gradeTest 1 cert1) = true := by decide +kernel
lemma g5p6Gr : ∀ e ∈ g5p6, HasGrade 1 (gradedRow 1 e) := addGrades g5p6Good grades1 g5p6CheckedGrade
def cert2 : List (ℕ × ℕ) := ((g5p0 ++ (g5p1 ++ g5p2)) ++ ((g5p3 ++ g5p4) ++ (g5p5 ++ g5p6))) ++ cert1
lemma good2 : ∀ e ∈ cert2, Imp [] e.1 e.2 := apI (apI (apI g5p0Good (apI g5p1Good g5p2Good)) (apI (apI g5p3Good g5p4Good) (apI g5p5Good g5p6Good))) good1
lemma grades2 : ∀ e ∈ cert2, HasGrade 1 (gradedRow 1 e) := joinGrades (joinGrades (joinGrades g5p0Gr (joinGrades g5p1Gr g5p2Gr)) (joinGrades (joinGrades g5p3Gr g5p4Gr) (joinGrades g5p5Gr g5p6Gr))) grades1
def g4p0 : List (ℕ × ℕ) := [(15,3), (23,4), (29,4), (30,5), (39,4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p0Check : g4p0.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p0Good : ∀ e ∈ g4p0, Imp [] e.1 e.2 := okAll g4p0Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p0CheckedGrade : g4p0.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p0Gr : ∀ e ∈ g4p0, HasGrade 1 (gradedRow 1 e) := addGrades g4p0Good grades2 g4p0CheckedGrade
def g4p1 : List (ℕ × ℕ) := [(45,4), (46,4), (53,4), (54,5), (60,4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p1Check : g4p1.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p1Good : ∀ e ∈ g4p1, Imp [] e.1 e.2 := okAll g4p1Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p1CheckedGrade : g4p1.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p1Gr : ∀ e ∈ g4p1, HasGrade 1 (gradedRow 1 e) := addGrades g4p1Good grades2 g4p1CheckedGrade
def g4p2 : List (ℕ × ℕ) := [(71,2), (77,5), (78,4), (85,5), (86,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p2Check : g4p2.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p2Good : ∀ e ∈ g4p2, Imp [] e.1 e.2 := okAll g4p2Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p2CheckedGrade : g4p2.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p2Gr : ∀ e ∈ g4p2, HasGrade 1 (gradedRow 1 e) := addGrades g4p2Good grades2 g4p2CheckedGrade
def g4p3 : List (ℕ × ℕ) := [(92,5), (101,4), (102,4), (108,4), (116,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p3Check : g4p3.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p3Good : ∀ e ∈ g4p3, Imp [] e.1 e.2 := okAll g4p3Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p3CheckedGrade : g4p3.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p3Gr : ∀ e ∈ g4p3, HasGrade 1 (gradedRow 1 e) := addGrades g4p3Good grades2 g4p3CheckedGrade
def g4p4 : List (ℕ × ℕ) := [(135,2), (141,4), (142,4), (149,3), (150,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p4Check : g4p4.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p4Good : ∀ e ∈ g4p4, Imp [] e.1 e.2 := okAll g4p4Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p4CheckedGrade : g4p4.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p4Gr : ∀ e ∈ g4p4, HasGrade 1 (gradedRow 1 e) := addGrades g4p4Good grades2 g4p4CheckedGrade
def g4p5 : List (ℕ × ℕ) := [(156,4), (165,4), (166,5), (172,4), (180,4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p5Check : g4p5.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p5Good : ∀ e ∈ g4p5, Imp [] e.1 e.2 := okAll g4p5Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p5CheckedGrade : g4p5.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p5Gr : ∀ e ∈ g4p5, HasGrade 1 (gradedRow 1 e) := addGrades g4p5Good grades2 g4p5CheckedGrade
def g4p6 : List (ℕ × ℕ) := [(197,2), (198,2), (204,4), (212,4), (228,3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p6Check : g4p6.all (fun e => okE [] (pr cert2 e.1) e) = true := by decide +kernel
lemma g4p6Good : ∀ e ∈ g4p6, Imp [] e.1 e.2 := okAll g4p6Check good2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4p6CheckedGrade : g4p6.all (gradeTest 1 cert2) = true := by decide +kernel
lemma g4p6Gr : ∀ e ∈ g4p6, HasGrade 1 (gradedRow 1 e) := addGrades g4p6Good grades2 g4p6CheckedGrade
def cert3 : List (ℕ × ℕ) := ((g4p0 ++ (g4p1 ++ g4p2)) ++ ((g4p3 ++ g4p4) ++ (g4p5 ++ g4p6))) ++ cert2
lemma good3 : ∀ e ∈ cert3, Imp [] e.1 e.2 := apI (apI (apI g4p0Good (apI g4p1Good g4p2Good)) (apI (apI g4p3Good g4p4Good) (apI g4p5Good g4p6Good))) good2
lemma grades3 : ∀ e ∈ cert3, HasGrade 1 (gradedRow 1 e) := joinGrades (joinGrades (joinGrades g4p0Gr (joinGrades g4p1Gr g4p2Gr)) (joinGrades (joinGrades g4p3Gr g4p4Gr) (joinGrades g4p5Gr g4p6Gr))) grades2
def g3p0 : List (ℕ × ℕ) := [(7,5), (13,7), (14,7), (21,7), (22,7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p0Check : g3p0.all (fun e => okE [] (pr cert3 e.1) e) = true := by decide +kernel
lemma g3p0Good : ∀ e ∈ g3p0, Imp [] e.1 e.2 := okAll g3p0Check good3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p0CheckedGrade : g3p0.all (gradeTest 1 cert3) = true := by decide +kernel
lemma g3p0Gr : ∀ e ∈ g3p0, HasGrade 1 (gradedRow 1 e) := addGrades g3p0Good grades3 g3p0CheckedGrade
def g3p1 : List (ℕ × ℕ) := [(28,7), (37,7), (38,7), (44,7), (52,7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p1Check : g3p1.all (fun e => okE [] (pr cert3 e.1) e) = true := by decide +kernel
lemma g3p1Good : ∀ e ∈ g3p1, Imp [] e.1 e.2 := okAll g3p1Check good3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p1CheckedGrade : g3p1.all (gradeTest 1 cert3) = true := by decide +kernel
lemma g3p1Gr : ∀ e ∈ g3p1, HasGrade 1 (gradedRow 1 e) := addGrades g3p1Good grades3 g3p1CheckedGrade
def g3p2 : List (ℕ × ℕ) := [(69,6), (70,5), (76,7), (84,7), (100,7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p2Check : g3p2.all (fun e => okE [] (pr cert3 e.1) e) = true := by decide +kernel
lemma g3p2Good : ∀ e ∈ g3p2, Imp [] e.1 e.2 := okAll g3p2Check good3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p2CheckedGrade : g3p2.all (gradeTest 1 cert3) = true := by decide +kernel
lemma g3p2Gr : ∀ e ∈ g3p2, HasGrade 1 (gradedRow 1 e) := addGrades g3p2Good grades3 g3p2CheckedGrade
def g3p3 : List (ℕ × ℕ) := [(133,5), (134,6), (140,7), (148,7), (164,7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p3Check : g3p3.all (fun e => okE [] (pr cert3 e.1) e) = true := by decide +kernel
lemma g3p3Good : ∀ e ∈ g3p3, Imp [] e.1 e.2 := okAll g3p3Check good3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p3CheckedGrade : g3p3.all (gradeTest 1 cert3) = true := by decide +kernel
lemma g3p3Gr : ∀ e ∈ g3p3, HasGrade 1 (gradedRow 1 e) := addGrades g3p3Good grades3 g3p3CheckedGrade
def g3p4 : List (ℕ × ℕ) := [(196,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p4Check : g3p4.all (fun e => okE [] (pr cert3 e.1) e) = true := by decide +kernel
lemma g3p4Good : ∀ e ∈ g3p4, Imp [] e.1 e.2 := okAll g3p4Check good3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3p4CheckedGrade : g3p4.all (gradeTest 1 cert3) = true := by decide +kernel
lemma g3p4Gr : ∀ e ∈ g3p4, HasGrade 1 (gradedRow 1 e) := addGrades g3p4Good grades3 g3p4CheckedGrade
def cert4 : List (ℕ × ℕ) := ((g3p0 ++ g3p1) ++ (g3p2 ++ (g3p3 ++ g3p4))) ++ cert3
lemma good4 : ∀ e ∈ cert4, Imp [] e.1 e.2 := apI (apI (apI g3p0Good g3p1Good) (apI g3p2Good (apI g3p3Good g3p4Good))) good3
lemma grades4 : ∀ e ∈ cert4, HasGrade 1 (gradedRow 1 e) := joinGrades (joinGrades (joinGrades g3p0Gr g3p1Gr) (joinGrades g3p2Gr (joinGrades g3p3Gr g3p4Gr))) grades3
def g2p0 : List (ℕ × ℕ) := [(5,9), (6,9), (12,10), (20,10), (36,10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g2p0Check : g2p0.all (fun e => okE [] (pr cert4 e.1) e) = true := by decide +kernel
lemma g2p0Good : ∀ e ∈ g2p0, Imp [] e.1 e.2 := okAll g2p0Check good4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g2p0CheckedGrade : g2p0.all (gradeTest 1 cert4) = true := by decide +kernel
lemma g2p0Gr : ∀ e ∈ g2p0, HasGrade 1 (gradedRow 1 e) := addGrades g2p0Good grades4 g2p0CheckedGrade
def g2p1 : List (ℕ × ℕ) := [(68,9), (132,9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g2p1Check : g2p1.all (fun e => okE [] (pr cert4 e.1) e) = true := by decide +kernel
lemma g2p1Good : ∀ e ∈ g2p1, Imp [] e.1 e.2 := okAll g2p1Check good4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g2p1CheckedGrade : g2p1.all (gradeTest 1 cert4) = true := by decide +kernel
lemma g2p1Gr : ∀ e ∈ g2p1, HasGrade 1 (gradedRow 1 e) := addGrades g2p1Good grades4 g2p1CheckedGrade
def cert5 : List (ℕ × ℕ) := (g2p0 ++ g2p1) ++ cert4
lemma good5 : ∀ e ∈ cert5, Imp [] e.1 e.2 := apI (apI g2p0Good g2p1Good) good4
lemma grades5 : ∀ e ∈ cert5, HasGrade 1 (gradedRow 1 e) := joinGrades (joinGrades g2p0Gr g2p1Gr) grades4
def activeBounds : List (ℕ × ℕ) := cert5.map (gradedRow 1)
lemma boundsHold (e) (h : e ∈ activeBounds) : HasGrade 1 e := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
  exact grades5 x hx
def smallTotal (h ph : ℕ) : List (ℕ × ℕ × ℕ) := (List.range 5).map (fun t => (t,h,ph))
def floorPart0 := smallTotal 0x4000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart0Ok : floorPart0.all (okS cert5 4 12) = true := by decide +kernel
def floorPart1 := smallTotal 0x20000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart1Ok : floorPart1.all (okS cert5 4 12) = true := by decide +kernel
def floorPart2 := smallTotal 0x200000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart2Ok : floorPart2.all (okS cert5 4 12) = true := by decide +kernel
def floorPart3 := smallTotal 0x8000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart3Ok : floorPart3.all (okS cert5 4 12) = true := by decide +kernel
def floorPart4 := smallTotal 0x40000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart4Ok : floorPart4.all (okS cert5 4 12) = true := by decide +kernel
def floorPart5 := smallTotal 0x80000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart5Ok : floorPart5.all (okS cert5 4 12) = true := by decide +kernel
def floorPart6 := smallTotal 0x400000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart6Ok : floorPart6.all (okS cert5 4 12) = true := by decide +kernel
def floorPart7 := smallTotal 0x100000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart7Ok : floorPart7.all (okS cert5 4 12) = true := by decide +kernel
def floorPart8 := smallTotal 0x400000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart8Ok : floorPart8.all (okS cert5 4 12) = true := by decide +kernel
def floorPart9 := smallTotal 0x10000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart9Ok : floorPart9.all (okS cert5 4 12) = true := by decide +kernel
def floorPart10 := smallTotal 0x80000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart10Ok : floorPart10.all (okS cert5 4 12) = true := by decide +kernel
def floorPart11 := smallTotal 0x40000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart11Ok : floorPart11.all (okS cert5 4 12) = true := by decide +kernel
def floorPart12 := smallTotal 0x100000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart12Ok : floorPart12.all (okS cert5 4 12) = true := by decide +kernel
def floorPart13 := smallTotal 0x200000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart13Ok : floorPart13.all (okS cert5 4 12) = true := by decide +kernel
def floorPart14 := smallTotal 0x800000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart14Ok : floorPart14.all (okS cert5 4 12) = true := by decide +kernel
def floorPart15 := smallTotal 0x2000000000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart15Ok : floorPart15.all (okS cert5 4 12) = true := by decide +kernel
def floorPart16 := smallTotal 0x8000000000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart16Ok : floorPart16.all (okS cert5 4 12) = true := by decide +kernel
def floorPart17 := smallTotal 0x400000000000000000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart17Ok : floorPart17.all (okS cert5 4 12) = true := by decide +kernel
def floorPart18 := smallTotal 0x1000000000000000000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart18Ok : floorPart18.all (okS cert5 4 12) = true := by decide +kernel
def floorPart19 := smallTotal 0x4000000000000000000000000000000000000000000000000000 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart19Ok : floorPart19.all (okS cert5 4 12) = true := by decide +kernel
def floorPart20 := smallTotal 0x3fbffebfffffff5fff4bff6ffffaffb3fff7fffdfffdbfffffffff 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorPart20Ok : floorPart20.all (okS cert5 4 12) = true := by decide +kernel
def floorLater : List (ℕ × ℕ × ℕ) := (List.range' 5 8).map (fun t => (t,FF,1))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem floorLaterOk : floorLater.all (okS cert5 4 12) = true := by decide +kernel
def fullFloorParts := ((((floorPart0 ++ floorPart1) ++ (floorPart2 ++ (floorPart3 ++ floorPart4))) ++ ((floorPart5 ++ (floorPart6 ++ floorPart7)) ++ (floorPart8 ++ (floorPart9 ++ floorPart10)))) ++ (((floorPart11 ++ floorPart12) ++ (floorPart13 ++ (floorPart14 ++ floorPart15))) ++ ((floorPart16 ++ (floorPart17 ++ floorPart18)) ++ (floorPart19 ++ (floorPart20 ++ floorLater)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma faceFloor : Imp [] 4 13 := imp_run fullFloorParts good5 (by decide +kernel) (appS (appS (appS (appS floorPart0Ok floorPart1Ok) (appS floorPart2Ok (appS floorPart3Ok floorPart4Ok))) (appS (appS floorPart5Ok (appS floorPart6Ok floorPart7Ok)) (appS floorPart8Ok (appS floorPart9Ok floorPart10Ok)))) (appS (appS (appS floorPart11Ok floorPart12Ok) (appS floorPart13Ok (appS floorPart14Ok floorPart15Ok))) (appS (appS floorPart16Ok (appS floorPart17Ok floorPart18Ok)) (appS floorPart19Ok (appS floorPart20Ok floorLaterOk)))))
end PEqualNP.Outside.L_meta_32632
namespace PEqualNP.Outside.L_meta_32632
namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isNegGate (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem negGate_iff (g : Gate) : isNegGate g = true ↔ g.op = .not := by
  cases g with | mk o l => cases o <;> simp [isNegGate]

theorem countNeg_le (gs : List Gate)
    (u : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP isNegGate ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun i j hi hj => Fin.ext (by
      have h := u i.succ j.succ hi hj
      exact Nat.succ.inj (congrArg Fin.val h)))
    by_cases neg : g.op = .not
    · have clear : gs.countP isNegGate = 0 := by
        apply List.countP_eq_zero.mpr
        intro k hk
        obtain ⟨i, rfl⟩ := List.get_of_mem hk
        have ne : (gs.get i).op ≠ .not := by
          intro h; have absurd := u 0 i.succ neg h
          have := congrArg Fin.val absurd
          simp at this
        cases h : isNegGate (gs.get i)
        · decide
        · exact (ne ((negGate_iff _).mp h)).elim
      simp [List.countP_cons,(negGate_iff g).mpr neg,clear]
    · simpa [List.countP_cons,negGate_iff,neg] using tail

theorem gateMonoOn (g : Gate) (h : g.op = .and ∨ g.op = .or)
    (a b : ℕ → Bool) (le : ∀ i ∈ g.inputs, a i ≤ b i) :
    g.op.eval (g.inputs.map a) ≤ g.op.eval (g.inputs.map b) := by
  rcases h with e | e
  · rw [e]; simp only [GateOp.eval,List.all_map,Function.comp_def]
    apply Bool.le_iff_imp.mpr
    intro ha
    simp_all only [List.all_eq_true,decide_eq_true_eq]
    intro i hi
    exact Bool.le_iff_imp.mp (le i hi) (ha i hi)
  · rw [e]; simp only [GateOp.eval,List.any_map,Function.comp_def]
    apply Bool.le_iff_imp.mpr
    intro ha
    simp_all only [List.any_eq_true,decide_eq_true_eq]
    obtain ⟨i,hi,ha⟩ := ha
    exact ⟨i,hi,Bool.le_iff_imp.mp (le i hi) ha⟩

theorem wiresAnti (gs : List Gate) (p : ℕ) (legal : ∀ g ∈ gs, Ok g)
    (no : ∀ g ∈ gs, g.op ≠ GateOp.not → p ∉ g.inputs)
    (unique : gs.countP isNegGate ≤ 1) :
    ∀ (A B : List Bool), A.length = B.length → p < A.length →
      A.getD p false = true → B.getD p false = false →
      (∀ i ≠ p, A.getD i false ≤ B.getD i false) →
      ((∃ g ∈ gs, g.op = GateOp.not) → ∀ i ≠ p, A.getD i false = B.getD i false) →
      ∀ i ≠ p, (wiresFrom gs A).getD i false ≤ (wiresFrom gs B).getD i false := by
  induction gs with
  | nil => intro A B _ _ _ _ le _; exact le
  | cons g gs ih =>
    intro A B lens plen ap bp le eq
    let newBit (W : List Bool) := g.op.eval (g.inputs.map fun i => W.getD i false)
    have child (h : ∃ k ∈ gs, k.op = GateOp.not) : g.op ≠ GateOp.not := by
      obtain ⟨k,hk,e⟩ := h
      have pos : 0 < gs.countP isNegGate := List.countP_pos_iff.mpr ⟨k,hk,(negGate_iff k).mpr e⟩
      intro bad
      simp only [List.countP_cons,(negGate_iff g).mpr bad,if_true] at unique
      omega
    have bit : newBit A ≤ newBit B := by
      by_cases neg : g.op = GateOp.not
      · have he := eq ⟨g,List.mem_cons_self,neg⟩
        unfold newBit
        rw [neg]
        cases hs : g.inputs with
        | nil => simp [GateOp.eval]
        | cons i ins =>
          change (!A.getD i false) ≤ !B.getD i false
          by_cases hn : i = p
          · rw [hn,ap,bp]; decide
          · rw [he i hn]
      · have hg := (legal g List.mem_cons_self).1
        have ops : g.op = .and ∨ g.op = .or := by
          rcases hg with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (neg h).elim
        exact gateMonoOn g ops _ _ (fun i hi => le i (fun e => no g List.mem_cons_self neg (e ▸ hi)))
    have ut : gs.countP isNegGate ≤ 1 := by
      rw [List.countP_cons] at unique
      split at unique <;> omega
    apply ih (fun k hk => legal k (List.mem_cons_of_mem _ hk))
      (fun k hk => no k (List.mem_cons_of_mem _ hk)) ut
      (A ++ [newBit A]) (B ++ [newBit B]) (by simp [lens]) (by simp;omega)
      (by rw [List.getD_append _ _ _ _ plen];exact ap)
      (by rw [List.getD_append _ _ _ _ (lens ▸ plen)];exact bp)
    · intro i nei
      by_cases h : i = A.length
      · rw [h,getD_snoc_eq,lens,getD_snoc_eq];exact bit
      · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)];exact le i nei
    · intro ex i nei
      have he := eq (by obtain ⟨k,hk,hn⟩ := ex;exact ⟨k,List.mem_cons_of_mem _ hk,hn⟩)
      by_cases h : i = A.length
      · rw [h,getD_snoc_eq,lens,getD_snoc_eq]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        exact he j (fun e => no g List.mem_cons_self (child ex) (e ▸ hj))
      · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)];exact he i nei

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isBinaryGate (g : Gate) : Bool := !isNegGate g
abbrev binaryCount (gs : List Gate) := gs.countP isBinaryGate

theorem binary_of_ne {g : Gate} (ne : g.op ≠ .not) : isBinaryGate g = true := by
  cases h : isNegGate g
  · simp [isBinaryGate,h]
  · exact (ne ((negGate_iff _).mp h)).elim

theorem simp_binary_le (g : Gate) (m : ℕ) (ins : List Stat) :
    binaryCount (simplify g.op m ins).1.toList ≤ (if isBinaryGate g then 1 else 0) := by
  by_cases neg : g.op = .not
  · rw [show isBinaryGate g = false by simp [isBinaryGate,(negGate_iff g).mpr neg]]
    rw [neg]
    cases ins with
    | nil => simp [binaryCount,simplify,simpNot]
    | cons s t => cases s <;> simp [binaryCount,simplify,simpNot,isBinaryGate,isNegGate]
  · have flag := binary_of_ne neg
    rw [flag]
    exact le_trans List.countP_le_length (toList_length_le _)

theorem bin_step (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binaryCount (elimStep n acc g).2 ≤ binaryCount acc.2 + (if isBinaryGate g then 1 else 0) := by
  simp only [elimStep,binaryCount,List.countP_append]
  exact Nat.add_le_add_left (simp_binary_le _ _ _) _

theorem bin_all (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    binaryCount (elim n gs acc).2 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs generalizing acc with
  | nil => simp [elim,binaryCount]
  | cons g gs ih =>
    have a := ih (elimStep n acc g)
    have b := bin_step n acc g
    rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
    omega

theorem bin_save (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, g.op ≠ .not ∧ k ∈ g.inputs) →
    binaryCount (elim n gs acc).2 + 1 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs with
  | nil => intro acc _ _ _ h; simpa using h
  | cons g gs ih =>
    intro acc ok hk hc hex
    by_cases hit : g.op ≠ .not ∧ k ∈ g.inputs
    · obtain ⟨c,hc⟩ := hc
      have hg := ok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hg.1.1
        · simpa using hg.1.2
        · intro h; simpa using hg.2 h
        · exact ⟨c,List.mem_map.2 ⟨k,hit.2,hc⟩⟩
      have same : (elimStep n acc g).2 = acc.2 := by simp only [elimStep,hnone];simp
      have after := bin_all n gs (elimStep n acc g)
      rw [same] at after
      have flag := binary_of_ne hit.1
      rw [elim_cons];simp only [binaryCount,List.countP_cons,flag,if_true] at *
      omega
    · have rest : ∃ g ∈ gs, g.op ≠ .not ∧ k ∈ g.inputs := by
        obtain ⟨g',hmem,props⟩ := hex
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact (hit props).elim
        · exact ⟨_,hmem,props⟩
      have step := bin_step n acc g
      have after := ih (elimStep n acc g) (fun j hj => ok j (List.mem_cons_of_mem _ hj))
        (by simp [elimStep];omega)
        (by obtain ⟨c,hc⟩ := hc; refine ⟨c,?_⟩;simp only [elimStep];rw [getD_snoc_ne _ _ _ _ (by omega)];exact hc)
        rest
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem needsPositiveReader (n : ℕ) (C : Circuit) (legal : FanInTwo C)
    (unique : C.gates.countP isNegGate ≤ 1) (hout : C.output ≠ n)
    (y : Fin n → Bool)
    (up : C.eval (List.ofFn (Fin.snoc y true)) = true)
    (dn : C.eval (List.ofFn (Fin.snoc y false)) = false) :
    ∃ g ∈ C.gates, g.op ≠ .not ∧ n ∈ g.inputs := by
  by_contra no
  have bad : ∀ g ∈ C.gates, g.op ≠ .not → n ∉ g.inputs :=
    fun g hg a b => no ⟨g,hg,a,b⟩
  let W := List.ofFn y
  have len : W.length = n := by simp [W]
  have same (i : ℕ) (ne : i ≠ n) : (W ++ [true]).getD i false = (W ++ [false]).getD i false := by
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
  have h := wiresAnti C.gates n legal bad unique (W ++ [true]) (W ++ [false])
    (by simp) (by simp [len]) (getD_snoc_len _ _ _ _ len) (getD_snoc_len _ _ _ _ len)
    (fun i hi => le_of_eq (same i hi)) (fun _ => same) C.output hout
  rw [ofFn_snoc] at up dn
  change (wiresFrom C.gates (W ++ [true])).getD C.output false = true at up
  change (wiresFrom C.gates (W ++ [false])).getD C.output false = false at dn
  rw [up,dn] at h
  contradiction

theorem normBinary (gs : List Gate) : binaryCount (gs.map normGate) = binaryCount gs := by
  simp only [binaryCount,List.countP_map]
  have eq : isBinaryGate ∘ normGate = isBinaryGate := by
    funext g
    cases g with | mk op t => cases op <;> rfl
  rw [eq]

theorem saveBinaryLast (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (unique : C.gates.countP isNegGate ≤ 1)
    (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (inc : ∃ y : Fin n → Bool, f (Fin.snoc y true) = true ∧ f (Fin.snoc y false) = false)
    (nonconstant : ∃ y z : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false)) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y false)) ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates := by
  have hout : C.output ≠ n := by
    intro out
    have fixed (y : Fin n → Bool) : f (Fin.snoc y false) = false := by
      rw [← comp,ofFn_snoc]
      change (wiresFrom C.gates (List.ofFn y ++ [false])).getD C.output false = false
      rw [out,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨y,z,ne⟩ := nonconstant
    exact ne ((fixed _).trans (fixed _).symm)
  obtain ⟨y,yup,ydn⟩ := inc
  obtain ⟨g,mem,op,read⟩ := needsPositiveReader n C fit unique hout y
    ((comp _).trans yup) ((comp _).trans ydn)
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, NOk g := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact normGate_nok u (fit u hu)
  have same : normGate g = g := by
    cases g with | mk o t => cases o <;> simp_all [normGate]
  have read' : ∃ t ∈ gs, t.op ≠ .not ∧ n ∈ t.inputs :=
    ⟨g,same ▸ List.mem_map_of_mem mem,op,read⟩
  set acc := elim n gs (initStats n false,[]) with ha
  have val (z : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) = f (Fin.snoc z false) := by
    have h := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (hok k hk).1) (inv_init n false z)
    rw [((h.2 C.output).2 : statVal _ _ = _), ← ofFn_snoc,hgs,wiresFrom_norm,← comp]
    rfl
  cases status : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y,z,ne⟩ := nonconstant
    exfalso;apply ne;rw [← val y,← val z,status];rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),?_,?_⟩
    · intro z;have e := val z;rw [status] at e;exact e
    · have h := bin_save n n gs (initStats n false,[]) hok (by simp [initStats])
        ⟨false,getD_snoc_len _ _ _ _ (by simp)⟩ read'
      change binaryCount acc.2 + 1 ≤ binaryCount ([] : List Gate) + binaryCount gs at h
      have counts : binaryCount gs = binaryCount C.gates := normBinary _
      rw [counts] at h
      simpa only [binaryCount,List.countP_nil,Nat.zero_add] using h

theorem relabelBinary {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    binaryCount (relabel n m π C).gates = binaryCount C.gates := by
  simp only [binaryCount,relabel,List.countP_map]
  rfl

theorem binary_lt_length (gs : List Gate) (ex : ∃ g ∈ gs, g.op = .not) :
    binaryCount gs < gs.length := by
  obtain ⟨g,hg,neg⟩ := ex
  by_contra! h
  have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
  simp [isBinaryGate,(negGate_iff g).mpr neg] at eq

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem relabelFan {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (fit : FanInTwo C) :
    FanInTwo (relabel n m π C) := by
  intro g hg
  obtain ⟨h, mem, rfl⟩ := List.mem_map.mp hg
  exact ⟨(fit h mem).1, by simpa [relGate] using (fit h mem).2⟩

theorem relabelHasNot {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (ex : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ g ∈ (relabel n m π C).gates, g.op = GateOp.not := by
  obtain ⟨g, hg, hop⟩ := ex
  exact ⟨relGate n m π g, List.mem_map.mpr ⟨g,hg,rfl⟩, hop⟩

theorem relabelUniqueNot {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j) :
    let D := relabel n m π C
    ∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
      (D.gates.get j).op = GateOp.not → i = j := by
  dsimp only
  intro i j hi hj
  let a : Fin C.gates.length := ⟨i.val, by simpa [relabel] using i.isLt⟩
  let b : Fin C.gates.length := ⟨j.val, by simpa [relabel] using j.isLt⟩
  have pick (k : Fin (C.gates.map (relGate n m π)).length) :
      ((C.gates.map (relGate n m π)).get k).op =
      (C.gates.get ⟨k.val, by simpa using k.isLt⟩).op := by
    change ((C.gates.map (relGate n m π))[k.val]).op =
      (C.gates[k.val]'(by simpa using k.isLt)).op
    rw [List.getElem_map]
    rfl
  have ha : (C.gates.get a).op = GateOp.not := (pick i).symm.trans hi
  have hb : (C.gates.get b).op = GateOp.not := (pick j).symm.trans hj
  apply Fin.ext
  exact congrArg (fun k : Fin C.gates.length => k.val) (unique a b ha hb)

theorem relabelEval {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem liftBinaryLower (π : Fin 8 → Fin 8) (graph : (Fin 8 → Bool) → Bool)
    (base : (Fin 7 → Bool) → Bool) (b : ℕ)
    (inc : ∃ y : Fin 7 → Bool, graph ((Fin.snoc y true) ∘ π) = true ∧ graph ((Fin.snoc y false) ∘ π) = false)
    (nc : ∃ y z : Fin 7 → Bool, graph ((Fin.snoc y false) ∘ π) ≠ graph ((Fin.snoc z false) ∘ π))
    (table : ∀ y, graph ((Fin.snoc y false) ∘ π) = base y)
    (baseLower : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = base x) → b ≤ binaryCount D.gates)
    (C : Circuit) (fit : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (has : ∃ g ∈ C.gates, g.op = .not) (comp : ∀ x, C.eval (List.ofFn x) = graph x) :
    b + 2 ≤ C.gates.length := by
  let D := relabel 8 8 π C
  have cd (x : Fin 8 → Bool) : D.eval (List.ofFn x) = graph (x ∘ π) :=
    (relabelEval π C x).trans (comp _)
  have un := countNeg_le D.gates (relabelUniqueNot π C unique)
  obtain ⟨S,fitS,evS,saved⟩ := saveBinaryLast 7 (fun x => graph (x ∘ π)) D
    (relabelFan π C fit) un cd inc nc
  have l := baseLower S fitS (fun x => (evS x).trans (table x))
  have same : binaryCount D.gates = binaryCount C.gates := relabelBinary π C
  have lt := binary_lt_length _ has
  omega
end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem simplify_neg_sub (g : Gate) (m : ℕ) (ins : List Stat) :
    (simplify g.op m ins).1.toList.countP isNegGate ≤ (if isNegGate g then 1 else 0) := by
  cases g with
  | mk op inp =>
    cases op with
    | not => exact le_trans List.countP_le_length (toList_length_le _)
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simplify,simpAnd,isNegGate]
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simplify,simpOr,isNegGate]
    | _ => simp [simplify,isNegGate]

theorem elim_neg_sub (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).2.countP isNegGate ≤ acc.2.countP isNegGate + gs.countP isNegGate := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    have step : (elimStep n acc g).2.countP isNegGate ≤ acc.2.countP isNegGate + (if isNegGate g then 1 else 0) := by
      simp only [elimStep,List.countP_append]
      exact Nat.add_le_add_left (simplify_neg_sub _ _ _) _
    have tail := ih (elimStep n acc g)
    rw [elim_cons,List.countP_cons]
    omega

theorem normNeg (gs : List Gate) : (gs.map normGate).countP isNegGate = gs.countP isNegGate := by
  rw [List.countP_map]
  have e : isNegGate ∘ normGate = isNegGate := by
    funext g;cases g with | mk op t => cases op <;> rfl
  rw [e]
end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem saveBinaryWithBudget (n : ℕ) (bit : Bool) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (unique : C.gates.countP isNegGate ≤ 1)
    (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (inc : ∃ y : Fin n → Bool, f (Fin.snoc y true) = true ∧ f (Fin.snoc y false) = false)
    (nonconstant : ∃ y z : Fin n → Bool, f (Fin.snoc y bit) ≠ f (Fin.snoc z bit)) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y bit)) ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates ∧ D.gates.countP isNegGate ≤ C.gates.countP isNegGate := by
  have hout : C.output ≠ n := by
    intro out
    have fixed (y : Fin n → Bool) : f (Fin.snoc y bit) = bit := by
      rw [← comp,ofFn_snoc]
      change (wiresFrom C.gates (List.ofFn y ++ [bit])).getD C.output false = bit
      rw [out,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨y,z,ne⟩ := nonconstant
    exact ne ((fixed _).trans (fixed _).symm)
  obtain ⟨y,yup,ydn⟩ := inc
  obtain ⟨g,mem,op,read⟩ := needsPositiveReader n C fit unique hout y
    ((comp _).trans yup) ((comp _).trans ydn)
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, NOk g := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact normGate_nok u (fit u hu)
  have same : normGate g = g := by
    cases g with | mk o t => cases o <;> simp_all [normGate]
  have read' : ∃ t ∈ gs, t.op ≠ .not ∧ n ∈ t.inputs :=
    ⟨g,same ▸ List.mem_map_of_mem mem,op,read⟩
  set acc := elim n gs (initStats n bit,[]) with ha
  have val (z : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) = f (Fin.snoc z bit) := by
    have h := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (hok k hk).1) (inv_init n bit z)
    rw [((h.2 C.output).2 : statVal _ _ = _), ← ofFn_snoc,hgs,wiresFrom_norm,← comp]
    rfl
  cases status : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y,z,ne⟩ := nonconstant
    exfalso;apply ne;rw [← val y,← val z,status];rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),?_,?_,?_⟩
    · intro z;have e := val z;rw [status] at e;exact e
    · have h := bin_save n n gs (initStats n bit,[]) hok (by simp [initStats])
        ⟨bit,getD_snoc_len _ _ _ _ (by simp)⟩ read'
      change binaryCount acc.2 + 1 ≤ binaryCount ([] : List Gate) + binaryCount gs at h
      have counts : binaryCount gs = binaryCount C.gates := normBinary _
      rw [counts] at h
      simpa only [binaryCount,List.countP_nil,Nat.zero_add] using h
    · have h := elim_neg_sub n gs (initStats n bit,[])
      change acc.2.countP isNegGate ≤ ([] : List Gate).countP isNegGate + gs.countP isNegGate at h
      have e : gs.countP isNegGate = C.gates.countP isNegGate := normNeg _
      rw [e] at h
      simpa only [List.countP_nil,Nat.zero_add] using h

end Transfer
namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem relabelNeg {n m : Nat} (pi : Fin n → Fin m) (C : Circuit) :
    (relabel n m pi C).gates.countP isNegGate = C.gates.countP isNegGate := by
  simp only [relabel,List.countP_map]
  rfl
end Transfer
end PEqualNP.Outside.L_meta_32632
namespace PEqualNP.Outside.L_meta_32632.CaseCache
open PEqualNP.Outside.L_meta_32632
abbrev Frame := Nat → Nat → Nat → List W → Bool
abbrev Test := Nat → Nat → Nat → Nat → Nat → List W → Bool
abbrev Arg := Nat × Nat × Nat × Nat × Nat × List W

def sameWire (a b : W) : Bool :=
  a.s == b.s && a.a == b.a && a.b == b.b && a.c == b.c && a.r == b.r

theorem sameWire_iff (a b : W) : sameWire a b = true ↔ a = b := by
  cases a; cases b; simp [sameWire, and_assoc]

def sameWires : List W → List W → Bool
  | [],[] => true
  | a :: l,b :: r => sameWire a b && sameWires l r
  | _,_ => false

theorem sameWires_iff (v w : List W) : sameWires v w = true ↔ v = w := by
  induction v generalizing w with
  | nil => cases w <;> simp [sameWires]
  | cons a l ih => cases w <;> simp [sameWires,sameWire_iff,ih]

def same : Arg → Arg → Bool
  | (a,b,c,d,e,v),(f,g,h,i,j,w) => a == f && b == g && c == h && d == i && e == j && sameWires v w

theorem same_iff (v w : Arg) : same v w = true ↔ v = w := by
  rcases v with ⟨a,b,c,d,e,v⟩; rcases w with ⟨f,g,h,i,j,w⟩
  simp [same,sameWires_iff,and_assoc]

def member (M : List Arg) : Test := fun tag fuel k t z v => M.any (same (tag,fuel,k,t,z,v))

noncomputable def original (l m g K : ℕ) : Arg → Bool
  | (tag,fuel,k,t,z,v) => if tag = 0 then BinarySearch.look l m g fuel k t z v else BinarySearch.look1 l m g K fuel k t z v

def Valid (A : Test) (l m g K : ℕ) := ∀ tag fuel k t z v,
  A tag fuel k t z v = true → original l m g K (tag,fuel,k,t,z,v) = false

theorem validList (M : List Arg) (l m g K : ℕ) (ok : ∀ a ∈ M, original l m g K a = false) :
    Valid (member M) l m g K := by
  intro tag fuel k t z v h
  obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
  exact (same_iff _ _).mp e ▸ ok a ha

noncomputable def step0 (l m g : ℕ) (ih : Frame) (k t z : ℕ) (v : List W) : Bool :=
Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => BinarySearch.mv ih l m g k t z v y)) true (Nat.ble v.length 1)
noncomputable def step1 (l m g : ℕ) (base ih : Frame) (k t z : ℕ) (v : List W) : Bool :=
Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (BinarySearch.mv base l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)
noncomputable def cached0 (A : Test) (l m g : ℕ) : Nat → Frame
  | 0 => fun _ _ _ _ => true
  | n+1 => fun k t z v => if A 0 (n+1) k t z v then false else step0 l m g (cached0 A l m g n) k t z v

noncomputable def cached1 (A : Test) (l m g K : ℕ) : Nat → Frame
  | 0 => fun _ _ _ _ => true
  | n+1 => fun k t z v => if A 1 (n+1) k t z v then false else
      step1 l m g (cached0 A l m g K) (cached1 A l m g K n) k t z v

theorem cached0_eq {A : Test} {l m g K : ℕ} (h : Valid A l m g K) (fuel : Nat) :
    cached0 A l m g fuel = BinarySearch.look l m g fuel := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    funext k t z v
    simp only [cached0]
    cases hc : A 0 (n+1) k t z v with
    | false => simp only [Bool.false_eq_true,ite_false,ih]; rfl
    | true => exact (h 0 (n+1) k t z v hc).symm

theorem cached1_eq {A : Test} {l m g K : ℕ} (h : Valid A l m g K) (fuel : Nat) :
    cached1 A l m g K fuel = BinarySearch.look1 l m g K fuel := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    funext k t z v
    simp only [cached1]
    cases hc : A 1 (n+1) k t z v with
    | false => simp only [Bool.false_eq_true,ite_false,ih,cached0_eq h]; rfl
    | true => exact (h 1 (n+1) k t z v hc).symm

noncomputable def checkpoint (A : Test) (l m g K : ℕ) : Arg → Bool
  | (tag,fuel,k,t,z,v) => if tag = 0 then cached0 A l m g fuel k t z v else cached1 A l m g K fuel k t z v

theorem checkpoint_eq {A : Test} {l m g K : ℕ} (h : Valid A l m g K) (a : Arg) :
    checkpoint A l m g K a = original l m g K a := by
  rcases a with ⟨tag,fuel,k,t,z,v⟩
  simp only [checkpoint,original,cached0_eq h,cached1_eq h]

noncomputable def branchTop (A : Test) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (BinarySearch.mv (cached0 A l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (cached1 A l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
noncomputable def branching (A : Test) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => branchTop A l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

theorem branching_eq {A : Test} {l m g K : ℕ} (h : Valid A l m g K) (B t p H ph : ℕ) :
    branching A l m g B K t p H ph = BinarySearch.startv l m g B K t p H ph := by
  funext v
  simp only [branching,BinarySearch.startv,branchTop,BinarySearch.topC,cached0_eq h,cached1_eq h]

noncomputable def root (A : Test) (Q : List (ℕ × ℕ)) (K t H ph : ℕ) : Bool :=
  let l := lz 4
  let m := mz 4
  let g := pL (Q.map fun _ => 16)
  let B := pL (Q.map fun e => 16 + (K - t - e.2))
  let v := avl (PZ Q) m (rawL [])
  frc v fun v => st l fun l => st m fun m => st g fun g => st B fun B => st (pwr [] 4) fun p =>
    anySub (pos t) l v 0 (branching A l m g B K t p H ph)

theorem root_eq {A : Test} (Q : List (ℕ × ℕ)) (K t H ph : ℕ)
    (h : Valid A (lz 4) (mz 4) (pL (Q.map fun _ => 16)) K) :
    root A Q K t H ph = BinarySearch.chk [] Q 4 K t H ph := by
  simp only [root,BinarySearch.chk,frc_eq,st_eq,branching_eq h]

end PEqualNP.Outside.L_meta_32632.CaseCache
namespace PEqualNP.Outside.L_meta_32632.RowData
open PEqualNP.Outside.L_meta_32632 PEqualNP.Outside.L_meta_32632.CaseCache
def table := pr activeBounds 4
noncomputable def budget := pL (table.map fun _ => 16)
noncomputable def input (i : ℕ) : W := mkW (PZ table) ((rawP.getD i 0) &&& mz 4)
def invert (w : W) : W := ⟨w.s ^^^ mz 4,w.b,w.a,w.c,0⟩
def gate (d : Bool) (a b : W) : W :=
  let x := if d then a.a &&& b.a else a.a ||| b.a
  let y := if d then a.b ||| b.b else a.b &&& b.b
  ⟨if d then a.s ||| b.s else a.s &&& b.s, x, y, x ||| y, 0⟩
noncomputable def w0 : W := input 0
noncomputable def w1 : W := input 3
noncomputable def w2 : W := input 1
noncomputable def w3 : W := input 5
noncomputable def w4 : W := input 4
noncomputable def w5 : W := input 6
noncomputable def w6 : W := input 7
noncomputable def w7 : W := invert w0
noncomputable def w8 : W := invert w1
noncomputable def w9 : W := gate true w1 w0
noncomputable def w10 : W := invert w2
noncomputable def w11 : W := gate false w2 w0
noncomputable def w12 : W := gate true w2 w0
noncomputable def w13 : W := gate true w2 w1
noncomputable def w14 : W := invert w3
noncomputable def w15 : W := gate true w3 w0
noncomputable def w16 : W := gate true w3 w1
noncomputable def w17 : W := gate true w3 w2
noncomputable def w18 : W := invert w4
noncomputable def w19 : W := gate true w4 w0
noncomputable def w20 : W := gate true w4 w1
noncomputable def w21 : W := gate true w4 w2
noncomputable def w22 : W := gate true w4 w3
noncomputable def w23 : W := invert w5
noncomputable def w24 : W := gate false w5 w0
noncomputable def w25 : W := gate true w5 w0
noncomputable def w26 : W := gate true w5 w1
noncomputable def w27 : W := gate false w5 w2
noncomputable def w28 : W := gate true w5 w2
noncomputable def w29 : W := gate true w5 w3
noncomputable def w30 : W := gate true w5 w4
noncomputable def w31 : W := invert w6
noncomputable def w32 : W := gate false w6 w0
noncomputable def w33 : W := gate true w6 w0
noncomputable def w34 : W := gate true w6 w1
noncomputable def w35 : W := gate false w6 w2
noncomputable def w36 : W := gate true w6 w2
noncomputable def w37 : W := gate true w6 w3
noncomputable def w38 : W := gate true w6 w4
noncomputable def w39 : W := gate false w6 w5
noncomputable def w40 : W := gate true w6 w5
noncomputable def w42 : W := gate false w7 w2
noncomputable def w43 : W := gate true w7 w2
noncomputable def w46 : W := gate false w7 w5
noncomputable def w47 : W := gate true w7 w5
noncomputable def w48 : W := gate false w7 w6
noncomputable def w50 : W := gate false w8 w0
noncomputable def w52 : W := gate false w8 w2
noncomputable def w56 : W := gate false w8 w5
noncomputable def w57 : W := gate true w8 w5
noncomputable def w58 : W := gate false w8 w6
noncomputable def w62 : W := gate true w9 w2
noncomputable def w63 : W := gate true w9 w3
noncomputable def w64 : W := gate true w9 w4
noncomputable def w65 : W := gate false w9 w5
noncomputable def w66 : W := gate true w9 w5
noncomputable def w67 : W := gate false w9 w6
noncomputable def w68 : W := gate true w9 w6
noncomputable def w71 : W := gate false w10 w0
noncomputable def w74 : W := gate true w10 w3
noncomputable def w75 : W := gate true w10 w4
noncomputable def w76 : W := gate false w10 w5
noncomputable def w77 : W := gate true w10 w5
noncomputable def w78 : W := gate false w10 w6
noncomputable def w79 : W := gate true w10 w6
noncomputable def w90 : W := gate true w12 w3
noncomputable def w91 : W := gate true w12 w4
noncomputable def w92 : W := gate false w12 w5
noncomputable def w93 : W := gate true w12 w5
noncomputable def w94 : W := gate false w12 w6
noncomputable def w95 : W := gate true w12 w6
noncomputable def w101 : W := gate true w13 w3
noncomputable def w102 : W := gate true w13 w4
noncomputable def w104 : W := gate true w13 w5
noncomputable def w105 : W := gate false w13 w6
noncomputable def w106 : W := gate true w13 w6
noncomputable def w111 : W := gate false w14 w0
noncomputable def w114 : W := gate false w14 w2
noncomputable def w115 : W := gate true w14 w2
noncomputable def w117 : W := gate false w14 w5
noncomputable def w119 : W := gate false w14 w6
noncomputable def w132 : W := gate true w15 w4
noncomputable def w134 : W := gate true w15 w5
noncomputable def w135 : W := gate false w15 w6
noncomputable def w136 : W := gate true w15 w6
noncomputable def w143 : W := gate false w16 w0
noncomputable def w145 : W := gate true w16 w4
noncomputable def w147 : W := gate true w16 w5
noncomputable def w148 : W := gate false w16 w6
noncomputable def w149 : W := gate true w16 w6
noncomputable def w157 : W := gate true w17 w4
noncomputable def w159 : W := gate true w17 w5
noncomputable def w160 : W := gate false w17 w6
noncomputable def w161 : W := gate true w17 w6
noncomputable def w168 : W := gate false w18 w0
noncomputable def w171 : W := gate false w18 w2
noncomputable def w172 : W := gate true w18 w2
noncomputable def w174 : W := gate false w18 w5
noncomputable def w175 : W := gate true w18 w5
noncomputable def w176 : W := gate false w18 w6
noncomputable def w184 : W := gate false w18 w12
noncomputable def w196 : W := gate false w19 w5
noncomputable def w197 : W := gate true w19 w5
noncomputable def w199 : W := gate true w19 w6
noncomputable def w210 : W := gate false w20 w5
noncomputable def w211 : W := gate true w20 w5
noncomputable def w213 : W := gate true w20 w6
noncomputable def w224 : W := gate true w21 w5
noncomputable def w226 : W := gate true w21 w6
noncomputable def w236 : W := gate false w22 w2
noncomputable def w238 : W := gate true w22 w5
noncomputable def w240 : W := gate true w22 w6
noncomputable def w249 : W := gate false w23 w0
noncomputable def w250 : W := gate true w23 w0
noncomputable def w251 : W := gate true w23 w1
noncomputable def w252 : W := gate false w23 w2
noncomputable def w253 : W := gate true w23 w2
noncomputable def w255 : W := gate true w23 w4
noncomputable def w256 : W := gate false w23 w6
noncomputable def w284 : W := gate true w24 w1
noncomputable def w285 : W := gate true w24 w2
noncomputable def w286 : W := gate true w24 w3
noncomputable def w287 : W := gate true w24 w4
noncomputable def w288 : W := gate true w24 w6
noncomputable def w291 : W := gate true w24 w11
noncomputable def w295 : W := gate false w25 w6
noncomputable def w296 : W := gate true w25 w6
noncomputable def w302 : W := gate false w25 w12
noncomputable def w308 : W := gate false w26 w0
noncomputable def w311 : W := gate true w26 w6
noncomputable def w325 : W := gate true w27 w6
noncomputable def w330 : W := gate false w28 w4
noncomputable def w331 : W := gate false w28 w6
noncomputable def w332 : W := gate true w28 w6
noncomputable def w343 : W := gate false w29 w0
noncomputable def w346 : W := gate true w29 w6
noncomputable def w360 : W := gate true w30 w6
noncomputable def w371 : W := gate false w31 w0
noncomputable def w374 : W := gate false w31 w2
noncomputable def w378 : W := gate false w31 w5
noncomputable def w419 : W := gate true w32 w1
noncomputable def w420 : W := gate true w32 w2
noncomputable def w421 : W := gate true w32 w3
noncomputable def w423 : W := gate true w32 w5
noncomputable def w426 : W := gate true w32 w11
noncomputable def w430 : W := gate true w32 w24
noncomputable def w431 : W := gate false w33 w2
noncomputable def w432 : W := gate false w33 w5
noncomputable def w438 : W := gate false w33 w12
noncomputable def w447 : W := gate false w34 w0
noncomputable def w455 : W := gate false w34 w13
noncomputable def w464 : W := gate true w35 w3
noncomputable def w465 : W := gate true w35 w4
noncomputable def w466 : W := gate true w35 w5
noncomputable def w472 : W := gate true w35 w27
noncomputable def w487 : W := gate false w37 w0
noncomputable def w488 : W := gate false w37 w2
noncomputable def w504 : W := gate false w38 w2
noncomputable def w532 : W := gate false w40 w18
def slackBlock0 : Array (Nat) := #[0x94a5294a5494a539ce7294e72ac2b2a4a559ce929565394253a56539ca319ce7384e70a467394e7194a1384eb29ce7194e328c63184e318ce139c6338c6318c2118c610, 0x94a529ce739ce75ace7494e72b46939ce74a52b19d2748c674a5695ad2739ce948ca919ca549d2529c6328d2b29ce7394e749ca528ca5294a339c6338c6319c6318c610, 0x94a529ce73ace739ce7294e72b46d3ace76a52b1ad2b48ce74a5e95aca319ce948d291aca949d2549c6729d2b2aceb3956748ca528d25294a739c6738ce339c6318c612, 0x94a52a4a52a4a539ce7294e72aca7494a939ce90a4e9384a53a56539ca319ce739467294e3394e339425194eb29ce7194e328c631946318c6539c6338c6318c2118c610, 0x94a52ace759ce739ce7294e72b4e959ceb4a52b39da749c674b5695aca319ce949ca939d2549d2929ce348d2b49d673a4e748ca529ca52952339ce339c6719c6318c650, 0x94a7394a539ce939ce739d293ac2b2a4a76a52719d27494a959da74aca52a527384e91aca948ca5294a5395691a4a9295674946528d2118ce52942538ce339c6108c612, 0x94a739ce72a4a739ce739d293a46939ce95ad690a4e938ce749da74aca52a52528ca72a4e7594e339c6729d291a4a92956749423194e3294a72942538ce339c2308c612, 0x94a739ce7494a739ce739d293a46939ce95ad692956539c674ad274aca52a52528ca72a4e7594e719ce348d29395252a4e749423194e329523294a139c6719c2308c650, 0x94a739ce74a52b39ce739d293a46939ce95ad692a56959ceb6adab6bca52a52528ca72a4e7594e739ce749da93a5294a56b69423194e329527294a539ce73ac2308c652, 0x94a73a4a539ce939ce739d293aca7494ab4a52719d27494a95ad274aca52a5273946939d2548ca5294a539569395252a4e74946529ca118ce5294a139c6719c6108c650, 0x94a73a52939ce939ce739d293acab4a52b6b5a719d27494a95adab6bca52a527394e93ad2968ca5294a5395693a5294a56b6946529d2118ce5294a539ce73ac6108c652, 0x94a73a5294a52b39ce739d293acab4a52b6b5a92a56959ceb6adab6bca52a527394e93ad29694e739ce749da93a5294a56b6946529d2329527294a539ce73ac6308c652, 0x94a949ce74a52b39ce74a56b4a46939ceb6b5a92a56959ceb6adab6bca73ad6528ca93ad29694e739ce749da93a5294a56b69c2529d2329527294a539ce73ac6308c652, 0x94e529ce94a5293a529294e93a4694a5274a5692a5ab694a96adab7b4e32a525394e519ce759529494a549da93a56b59d2969461194e51952729ce7294a73ac23184652, 0x94e52a4a739ce73a529294e93aca759ce939d2719d6958c675ad275a4e32a52749ca72952548ce738c63395693956739ca5494a329ca308ce529ce32942719c61184650, 0x94e52a52b4a5293a529294e93acab5ad695ada92a5ab694a96adab7b4e32a52749d272a52969529494a549da93a56b59d29694a329d251952729ce7294a73ac63184652, 0x94e539ce749ca54a4e9395273ac6b3a4e75a52b29d67394653ad674a4e529d2738ce71a4a749d2729ca338ceb39d2729ce53946318ce5294e339ca3394651942318c630, 0x94e539ce74ad294a4e9395273ac6b3a4e75a52b2ad6b594e95adeb6b4e529d2738ce71a4a749d2749ca739d6b3ad2b49d695946318ce5294e739ca7394e53a42318c632, 0x94e53a4a53a4e74a4e9395273b4a949ca949ce91a52948ca74ad674a4e529d29494a929ce5394e5394652952b39d2729ce5394a5294a318ca539ca3394651946118c630, 0x94e53a5293a4e74a4e9395273b4ad4ad296ad691a52948ca74adeb6b4e529d29495292ace9594e5394652952b3ad2b49d69594a52952318ca539ca7394e53a46118c632, 0x94e53a5294ad294a4e9395273b4ad4ad296ad6b2ad6b594e95adeb6b4e529d29495292ace959d2749ca739d6b3ad2b49d69594a529525294e739ca7394e53a46318c632, 0x94e7394a72a4a73a52939d2b49c2739ce74a5690a52b48ce7595654a4e53ad6328ca519ce75952549c673a56709ca928d2549c21194e529ce919425284a339c25084612, 0x94e7394a7494a73a52939d2b49c2739ce74a569295a749c675a4e54a4e53ad6328ca519ce75952929ce35956728d2529ca549c21194e529d65194a12942719c25084650, 0x94e7394a74a52b3a52939d2b49c2739ce74a5692a5ab69ceb7a5696b4e53ad6328ca519ce75952949ce75a5e729d2949d2969c21194e529d69194a5294a73ac25084652]
def slackBlock1 : Array (Nat) := #[0x94e739ce939ce93a52939d2b4a4694a5295ada719d69594a96a5696b4e53ad65394e72a52968ce7394a549da729d2949d2969c6329d2319527194a5294a73ac63084652, 0x94e73a4a7294a73a52939d2b4aca759ceb4a5650952748c675a4e54a4e53ad6749ca939d67584a528c633956728d2529ca549ca53a4e108ce5194a12942719ca1084650, 0x94e7494a549ca74a4e949d694a42929ca75a52b29d6739ca74a5253a4e73a565284a71a4a749d272a4e549529294e519ce539c2318ce539d2529461394651942508c630, 0x94e7494a54ad2b4a4e949d694a42929ca75a52b2ad6b59d2b6a5a95b4e73a565284a71a4a749d274a4e94a5a92a4e939d6959c2318ce539d2929465394e53a42508c632, 0x94e749ce73a4e94a4e949d694ac6b3a4e96ad691a529494e95a5a95b4e73a56738ce92ace9594e539ca739d692a4e939d6959c6529523294e729465394e53a46308c632, 0x94e74a4a529ca74a4e949d694b4a949cab5a52709ce738ca74a5253a4e73a569494ab3a52748ca32946529529294e519ce539ca739ce118ca52946139465194a108c630, 0x94e9494a74a52b3a5294a56d59c2739ce95ada92a5ab69ceb7a5696b4e74b5a328ca72a5296952949ce75a5e729d2949d296a42329d2529d69194a5294a73ac65084652, 0x9525394a74ad294ad2b395294a4293a4e549d2b2adad694e96a5a96ad253a56538ce509ca749d6959ca74a5a92a52b4952759c6118ce729d2929ca728ca53a425184632, 0x952539ce93a4e74ad2b395294ac6b4ad275a5691a56b58ca75a5a96ad253a567495271a4e9595274946539d692a52b4952759ca329525194e729ca728ca53a463184632, 0x952549ce73ace75aceb495674b46d3ace76a52b1ad2b48ce74a5e95ad2739d6948d291aca949d2549c6729d2b2aceb3956749ca528d25294a739c6738ce339c6318c612, 0x952549ce74ad295aceb495674b46d3ace76a52b2ad6b594e95adeb6b52739d6948d291aca949d2749ca739d6b3ad2b49d6959ca528d25294e739ca7394e53a46318c632, 0x95254a5293ace75aceb495674b4ad4ad296ad6b1ad2b48ce74adeb6b52739d69495292ace959d2549c6729d2b3ad2b49d6959ca529525294a739ca7394e53a46318c632, 0x9527494a73a4e94ad2b49d6b5a4293a4e75a5691a56b594e969d675ad274ada538ce71a4e95952749ca74a5a719ce9395275a4632952529d291946528ca53a465084632, 0x952749ce929ca74ad2b49d6b5ac6b4ad296ada709d2948ca759d675ad274ada7495292ad2b68ce53946539d6719ce9395275a4a539d63194e71946528ca53a4a3084632, 0x95274a4e94ace95aceb495694b46d4ace96a56b1ad6b494e75ade96b52739d6948d291ace949d2549c6739d2b2ad2b39d6759ca528d25294a739c6738ce539c6318c612, 0x9ca5294e539d2749d2929d272ac6d2a4e55a4e72a52758c6949da94a4e51a52938d271ac67494a738ca528d692aca938d27394a518d23184e53946728ce129c6118c212, 0x9ca5294e539d276ad2949d272ac69294e53a4eb2a52758c6949d294a5693a52938ca719c634a52739ca528d6929ca538ca73a4a518ca7394e53946328c6109c6518c210, 0x9ca529d272a4e549d2929d272a4ab39d274ad291ace9484a739da94a4e51a527294e52a4a559ce549467195292aca938d2739463094e528ca73946728ce129c2318c212, 0x9ca529d27494e549d2929d272a4ab39d274ad2939d65494273ad294a4e51a527294e52a4a559ce9294e33852949d2539ca739463094e528d23394e329c6509c2318c250, 0x9ca529d274a56949d2929d272a4ab39d274ad293ad69694ab5adad6b4e51a527294e52a4a559ce9494e7395a94ad2959d2b59463094e528d27394e729ce52ac2318c252, 0x9ca52a4e539d2749d2929d272ace9494e93a4e72a52758c694ad294a4e51a52939ca739ce3494a738ca528d6949d2539ca7394a519ca3184e5394e329c6509c6118c250, 0x9ca52a56939d2749d2929d272aced4a5695b5672a52758c694adad6b4e51a52939d273ace7694a738ca528d694ad2959d2b594a519d23184e5394e729ce52ac6118c252, 0x9ca52a5694a56949d2929d272aced4a5695b5693ad69694ab5adad6b4e51a52939d273ace769ce9494e7395a94ad2959d2b594a519d2528d27394e729ce52ac6318c252, 0x9ca729ca549ce74a52739ce92b46b3a4a759ce929d67494674a5a74a4e52a4e948ce91a4a7394e7294a338d2b2a4e929525394a528ce318ce339c6538ca32946118c611]
def slackBlock2 : Array (Nat) := #[0x9ca729ca54ace76b52759ce92b467394a739ced2ad6b494e74a5a74a5694a4e948c69194a33a5674a4a739d2b2a4e9295253a4a528c6739ce739c6538ca32946518c611, 0x9ca72a4e73a4a54a52739ce92aca949ce94a52b1a52938ca53a5a74a4e52a4e7394a729ce549d2539c65294eb2a4e92952539463194a5294a539c6538ca32942318c611, 0x9ca72a4e749ce75ad2749ce92b4a949ce94a52b29d67494674ad695ad273a4e9494a929ce549d2729ca338d2b39d2739ce749ca5294a5294e339ca33946519c6318c630, 0x9ca72a4e75a5294a52739ce92aca949ce94a52b3a5a959ca95b5ab6b4e52a4e7394a729ce549d2939ce54956b4a5694a52959463194a52952539ce539ca72a42318c651, 0x9ca72aca549ce74a52739ce92b4e7594ab39ce929d67494674b5ab6b4e52a4e949c6939523394e7294a338d2b4a5694a529594a529c6318ce339ce539ca72a46118c651, 0x9ca72ad2949ce74a52739ce92b4eb5a52b5ad6929d67494674b5ab6b4e52a4e949ce93a527594e7294a338d2b4a5694a529594a529ce318ce339ce539ca72a46118c651, 0x9ca72ad295a5294a52739ce92b4eb5a52b5ad6b3a5a959ca95b5ab6b4e52a4e949ce93a52759d2939ce54956b4a5694a529594a529ce52952539ce539ca72a46318c651, 0x9ca7394e5294e749d293a56939c69294e74ad2519ce548c694a56b5b4e72ad6518ca52a4a558c6528ca528d673a4e749d2b59c23094e1184e528ca529ce52ac2108c252, 0x9ca7394e5294e749d293a5693ac6d2a4e76ad2519ce548c69495673a4e72ad6938d292b4a958c6528ca528d671a46728d2739ca729561184e528c2528ce129ca108c212, 0x9ca7394e5294e76ad295a5693ac69294e74ad2919ce548c69494e73a56b4ad6938ca92a4a559ce529ca528d671946328ca73aca7294e5394e528c2128c6109ca508c210, 0x9ca7394e52a4e749d293a56939c69294e74ad291ace948ce9495673a4e72ad6518ca52a4a559ce549ca929d671a46728d2739c23094e5394e928c2528ce129c2508c212, 0x9ca7394e539d2949d293a56939c69294e74ad272a527594ab5a56b5b4e72ad6518ca52a4a5594a7394e7395a73a4e749d2b59c23094e328d2728ca529ce52ac2308c252, 0x9ca7394e53a52949d293a56939c69294e74ad292ad29594eb59d694ace72ad6518ca52a4a559ce749ce939da72a4a73952949c23094e53952928c65294e32a42508c232, 0x9ca7394e5494e749d293a56939c69294e74ad2939d6549c694a4e73a4e72ad6518ca52a4a559ce929d2548d67394e329ca739c23094e53956528ca129c6509c2508c250, 0x9ca7394e54a56b49d293a56939c69294e74ad293ad6969ced6a56b5b4e72ad6518ca52a4a559ce949d2949de73a4e749d2b59c23094e53956928ca529ce52ac2508c252, 0x9ca739d2739d2949d293a5693a4ab39d295b5672a527594ab5a56b5b4e72ad67294e73ace7694a7394e7395a73a4e749d2b59c6519d2328d2728ca529ce52ac6308c252, 0x9ca73a4e5294e749d293a5693ace9494eb4ad2519ce548c694a4e73a4e72ad6939ca94a52558c6528ca528d67394e329ca739ca72a4e1184e528ca129c6509ca108c250, 0x9ca92a4e749ce74a5274a4eb2aca949ceb4a52929d6749c674ad695ace73ace7394a939d25494e729ce348d2939d273a4e749c6529ca329523294a339c6719c6308c650, 0x9ca939ca5394a74a5274a52b3a467394a94a52719525394674ad695b4e73ad2528c6729ce548ca5194a338d2939d273a52959c23194a118ce3294a339ca72a42108c651, 0x9ca939ca5394a74a5274a52b3b46b3a4a96a527195253946749d653a4e73ad2948ceb2ace948ca5194a338d2919ca71952539ca73952118ce32942338ca3294a108c611, 0x9ca939ca53a4a74a5274a52b3a467394a94a52b1a529394e749d653a4e73ad2528c6729ce549d253a4a739d2919ca71952539c23194a539ce72942338ca32942508c611, 0x9ca939ca55a52b4a5274a52b3a467394a94a52b3a5a95a4eb6ad695b4e73ad2528c6729ce549d293a52759da939d273a52959c23194a539d67294a339ca72a42508c651, 0x9ca93a4e749ce94a5274a52b3aca949ceb5ad6929d6749ca95ad695b4e73ad27394a93a527594e729ce54956939d273a52959c6529ce329525294a339ca72a46308c651, 0x9ca93ad29394a74a5274a52b3b4eb5a52d6b5a719525394674ad695b4e73ad2949ceb4ad6968ca5194a338d2939d273a52959ca73a52118ce3294a339ca72a4a108c651]
def slackBlock3 : Array (Nat) := #[0x9ca9494e54a56b49d294adab49c69294e95b5693ad6969ced6a56b5b4e93b5a518ca73ace769ce949d2949de73a4e749d2b5a42519d253956928ca529ce52ac6508c252, 0x9ca94a569294e949d294adab4aced4a56b6bda519ce5494ab5a56b5b4e93b5a939d294b52978c65294e7395a73a4e749d2b5a4a72a56128d2728ca529ce52aca308c252, 0x9cab49ca55a52b4a5275ad6d4a467394ab5ad6b3a5a95a4eb6ad695b4e94b56528c693a52759d293a52759da939d273a5295a42529ce539d67294a339ca72a46508c651, 0x9ce5294e72a4e54a56b29d2939c6939d253a5291ad2b584a74956749d252ad65294e319ca559d275946729d671a4a9384e539c61094e7294e929467184a129c25184212, 0x9ce5294e7494e54a56b29d2939c6939d253a52939da7594274a4e749d252ad65294e319ca559d2b394e348d67395253946539c61094e729565294e31942509c25184250, 0x9ce5294e74a5694a56b29d2939c6939d253a5293adab794ab6a56b6ad252ad65294e319ca559d2b594e749de73a529594e959c61094e729569294e7194a52ac25184252, 0x9ce529d2939d274a56b29d293a4ab4a5674ad672a56968c695a56b6ad252ad6739d252a4e7694e948ca5395a73a529594e959ca319d2518d27294e7194a52ac63184252, 0x9ce52a4e7294e54a56b29d293ace959d293a52519d27584274a4e749d252ad694a4e739d2558ca73846328d67395253946539ce52a4e3084e5294e31942509ca1184250, 0x9ce5394e549ce55a52b39d673a46b29ce54a4eb3a567494673a52739d272a56728ce51a4654a52939ce538d2939ce5294a529c6308ce739525394a3294630942518c230, 0x9ce5394e54ad695a52b39d673a46b29ce54a4eb3b56b694eb5a5ab5ad272a56728ce51a4654a52959ce939da93ace94952949c6308ce739529394a7294e32a42518c232, 0x9ce539d273a5275a52b39d673acad3a5275ad292ad2958ca94a5ab5ad272a569395272aca759ce7494a7295693ace94952949ca51952528ce7394a7294e32a46318c232, 0x9ce53a4e529ce55a52b39d673b4eb49ce94a4e71a4e7484673a52739d272a56b49ce93a4e5494a538c6518d2939ce5294a529ce729ce3184a5394a329463094a118c230, 0x9ce729ca73a4a54ad6939ceb3a46749ce739d2b1a56b48ca549d6549d253ad25394a5194e549d6749c6539d2919ce928ce339c61194a729ce729c652846329425184611, 0x9ce729ca75a5294ad6939ceb3a46749ce739d2b3a5eb69ca96ad696ad253ad25394a5194e549d6b49ce559da939d6949ce759c61194a729d6729ce5294672a425184651, 0x9ce72a4e949ce74ad6939ceb3aca95a5294a56929da9594675ad696ad253ad2749ce729d2759529394a34956939d6949ce759ca329ce51952529ce5294672a463184651, 0x9ce7394e739d294a56b3a56b49c6939d274ad672a569694ab69d295ad273b5a5294e52a4e7694e9494e749de529ce7494e95a46319d252956918ca5194a52ac65084252, 0x9ce739ca539ca55ad2949d293ac6939ca749ce919d2738c653ada95ad273a52738ca719ca5394e52946328ceb3a52939d2749c6318ca318ca339ca5394a529c2118c631, 0x9ce739ca54a4e75ad2949d293ac6939ca749ceb2a569494a74ada95ad273a52738ca719ca539d2739ca53952b3a52939d2749c6318ca5294e539ca5394a529c2318c631, 0x9ce739ca54a4e95ad2949d293ac6939ca749ceb2a56949ce95a5674ad273a52738ca719ca539d273a4e749d6929ce729d2749c6318ca539d2729463394a529c2508c631, 0x9ce739ca54a5275ad2949d293ac6939ca749ceb3ad69594a94a5694a5273a52738ca719ca53a52949ce7395693a4e7394e739c6318ca739527394a5294a319c2518c231, 0x9ce739ca55aca55ad2949d293ac6939ca749ced3adab39ce53ada539d273a52738ca719ca53a5694a4e749ceb3a52919d2329c6318ca739d2739ca5394a528c2518c631, 0x9ce739ca55ad295ad2949d293ac6939ca749ced3adab59ce95ada95ad273a52738ca719ca53a5694a4e749d6b3a52939d2749c6318ca739d2739ca5394a529c2518c631, 0x9ce739ce739d6b4a5293a5693a46939ce74ad273ad2769ced69d2b4b4e72ad6528ca52a4a559ca949d2949de53a4a549d2b59c23094e539569284a529ce52ac2508c252, 0x9ce739ce73ace74a52939d293ac6b3a4e75a52b1ad2b48ce74adeb6b4e52a52738ce71a4a749d2549c6729d2b3ad2b49d695946318ce5294a739ca7394e53a42318c632]
def slackBlock4 : Array (Nat) := #[0x9ce739ce73ace74a52939d293b46d3ace76a52b1ad2b48ce74a5e95ace52a52948d291aca949d2549c6729d2b2aceb39567494a528d25294a739c6738ce339c6318c612, 0x9ce739ce73ad675a52b39d693a46b39ce74a52b3b52b68ceb49dab4a5272a56728ce51a4a54a52959ce929da93aca948d2939c6308ce739529394a7294e12a42518c232, 0x9ce739ce74a5294a52939d293b46d3ace76a5292a569594a95a5e95ace52a52948d291aca9494e7394a53956b2aceb39567494a528d2318ce539c6738ce339c6118c612, 0x9ce739ce74ace76b52959d293b46939ce74a52d2ad6b494e74a5a74a5694a52948ca919ca54a5674a4a739d2b2a4e9295253a4a528ca739ce739c6538ca32946518c611, 0x9ce739ce75a4e76b52959d293b46939ce74a52d3a5a949ca74ad674a5694a52948ca919ca54a5693a4e54952b39d2729ce53a4a528ca739d2539ca3394651946518c630, 0x9ce739ce75ace75ad2949d293ac6939ce74a52d3adab49ce74ada74a5273a52738ca719ca54a5694a4e749d2b3a52929d2539c6318ca739d2739ca5394a52942518c631, 0x9ce739d29294e74a56b3a56b4a4ab4a5695b5a519d2758c6959d295ad273b5a739d273ad2978ca738ca5395a529ce7494e95a4a52a56318d2718ca5194a52aca3084252, 0x9ce739d6b39ce74a56b39d293a4ed5ada74b5a719d2758c6749d2b6a5252ad694a5653ad2978ca738c6328d653a52958ca959ce52a563084e5294e7094a52aca1184252, 0x9ce73a4e74a4e75ad2949d293b4ab4a4e95a52b2a569494a74ada95ad273a529494e92a4e749d2739ca53952b3a52939d2749ca5294e5294e539ca5394a529c6318c631, 0x9ce73a4e759ce74a52939d293aca949ce94a52b39da749c674b5ab6b4e52a527394a729ce549d2929ce348d2b4a5694a52959463194a52952339ce539ca72a42318c651, 0x9ce73a5293ace74a52939d293acab4a5295ad6b1ad2b48ce74a5e95ace52a527394e72a4e759d2549c6729d2b2aceb3956749463194e5294a739c6738ce339c2318c612, 0x9ce73a5294ad294a52939d293acab4a5295ad6b2ad6b594e95adeb6b4e52a527394e72a4e759d2749ca739d6b3ad2b49d6959463194e5294e739ca7394e53a42318c632, 0x9ce73a52959ce74a52939d293acab4a5295ad6b39da749c674b5695ace52a527394e72a4e759d2929ce348d2b49d673a4e749463194e52952339ce339c6719c2318c650, 0x9ce73aca539ca55ad2949d293bced5acab69ce919d2738c653ada539d273a52b59d2b3ad29394e52946328ceb3a52919d2329ce739d2318ca339ca5394a528ca118c631, 0x9ce73ace739ce75ad2949d293bced5aceb6a52919d2748c674ada74a5273a52b59d2b3ad29494e52946328d2b3a52929d2539ce739d2318ca339ca5394a5294a118c631, 0x9ce73ace739ce76b52959d293bceb5a4eb5a52b19d2748c674ad674a5694a52b59ceb3a52749d2529c6328d2b39d2729ce53a4e739ce5294a339ca339465194a318c630, 0x9ce73ace749ce74a52939d293b4e959ceb4a52929d67494674b5ab6b4e52a52949ca939d25494e7294a338d2b4a5694a529594a529ca318ce339ce539ca72a46118c651, 0x9ce73ace74a5294a52939d293b4e959ceb4a5292a569594a95b5695ace52a52949ca939d25494e7394a53956b49d673a4e7494a529ca318ce539ce339c6719c6118c650, 0x9ce73ace759ce74a52939d293b4e959ceb4a52b39da749c674b5695ace52a52949ca939d2549d2929ce348d2b49d673a4e7494a529ca52952339ce339c6719c6318c650, 0x9ce73aceb39ce74ad6939d2b3b4e96ad6b4a5a719d6748c674ad276a5253ad295a52939d6968ce728c6338d293956949ca559ce53a52308ce329ce5294272a4a1184651, 0x9ce73ad2939ca55ad2949d293bced5ad2b6ad6919d2738c653ada95ad273a52b59d2b3ad29594e52946328ceb3a52939d2749ce739d2318ca339ca5394a529ca118c631, 0x9ce7494e53a5295a52b4a5a94a46b29ce75ad292ad29594eb59d694ad293ada728ce72aca759ce749ce939da72a4a7395294a465195253952928c65294e32a46508c232, 0x9ce749ca54a4e75ad2959d694ac6939ca759ceb2a569494e74a5674a5294a56738ca91a4a739d273a4a739d2929ce7295253a46528ce539ce72946338ca32946508c611, 0x9ce749ce73aceb4a52949d694a46939ce75a52b1ad2b49d2b69da74b4e73a56528ca71a4a749d254a4e94a5a91a4a929d6959c2318ce539d2929425394e53a42508c632]
def slackBlock5 : Array (Nat) := #[0x9ce749d2729ce75a52b4a5a94acad3a5296b5671a4e748ca949d694ad293ada9395293b4e9694a5394a7295672a4a7395294a4a729d6328ce728c65294e32a4a308c232, 0x9ce74a5294a5294a52949d694acab4a5296ad692a569594e95adab6b4e73a567394e92ace9594e739ca739d693a52949d6959c6529523294e7294a5394e53a46308c632, 0x9ce759ce73ace94a52959da95a46939ce76a52b1ad2b4952959da74ace94a5a528ca91aca949d254a4a93a5691a4a9295674a42528d2539ce92942538ce339c6508c612, 0x9ce939ca749ce94ad694a52d4a46749ce94a56929da959ca96a5275ad274b565394a729d275952939ce559da72952739ce75a46329ce529d67194a3294672a465084651, 0x9ce939ce759ceb4a5294a52b3a46939ce94a52b39da74a4eb6ad274b4e73ad2528ca729ce549d292a52759da9395252a52959c23194a539d67294a139ca72a42508c651, 0x9ce93a4e9394a74ad694a52d4aca95a52b5ada719567494675a5275ad274b56749ce93a56968ce7294a3495672952739ce75a4a53a52319525194a3294672a4a3084651, 0x9ce93ad295a4e94ad2749ceb3b4eb5a52b5ad6b29da949ca75b5ab6b4e53a4e949ce93a5275952729ca34952b4a5694a529594a529ce3194e339ce539ca72a46118c651, 0x9ce949ca54a4e95ad295a56b4ac6939ca95a52b2a56949ce95a5674ad294ad6738ca92a4e749d273a4e749d6929ce729d274a465294e539d2729463394a529c6508c631, 0x9ce94a4e739ca75ad295a56b4b4ab4a4eb6ad6919d27394a74a5674ad294ad69494eb3ad29594e529ca53952929ce729d274a4a739d23294e529463394a529ca308c631, 0x9ce94a5294a52b4a5294a56b4acab4a52b6b5a92a56959ceb6adab6bce73ad67394e93ad29694e739ce749da93a5294a56b69c6529d2329527294a539ce73ac6308c652, 0x9ce94ace739ce94a5294a56b4b4e959ced5ad6719d27494a95ad274ace73ad6949cab4a56758ca5294a539569395252a4e749ca73a4e118ce5294a139c6719ca108c650, 0x9ceb39ce759ce94a5295ad2d3a46939ceb4a52b39da74a4a95ad274ace94b52528ca939d2549d292a52559569395252a4e74a42529ca539d65294a139c6719c6508c650, 0x9ceb3ace739ce74a5295ad2d3b4e959ced5ad6719d2749c674ad274ace94b52949cab4a56758ca529ce348d29395252a4e74a4a73a4e129523294a139c6719ca308c650, 0x9d25394e73a5275ad6d39d694a46b3a5254a5292ad6b68ca959d695a5673ada7395251a4a759d29594a739da72a4e948ce74a4a31952729529294a718ca32a465184232, 0x9d2539d2929ce55ad6d39d694acad4ad675ad671a5295846749d695a5673ada949d672ace9694e748c65295672a4e948ce74a4e529d6518ce7294a718ca32a4a3184232, 0x9d25494e53ad276ad2d49da74ac6d2a4e55a4eb2b52b58ce949da94a5693a5a938d271ac674a52759ca929d692aca938d273a4a518d27394e93946728ce129c6518c212, 0x9d25494e54ad696ad2d49da74ac6d2a4e55a4eb3b56b694eb5a5ab5ad693a5a938d271ac674a52959ce939da93ace9495294a4a518d2739529394a7294e32a46518c232, 0x9d254a5294ad275ad2b495674b4ad4ad276a52b2ad6b58ce74adeb6ad2739d69495291aca949d2749c6729d2b3ad2b4956749ca528d25294a739ca738ce339c6318c612, 0x9d2739ca74a4e75b56b49d2b4ac694a4e749d2b2a5ab594a75a5675a5674ad67494e719ce749d6949ca549d6929d29394e54a4a3294e729d2729ca528c6529c65184631, 0x9d273a4e939ca55b56b49d2b4b4ab5ad295a56919d6948c654a5675a5674ad6959d292a52959527394633952929d29394e54a4e539d25194e529ca528c6529ca3184631, 0x9d273a52b4a5294ad6b39d2b4acab5ad695ada92a5ab694a96adab7b5253ad6749d272a52969529494a549da93a56b59d2969ca329d251952729ce7294a73ac63184652, 0x9d27494e729ce75ad6d4a5ab5a46b3a5275ad671a52958ca9595274a5694b5e7395272ace9694e7494a739da519ca738ce74aca529d652952918c6518ca32a4a5084232, 0x9d2749ca54ace76b52b59d694b46b3a4a759ced2ad6b494e74a5a74a5694a56948ce91a4a73a5674a4a739d2b2a4e9295253a4a528ce739ce739c6538ca32946518c611, 0x9d2749ca55ad296b52b59d694b46b3a4a759ced3adab59ce95ada95ad694a56948ce91a4a73a5694a4e749d6b3a52939d274a4a528ce739d2739ca5394a529c6518c631]
def slackBlock6 : Array (Nat) := #[0x9d2749ce75a4e75ad2b49d694ac6b3a4e75a52d3a5a949ca74ad674a5273a56738ce71a4a74a5693a4e54952b39d2729ce539c6318ce739d2539ca3394651942518c630, 0x9d274a4e73a4a56b52b59d694bcad4ace96a52b1a52938ca53a5a74a5694a56b5952b2ace949d2539c65294eb2a4e9295253a4e739525294a539c6538ca3294a318c611, 0x9d274a5274ad295aceb49d674b4ad3ace96ad2b2ad2b494e94adeb5b52739d6948d292aca949d2549ca729d2b3aceb39d6949ca528d25294a739c67394e339c6318c612, 0x9d274a5294ad295ad2b49d694b4ad4ad296ad6b2ad6b594e95adeb6b5273a569495292ace959d2749ca739d6b3ad2b49d6959ca529525294e739ca7394e53a46318c632, 0x9d274ace73a4e75ad2b49d694bceb5a4eb5a5291a52948ca74ad674a5273a56b59ceb3a527494e5394652952b39d2729ce539ce739ce318ca539ca339465194a118c630, 0x9d274ad293a4a56b52b59d694bced5ad2b6ad6b1a52938ca53ada95ad694a56b59d2b3ad2959d2539c65294eb3a52939d274a4e739d25294a539ca5394a529ca318c631, 0x9d2949ca739ca75b56b5a56d5ac694a4e95a56919d69494a759d254a5695b5a7494e92a5295952739ca549d67194e7294e54aca539d2529d271946328c6529ca5084631, 0x9d2949ce94a52b4ad6b4a56d5a4694a5295ada92a5ab69ceb7a5696b5274b5a5394e72a5296952949ce75a5e729d2949d296a46329d2529d69194a5294a73ac65084652, 0x9d294a4a75ad295b52959d2b4b4694a4a959d2d3adab59ce95ada95ad274a52748ca919ce73a5694a4e749d6b3a52939d2749c6328ca739d2739ca5394a529c2518c631, 0x9d294a52b39ce94ad6b4a56d5acab5ad6b6b5e719d69594a96a5696b5274b5a749d293ad6b78ce7394a549da729d2949d296a4a53a56319527194a5294a73aca3084652, 0x9d294ad294a4a75b52959d2b4bced5ad2b6ad6b19d69394a54ada95ad274a52b59d2b3ad295952529c63394eb3a52939d2749ce739d23194a339ca5394a529ca118c631, 0x9d2959ca53a4a76b52b6a5ab5b46b3a4a96a52b1a529394e749d653a56b5ada948ceb2ace949d253a4a739d2919ca7195253aca73952539ce72942338ca3294a508c611, 0x9d2959ce74ad2b5ad2b5a5ab5ac6b3a4e96ad6b2ad6b59d2b6a5a95b5294ada738ce92ace959d274a4e94a5a92a4e939d695a4652952539d2929465394e53a46508c632, 0x9d295a5293a4e95ad2b5a5ab5b4ad4ad2b7b5a91a529494e95a5a95b5294ada94952b3b52b694e539ca739d692a4e939d695a4a739d63294e729465394e53a4a308c632, 0x9d6739ce73ace74b52d39d295a4693ace74a52b1ad6d58ce759da75a5654a5a548d2519ca949d6759c673a5691a4eb38d254a4a128d2729ce929c67284a339c65184612, 0x9d6749ce94ad295b56d49d6b5ac6b4ad275a56b2adad694e96a5a96ad674ada7495271a4e959d6959ca74a5a92a52b495275a4a32952729d2929ca728ca53a465184632, 0x9d674a52b3a4e75b4ed49d675b4ad5b5696ada91a4eb38ca73a5a96ad6749da959d692ad2b695234946519ce92a52b495275a4e539d651946729ca728ca53a4a3184632, 0x9d674a52b3a4e75b56d49d6b5b4ad5b5696ada91a56b58ca75a5a96ad674ada959d692ad2b695274946539d692a52b495275a4e539d65194e729ca728ca53a4a3184632, 0x9d6759ce739ce74b52d59dab6a4693ace76a56719d2b48ce759d274a5695ade548d291aceb58d2549c673a565194a928d254aca53956529ce909425284a339ca5084612, 0x9d6959ce93a4e95b56d5a5ad6ac6b4ad296ada91a56b594e969d675ad695b5e7495292ad2b6952749ca74a5a719ce9395275aca539d6529d291946528ca53a4a5084632, 0xa4a529d674a56959d6b2a5672a4ed39d674b5293ad69694ab5adad6b5271ad6929d253aca569ce9494e7395a94ad2959d2b59ca509d2528d27394e729ce52ac6318c252, 0xa4a729ce5394e55a5693a5292b4ad3a4e75a4e729d2548c2739d6739d272ad2b495292aca7494a728ca3285292a4a728ce529ce729523184e33946528ca1194a118c211, 0xa4a729ce53a4e55a5693a5292a4a9394e73a4eb2ad2948ca739d6739d272ad27294a529ca34a52749ca7295292a4a728ce529c63094a7394e73946528ca11942518c211, 0xa4a729ce55a5695a5693a5292a4a9394e73a4eb4ada969cab5ad6b5ad272ad27294a529ca34a52b49d27495a94a52749ce949c63094a739567394e529ca51a42518c251]
def slackBlock7 : Array (Nat) := #[0xa4a72a52749d275a5693a5292aceb49d294ad293a567594694ad6b5ad272ad2939ce73a4e559ce9394e538d694a52749ce949ca519ce528d25394e529ca51a46318c251, 0xa4a7395254a56b59d6b3ada939cab295274b5293ad6969ced6a56b5b5292b5a7194e53aca569ce949d2949de73a4e749d2b5a46509d253956928ca529ce52ac6508c252, 0xa4a92ace759ce75ad674a4eb2b4e959ceb4a52b39da749c674b5695ad273ace949ca939d2549d2929ce348d2b49d673a4e749ca529ca52952339ce339c6719c6318c650, 0xa4a92ace75a5295ad674a4eb2b4e959ceb4a52b3a5a959ca95b5ab6b5273ace949ca939d2549d2939ce54956b4a5694a52959ca529ca52952539ce539ca72a46318c651, 0xa4a92ad2959ce75ad674a4eb2b4eb5a52b5ad6b39da749c674b5ab6b5273ace949ce93a52759d2929ce348d2b4a5694a52959ca529ce52952339ce539ca72a46318c651, 0xa4a939ce5394e76ad695ad6b3aca9394e94ad2929d254946949ce73a56b4b569394a93a4e559ce729ce538d67294a3294a73aca729ce53952528c612946309ca508c230, 0xa4a939ce549d295a5694ad6b3a4a9394e94ad293a56759cab5a5294ad293b567294a73a4e559ce939d27495a739ce539ce94a46519ce53956728ca329ca51a46508c251, 0xa4a939d274a56b49d693ad6b39ca9395294b5693ad6969ced6a56b5b4e72b565194a53a4e569ce949d2949de73a4e749d2b59c2309ce53956928ca529ce52ac2508c252, 0xa4a93a4e5394e75a5694ad6b3ace9494eb4ad2729d25494694a4e73a5293b56939ca94a525594a7294e538d67394e329ca73a4a72a4e328d2528ca129c6509ca308c250, 0xa4a93a527394e75a5694ad6b3aceb49d2b5b56729d25494694a5294ad293b56939ce94ad27694a7294e538d6739ce539ce94a4a72a52328d2528ca329ca51a4a308c251, 0xa4a93ad275a5295ad674a52b2b4eb59ceb5ad2b3a5a749ca94b5ab5b5273ace949ca93a52549d2929ce548d2b4a5673a52949ca529ca52952339ce339ca719c6318c650, 0xa4a93ad295a5295a5274a5292b4eb5a52b5ad6b3a56749ca94b5ab6b4e72a4e949ce93a52759ce729ce538d2b4a5694a529594a529ce328ce339ce539ca72a46118c651, 0xa4a94952539d6b59d6b4adab49cab295295b5673ad2769ced69d2b4b5293b5a7194e73ace769ca949d2949de53a4a549d2b5a46519d2539569284a529ce52ac6508c252, 0xa4a949d254a56b59d294ada93a4ab294e95b5293ad6969ced6a56b5b4e92ad6718ca73aca559ce949d2949de73a4e749d2b59c25094e53956928ca529ce52ac2508c252, 0xa4a949d672952959d6b4adab4a4ed39d6b6bda52a4e5594ab59d2b4b5293b5a929d294b52979467394e7395a53a4a549d2b5a4a72a56328d27284a529ce52aca308c252, 0xa4ab3a4a559ce95ad675ad2d3aca7494ab4a52b39da74a4a95ad274ad294b5273946939d2549d292a52559569395252a4e74a46529ca539d65294a139c6719c6508c650, 0xa4ab3a4a55a52b5ad675ad2d3aca7494ab4a52b3a5a95a4eb6ad695b5294b5273946939d2549d293a52759da939d273a5295a46529ca539d67294a339ca72a46508c651, 0xa4ab3ace7494a75ad675ad2d3b4e959ced5ad692956539c674ad274ad294b52949cab4a567594e719ce348d29395252a4e74a4a73a4e329523294a139c6719ca308c650, 0xa4ab3ad29494a75ad675ad2d3b4eb5a52d6b5a92956539c674ad695b5294b52949ceb4ad69694e719ce348d2939d273a5295a4a73a52329523294a339ca72a4a308c651, 0xa4ab4a4a559ceb5ad675ad6d4aca7494ab5ad6b39da74a4eb6ad274b5294b567394693a52759d292a52759da9395252a5295a46529ce539d67294a139ca72a46508c651, 0xa4e5295274a5695a5ad2a56939cab39d653ad293adab794ab6a56b6ad672b5a729d232a4a569d2b594e749de73a529594e95a4a309d2729569294e7194a52ac65184252, 0xa4e5395254ad696a56d3a5a73a4ad29d254aceb3b56b694eb5a5ab5ad692ada9295252ac655a52959ce939da93ace9495294a4a50952739529394a7294e32a46518c232, 0xa4e729ce749d275adab3a52b3a4a949d273a5293a5a9694695a5295a5673b56739ce529ce559d2b494e5495a739d27494a74a4a319ce729567294e5194651a465184251, 0xa4e72a529394e55adab3a52b3aceb5a5694ad6729d6758c274a5295a5673b5694a5273a527694e938ca338d6739d27494a74a4e52a52518d25294e5194651a4a3184251]
def slackBlock8 : Array (Nat) := #[0xa4e72ad295a5275ad6939ce92b4eb5a52b5ad6b3a5a9594674b5ab6b5252a4e949ce93a52759d29394a338d2b4a5694a529594a529ce518ce339ce539ca72a46118c651, 0xa4e739ce54a5276ad6b4a5693acab39ce74a4eb3ad69594a94a5694a5693ad69394e72a4a54a52949ce7395693a4e7394e73a4a5194e739527394a5294a319c6518c231, 0xa4e739ce759d675a5693a5293a4a939ce74a52b4ada769c6b4ad2b4a5272ad27294a529ca54a52b49d2748da94a52549ca939c63094a739567394e529ca50a42518c251, 0xa4e739d273ad275a56b3a5693a4ab39d274ad2b2b52b58ce949da94a5272ad67294e52a4a55a52759ca929d692aca938d2739c63094e7394e93946728ce129c2518c212, 0xa4e73a52739ce56ad6b4a5693b4ed4a5295ad292a52748c673a5694a5693ad6b49d293ace759ce7394a528d293a4e7394e73a4e729d2528ce5394a5294a319ca318c231, 0xa4e73a5694a5695a56b3a5693aced4a5695b5693ad69694ab5adad6b5272ad6939d273ace769ce9494e7395a94ad2959d2b59ca519d2528d27394e729ce52ac6318c252, 0xa4e73ad6739ce75a5693a5293b52d59d6b4b52729d2748c674ad2b4a5272ad2b4a5294ad25694a728ca328d294a52549ca939ce72a523184e3394e529ca50a4a118c251, 0xa4e92a4a759ce75b5a94a4ed3aca759ce939d2b39de959c675ad275a5674b52749ca72952549d6b39ce3595693956739ca54a4a329ca729d6529ce32942719c65184650, 0xa4e92a4a75a5295b5a94a4ed3aca759ce939d2b3a5eb69ca96ad696ad674b52749ca72952549d6b49ce559da939d6949ce75a4a329ca729d6729ce5294672a465184651, 0xa4e92ace9494a55b5a94a4ed3b4e96a52b4a569295a7494254ad275a5674b5295a4e939d6759529294a148d293956739ca54a4e53a4e51952329ce32942719ca3184650, 0xa4e92ad295a5275ad694a4eb2b4eb5a52b4a52b3a5a959c674b5ab6ad273ace949ce939d2549d2939ce348d2b4a5694a4e749ca529ca52952339ce539c6719c6318c650, 0xa4e939ce7394e75adab4ad6d4a4a949d294ad6729d675946959ce74a5694bda739ce73a527694e9394e5495a5294e5394a74aca52a5252956718ca3194651a4a5084251, 0xa4e93a4a55a4e76b5695a52b3b4a949ca949ced3a5a949ca74ad674a5694ad29494a929ce53a5693a4e54952b39d2729ce53a4a5294a739d2539ca3394651946518c630, 0xa4e93a4a55ad296b5695a52b3b4a949ca949ced3adab59ce95ada95ad694ad29494a929ce53a5694a4e749d6b3a52939d274a4a5294a739d2739ca5394a529c6518c631, 0xa4e93a4e749ce75ad694a52b3bcad4ace96a52929d67494674a5a74a5273ad2b5952b2ace9494e7294a338d2b2a4e92952539ce73952318ce339c6538ca3294a118c611, 0xa4e93a4e74ace75ad694a52b3aca949ce94a52d2ad6b494e74a5a74a5273ad27394a729ce54a5674a4a739d2b2a4e92952539c63194a739ce739c6538ca32942518c611, 0xa4e93a4e95a5295ad694a52b3aca95a5294a56b3a5a959ca95ad696ad273ad2749ce729d2759d2939ce54956939d6949ce759ca329ce52952529ce5294672a463184651, 0xa4e93a5275a5295ad694a52b3aceb49d294ad2b3a5a959ca95ad6b5ad273ad2939ce73a4e559d2939ce5495694a52749ce949ca519ce529525394e529ca51a46318c251, 0xa4e93ace749ca56b5695a52b3bceb5a4eb5a52b29d67394653ad674a5694ad2b59ceb3a52749d2729ca338ceb39d2729ce53a4e739ce5294e339ca339465194a318c630, 0xa4e93ace95a4e95ad674a4eb3b4e95a4eb5a56b39da949ca75b5a96b5273ace949ca939d2749d2929ce34952b49d693a52759ca529ca52952339ce339c6729c6318c650, 0xa4e93ad2949ca56b5695a52b3bced5ad2b6ad6b29d67394653ada95ad694ad2b59d2b3ad2959d2729ca338ceb3a52939d274a4e739d25294e339ca5394a529ca318c631, 0xa4e93ad295a5295ad694a52b3b4eb5a52b5ad6b3a5a959ca95b5ab6b5273ad2949ce93a52759d2939ce54956b4a5694a52959ca529ce52952539ce539ca72a46318c651, 0xa4e949527295295a5ad4adad59cab39d695b5a52a527694ab694e94ad694bde729d273ad29794a9494e749de329ca5494e95aca52a56529569184a5194a52aca5084252, 0xa4e949ce539ce76ad6b5adab4acab39ce95ad292a527494a949d273a56b4b5a9394e93ace759ce739ce73956729ca5294e73aca729d253952728c63294a319ca508c231]
def slackBlock9 : Array (Nat) := #[0xa4e949d2739d295a56b4adab4acad3a5296b5672a527594ab59d694ad293b5a9395293b4e9694a7394e7395a72a4a7395294a4a729d6328d2728c65294e32a4a308c232, 0xa4e949d274a56b5a56b4adab4a4ab39d295b5693ad6969ced6a56b5b5293b5a7294e73ace769ce949d2949de73a4e749d2b5a46519d253956928ca529ce52ac6508c252, 0xa4e949d2939d295a56b4adab4a4ab4a5695b5a72a527594ab59d295ad293b5a739d273ad29794a7394e7395a529ce7494e95a4a52a56328d2718ca5194a52aca3084252, 0xa4e94a4e55ad296ad295a5693b4ab39ca95a4ed3adab59ce95ada95ad293a52938ca92a4a53a5694a4e749d6b3a52939d2749c6518ca739d2739ca5394a529c2518c631, 0xa4e94a4e75a5295ad695a56b4aca949ce95a52b3a5a959ce95ad695ad294ad67394a92a4e749d293a4e749d6939d2739d274a465294e539d27294a3394a529c6508c631, 0xa4e94a52739d295a56b4adab4aceb49d2b5b5672a527594ab5a5294ad293b5a939ce94ad27694a7394e7395a739ce539ce94a4a72a52328d2728ca329ca51a4a308c251, 0xa4e94a56939d295a56b4adab4aced4a56b6bda72a527594ab5a56b5b5293b5a939d294b529794a7394e7395a73a4e749d2b5a4a72a56328d2728ca529ce52aca308c252, 0xa4e94ad294a4e76ad295a5693bced5ad2b6ad6b2a527394a73ada95ad293a52b59d2b3ad2959ce529ca528ceb3a52939d2749ce739d2328ca339ca5394a529ca118c631, 0xa4e94ad6b5ad6b5a5294a5693b4ed5ad6b6b5ab3adab69ceb6b5ed7bce72a52949d293ad2969d2949ce749dab4ad6b5a56b694a529d252952739ce739ce73ac6318c652, 0xa4e95952529d296a56d5adeb5a4ad29d296b5672ace7594eb595293ad6b4b5e9295293b4e969ca749ce939da52a465395294aca729d653952928465294e32a4a508c232, 0xa4eb3a4a7494a75b5a95ad2f4aca759ceb4a569295a749c675a4e54a5695bd6749ca939d675952929ce35956728d2529ca54aca53a4e529d65194a12942719ca5084650, 0xa4eb4a4a549ca76b5696ad6d4b4a949cab5a52b29d6739ca74a5253a56b5b569494ab3a52749d272a4e549529294e519ce53aca739ce539d252946139465194a508c630, 0xa4eb4a4a75a4eb5ad675ad2d4aca749cab5a56b39da94a4e96ad675b5294b5273946939d2749d292a52559d69395272a5275a46529ca539d65294a139c6729c6508c650, 0xa4eb4a4e75a52b5ad695ad6d4aca949ceb5ad6b3a5a95a4eb6ad695b5294b567394a93a52759d293a52759da939d273a5295a46529ce539d67294a339ca72a46508c651, 0xa4eb4ad2949ce95ad695ad6d4b4eb5a52d6b5a929d6749ca95ad695b5294b56949ceb4ad69694e729ce54956939d273a5295a4a73a52329525294a339ca72a4a308c651, 0xa4eb5a4a549ca96b5696adad5b4a949cab6ad6b29d6739ce95a5253ad6b5b5a9494ab3ad2959d272a4e749d69294e519d274aca739d2539d2729461394a529ca508c631, 0xa52739ce739ce56b5ad4a56b4acab4a5274a5292a56958c6749d2749da94b5a949d272a4e759d29494a53956729ce738ca53ace529d2729527294a518c6319ca5184231, 0xa52739d294a5695adad3a56b4a4ab4a5674ad693adab794ab6a56b6ad673b5a739d252a4e769d2b594e749de73a529594e95a4a319d2729569294e7194a52ac65184252, 0xa5273a4e75ad296b56b49d293b4ab4a4e749ced3adab59ce95ada95ad673a529494e719ca53a5694a4e749d6b3a52939d2749ca318ca739d2739ca5394a529c2518c631, 0xa5273a56b39d275adad3a56b4aced5ada95b5a72a56968c695a56b6ad673b5a94a5673ad29794e948ca5395a73a529594e95a4e52a56518d27294e7194a52aca3184252, 0xa5273ad294a4e56b56b49d293bced5ad2b6ad6b2a56948c653ada95ad673a52b59d2b3ad2959d273946328ceb3a52939d2749ce739d2518ca339ca5394a529ca118c631, 0xa52749ce53a4e57b56d5a5a94b4ad3a4e75a4eb2ad2948ca739d6739dab4adab495292aca74a52749ca7295292a4a728ce52ace729527394e73946528ca1194a518c211, 0xa52749d274ad696ad6d4a5a94acad3a5275ad2b3b56b694eb5a5ab5ad693ada9395272aca75a52959ce939da93ace9495294a4a51952739529394a7294e32a46518c232, 0xa5274a4e75ad276b56b59d694b4ab4a4e759ced3adab594e74ada95a5694a569494e91a4a73a5694a4a739d2b3a529395253a4a528ce739ce739ca538ca32946518c611]
def slackBlock10 : Array (Nat) := #[0xa5274a5693a5276ad6d4a5a94b4ef4ad696b5692ad2958ca94a5ab5ad693adab49d693b4e969ce7494a7295693ace9495294a4e729d6528ce7394a7294e32a4a318c232, 0xa527595252a5276ad6d5ade95acad2a5276b5292ace958ceb495693a56b4b5e9395293b4a969ce749ce929da72a46738d293aca729d653952928c65294e12a4a508c232, 0xa5293a4a749ca56bdab5a52d4b4a95a4e949d2b29da9494654a52549da95b56959ce929d2749d6939ca34952929527294a33ace539ce729d2529ca328c25194a5184630, 0xa5293a4e75a5295b56b4a52b4aca94a4e94a52b3a5ab59ca95ad695ad674ad67494e729ce749d6949ce549d6939d2939ce74a4a3294e729d2729ca52946529c65184631, 0xa5293a4e95a5295b5ab4a52d4aca95a5294a56b3a5eb69ca96ad696ad674b56749ce729d2759d6b49ce559da939d6949ce75a4a329ce729d6729ce5294672a465184651, 0xa5293ad2b49ce75b5ab4a52d4b4eb6ad6b5ada929da9594675ad696ad674b5695a5293a56969529394a34956939d6949ce75a4e53a5251952529ce5294672a4a3184651, 0xa52949d2739d295ad6d4adab5a4ab3a5295b5672a529594ab59d294ad694b5e7395273ace9694e7494e739da529ca7394e94aca529d652952918c65194a32a4a5084232, 0xa52949d2939d295adad4adad5a4ab4a5695b5a72a569694ab69d295ad694bde739d273ad29794e9494e749de529ce7494e95aca52a5652956918ca5194a52aca5084252, 0xa5294a4a55ace76b56b5a56b4b4ab4a4a959ced3adab49ce74ada74a5694ad69494e92a4e73a5694a4e749d2b3a52929d253a4a5294e739d2739ca5394a52946518c631, 0xa5294a4e55ad296b52b5a5694b4ab3a4a95a4ed3ad6b49ce94ada94ad694a56948ce92a4a73a5674a4e739d2b3a4e929d273a4a528ce739ce739c65394a32946518c611, 0xa5294a4e75ad296b56b5a56b4b4ab4a4e95a52d3adab59ce95ada95ad694ad69494e92a4e74a5694a4e749d6b3a52939d274a4a5294e739d2739ca5394a529c6518c631, 0xa5294a4e94a4e76b56b5a56b4b4ab5ad295a56b2a569494a74a5675a5694ad6959d292a52959d2739ca53952929d29394e54a4e539d25294e529ca528c6529ca3184631, 0xa5294a5274a4e76b56b5a56b4b4ed4a5295ad2b2a569494a74a5694a5694ad6b49d293ace759d2739ca5395293a4e7394e73a4e729d25294e5394a5294a319ca318c231, 0xa5294a5294a5295ad6b4a56b4acab4a5295ad692a569594a95b5ed7bd273ad67394e72a4e7594e7394a53956b4ad6b5a56b69c63194e318ce539ce739ce73ac2118c652, 0xa5294a5294a5295ad6b4a56b4bcaf4b5297ad692a569594a95a5e95ad273ad6b5956b2b4eb594e7394a53956b2aceb3956749ce73956318ce539c6738ce339ca118c612, 0xa5294a5294a5297bd6b6a56b4bcab4a5295ad6d2a569594a95a5695adab5ad6b594eb2a4e75a5673a4a53956b29ce7394e74ace7394e739ce539c6338c6319ca518c610, 0xa5294a5294b5295ad6b4a56b4acab4a5295ad6d2b56d595295a5e95ad273ad67394e72a4e75a5675a4a93a56b2aceb3956749c63194e739ce939c6738ce339c2518c612, 0xa5294a5295ad6b5ad6b4a56b4acab4a5295ad6b3adab69ceb6b5ed7bd273ad67394e72a4e759d2949ce749dab4ad6b5a56b69c63194e52952739ce739ce73ac2318c652, 0xa5294a5295ad6b5ad6b4a56b4acab4a5295ad6b3aded79ceb7adab7b5273ad67394e72a4e759d6b59ce75a5e93a56b59d2969c63194e729d6929ce7294a73ac25184652, 0xa5294a5295ad6d5ad6b4a56b4acab4a5295ad6b3adab6a52d7adab6bd273ad67394e72a4e759d294a5295a5e93a5294a56b69c63194e539d69294a539ce73ac2508c652, 0xa5294a5295adab5ad6b4a56b4acab4a5295ad6b4b5ab79ced6adad6b5273ad67394e72a4e75a52b59d2949de94ad2959d2b59c63194e739569394e729ce52ac2518c252, 0xa5294a5295b56b5ad6b4a56b4acab4a5295ad6d3b5ad69d2b6adeb6b5273ad67394e72a4e75a5695a4e94a5ab3ad2b49d6959c63194e739d2939ca7394e53a42518c632, 0xa5294a5296a5295ad6b4a56b4acab4a5295ad6d4a5e95a4a95b5695ad273ad67394e72a4e75a56b3a5255956b49d673a4e749c63194e739d6539ce339c6719c2518c650, 0xa5294a5296ad6b5ad6b4a56b4acab4a5295ad6d4adeb6a4eb6b5ab6b5273ad67394e72a4e75a56b4a52759dab4a5694a52959c63194e739d6739ce539ca72a42518c651]
def slackBlock11 : Array (Nat) := #[0xa5294a52b5ad6b5ad6b4a56b4acab5ad695adab3adab69ceb6adab7b5273ad6749d272a52969d2949ce749da93a56b59d2969ca329d252952729ce7294a73ac63184652, 0xa5294ace74a4a56b56b5a56b4bced5aceb6a52b2a569394a53ada74a5694ad6b59d2b3ad2949d2739ca5394eb3a52929d253a4e739d25294e539ca5394a5294a318c631, 0xa5294ace74a4e76b56b5a56b4bceb5a4eb5a52b2a569494a74ad674a5694ad6b59ceb3a52749d2739ca53952b39d2729ce53a4e739ce5294e539ca339465194a318c630, 0xa5294ad294a4e76b56b5a56b4bced5ad2b6ad6b2a569494a74ada95ad694ad6b59d2b3ad2959d2739ca53952b3a52939d274a4e739d25294e539ca5394a529ca318c631, 0xa5294ad6b4a5295ad6b4a56b4b4ed5ad6b6b5a92a569594a95b5ed7bd273ad6949d293ad29694e7394a53956b4ad6b5a56b69ca529d2318ce539ce739ce73ac6118c652, 0xa5294ad6b4a5295ad6b4a56b4b4ed5ad6d7bde92a569594a95adab6bd273ad6949d2b4b56b794e7394a5395693a5294a56b69ca73a56318ce5294a539ce73aca108c652, 0xa5294ad6b4a5295ad6b4a56b4bcef5b56b7b5a92a569594a95adeb6b5273ad6b59d6b3b52b694e7394a53956b3ad2b49d6959ce739d6318ce539ca7394e53a4a118c632, 0xa5294ad6d4a5295ad6b4a56b4b4ed6b5ab6b5e92a569594a95adab7b5273ad695a5693ad6b794e7394a5395693a56b59d2969ce53a56318ce529ce7294a73aca1184652, 0xa5294adab4a5295ad6b4a56b4b52f5adab6bda92a569594a95adad6b5273ad6b4a5694b529794e7394a5395694ad2959d2b59ce72a56318ce5394e729ce52aca118c252, 0xa5294b5294a5295ad6b4a56b4bd2b6a52d5ad692a569594a95b5695ad273ad6b5a4eb4a567594e7394a53956b49d673a4e749ce73a4e318ce539ce339c6719ca118c650, 0xa5294b56b4a5295ad6b4a56b4bd2d6ad6d6b5a92a569594a95b5ab6b5273ad6b5a52b4ad69694e7394a53956b4a5694a52959ce73a52318ce539ce539ca72a4a118c651, 0xa52959d273a5296ad6d5adeb5acad3a5296b5692ad29594eb59d694ad6b4b5e9395293b4e969ce749ce939da72a4a7395294aca729d653952928c65294e32a4a508c232, 0xa52b4a4a749ce95b5ab5ad6f5aca759ceb4a56929da959ca96a4e54a5695bda749ca939d675952939ce559da728d2529ca54aca53a4e529d67194a12942719ca5084650, 0xa52b4a4e949ce95b5ab5ad6f5aca95a52b5ada929da959ca96a5275ad695bda749ce93a5696952939ce559da72952739ce75aca53a52529d67194a3294672a4a5084651, 0xa52b5a4a54a4a76b56b6adad5b4ab4a4ab6a52b2a56939ce74a5653a56b5b5a9494eb3ad2949d273a4e749d2929ce719d253aca739d2539d2729463394a5294a508c631, 0xa52b5a4e74a4e96b56b6adad5b4ab4a4eb6ad6b2a56949ce95a5674ad6b5b5a9494eb3ad2959d273a4e749d6929ce729d274aca739d2539d2729463394a529ca508c631, 0xa56749d293a5276b5af4a5ab5acad4ad675ad692ad6b68ca959d695a5a94b5e949d672ace969d29594a739da72a4e948ce74ace529d6729529294a718ca32a4a5184232, 0xa5694a4a74a4a56bdad5a56d5b4ab5ace959d2b2a5ab494a54a56549da95b5a959d292a52949d6949ca549d2929d29294e33ace539d2729d2729ca528c65294a5184631, 0xa5694a4e94a4e76bdad5a56d5b4ab5ad295a56b2a5ab594a75a5675a5a95b5a959d292a52959d6949ca549d6929d29394e54ace539d2729d2729ca528c6529ca5184631, 0xa5694a52b4a5295b52d4a5695b4ad5b5696ada92a52b494a94a5a96ad674a5a959d692ad2b69525494a529d292a52b495275a4e539d65194a729ca728ca53a4a3184632, 0xa5695a5294ad296b56d5a5ab5bcaf4b5297ad6b2ad6b594e95a5e95ad694adab5956b2b4eb59d2749ca739d6b2aceb395674a4e739565294e739c6738ce339ca318c612, 0xa5695a5294ad297b56f5a5eb5b4af4ad296ad6b2b56b594e95a5a95adab4adeb495692b4e95a52759ca939d692ace9395274ace729567394e93946728ce329ca518c212, 0xa5695a5294ad297bd6d6a5ab5bcad4ad296ad6d2ad6b594e95a5a95adab5adab5952b2ace95a5674a4a739d6b2a4e9395274ace73952739ce739c6538ca329ca518c611, 0xa5695a5294b5296b56d5a5ab5b4ad4ad296ad6d2b56d595295a5e95ad694ada9495292ace95a5675a4a93a56b2aceb395674a4a52952739ce939c6738ce339c6518c612]
def slackBlock12 : Array (Nat) := #[0xa5696a5294ad296b56d6a5eb6b4ad4ad297ad6b2ad6b595295a5a95ad6b5ade94952b2b4eb59d274a4a93a5692a4e9395674aca73956539ce92946538ce339ca508c612, 0xa56b5ad2b6b5ad5b56b5a56d5b4ab5ad2b6adad4b5ed7a52d7b5ed7bd274ad67494e92a5295a56b5a5295a5eb4ad6b5a56b69c63294e739d6939ce739ce73ac2518c652, 0xa5a95a5294ad296bd6f5a5ab6b4ad4b5296ad6b2ad6d594e95a5a95ada95ade9595692aceb59d6759ca73a5692a4eb395274ace53956729ce929c6728ca339ca5184612, 0xaca729d255a5696a5ab3ad692a4eb395273aceb4ada969cab5ad6b5ad692b56929ce53a4a35a52b49d27495a94a52749ce94a4a509ce739567394e529ca51a46518c251, 0xaca92a4e559d276ada94ad2b2ace9494e93a4eb4a5a759c694ad294a5693b52939ca739ce34a52b39d2548d6949d2539ca73a4a519ca739565394e329c6509c6518c250, 0xaca92a4e55a5696ada94ad2b2ace9494e93a4eb4ada969cab5ad6b5ad693b52939ca739ce34a52b49d27495a94a52749ce94a4a519ca739567394e529ca51a46518c251, 0xaca92a52559d676adab4ad6b2aceb495293aceb4ada769c6b4ad2b4a5693b56939ce73a4e35a52b49d2748da94a52549ca93a4a519ce739567394e529ca50a46518c251, 0xaca92ad27494e56ada94ad2b2b52b59d2b4ad2939d65494273ad294a5693b52b4a4e94a52559ce9294e33852949d2539ca73a4e72a4e528d23394e329c6509ca318c250, 0xacab3a4e5494e76ada95b56d3ace9494eb4ad2939d6549c694a4e73a56b4bd6939ca94a52559ce929d2548d67394e329ca73aca72a4e53956528ca129c6509ca508c250, 0xacab3a525495276adab5b5ad3aceb4952b4b5293a56559c6b4a4e93a56b4bda939ce94ad2569ce939d2748da739ce339ca93aca72a5253956728ca329ca50a4a508c251, 0xacab49d25395296a5ab5b5ad4a4eb3952b5b5673a52559cab59ce93ad6b4bda929ce94ad2769ca939d27495a539ca339ce94aca72a52539567284a329ca51a4a508c251, 0xacab4a4e5494e96ada95b5ad4ace9494eb5b56939d6549cab5a4e73ad6b4bda939ca94ad2769ce929d27495a7394e329ce94aca72a5253956728ca129ca51a4a508c251, 0xacab4a52549d296ada95b5ad3aceb494eb5b5293a56549cab4a5293ad6b4bd6939ca94ad2559ce929d2748d6739ce329ce93aca72a4e53956528ca129ca509ca508c250, 0xace72a5275a5696adab3a5292aceb49d273a4eb4ada969cab5ad6b5ad672ad2939ce529ca34a52b49d27495a94a52749ce949ca3094a739567394e529ca51a42518c251, 0xace739ce759d276a5a93ad293a4e939ce74a52b4a5a759c694ad294a5692b52929ca539ca54a52b39d2548d6949d2539ca73a4a509ca739565394e329c6509c6518c250, 0xace73ad2739ce76a5a93ad293b52b59d2b4ad2739d2748c674ad294a5692b52b4a4e94a52559ca928ce328d2949d2539ca73a4e72a4e528523394e329c6509ca318c250, 0xace92a4e7494e56b5eb4ad2d3ace959d293a52939da7594274a4e749da94bd694a4e739d2559d2b394e348d6739525394653ace52a4e729565294e31942509ca5184250, 0xace92a527495256b5ed4ad6d3aceb59d693ad293a5a7694294a4e949da94bda94a5273a52569d2b494e548da739d25494673ace52a52729567294e5194650a4a5184251, 0xace93a4e549ce57b5ab5ad6b3b4eb49ce94a4eb3a567494673a52739dab4b56b49ce93a4e54a52939ce538d2939ce5294a52ace729ce739525394a329463094a518c230, 0xace93a52549d257b5ad5adab3b4ed49d294aceb3ad67594693a52939dab4b5ab49d293ace55a52949ce738d693a4e5394a72ace729d2739527394a5294a309ca518c231, 0xace93a5275a5696adab4ad6b3aceb49d294ad2b4ada969cab5ad6b5ad693b56939ce73a4e55a52b49d27495a94a52749ce94a4a519ce739567394e529ca51a46518c251, 0xace93ad6949d276adab4ad6b3b52d5a56b5b5693a567594694ad6b5ad693b56b4a5294ad2769ce9394e538d694a52749ce94a4e72a52528d25394e529ca51a4a318c251, 0xaceb39ce739ce76a5a95b56d3a4e939ceb4ad2739d2749c6949d274a56b4bd6929ca94a52559ca929d2548d65394a529ca73aca72a4e539565284a129c6509ca508c250, 0xaceb4a4e549d296adab5b5ad4ace9494eb4ad293a56759cab5a4e73a56b4bda939ca94a52559ce939d27495a7394e329ca73aca72a4e53956728ca129c6509ca508c250]
def slackBlock13 : Array (Nat) := #[0xaceb4a52749d296adab5b5ad4aceb49d2b5b5693a56759cab5a5294ad6b4bda939ce94ad2769ce939d27495a739ce539ce94aca72a5253956728ca329ca51a4a508c251, 0xad293a52949d276b5ed4ad6d4aceb5a5694ad693a5a9694695a5295a5a94bda94a5273a52769d2b494e5495a739d27494a74ace52a52729567294e5194651a4a5184251, 0xad294a4e54a4e57b5ad5adab4b4ed4a4e95a4eb3ad69494a73a56739dab4b5ab49d293ace74a52949ce7395293a4e7294e52ace729d2739527394a5294a3194a518c231, 0xad294a5274a5277b5ad5adab4b4ed4a5295ad2b3ad69594a94a5694a5ab4b5ab49d293ace75a52949ce7395693a4e7394e73ace729d2739527394a5294a319ca518c231, 0xad2b4ad295a5296bdeb5ad6f4b4eb6a52b5ad6b3a5e959ca95ad695ada95bd695a4e93a56759d6b39ce55956939d6739ce74ace53a4e729d6529ce32946719ca5184650, 0xad2b4ad295a5297bdab6ad6d4bceb5a52b5ad6d3a5a959ca95ad695adab5b56b59ceb3a5275a5693a4e54956b39d2739ce74ace739ce739d2539ca33946519ca518c630, 0xad2b4ad296a5296b5ab5ad6d4b4eb5a52b5ad6d4a5e95a4a95b5695ad694b56949ce93a5275a56b3a5255956b49d673a4e74a4a529ce739d6539ce339c6719c6518c650, 0xad2b4ad6b6b5ad5adab4ad6d4aceb5a56b5b5ad4b5ed7a52d7b5ed7bd273b56739ce73a5276a56b5a5295a5eb4ad6b5a56b69c6319ce739d6939ce739ce73ac2518c652, 0xad2b4b5295a5296b5ab5ad6d4bd2b6a52d5ad6b3a5a959ca95b5695ad694b56b5a4eb4a56759d2939ce54956b49d673a4e74a4e73a4e52952539ce339c6719ca318c650, 0xad2b5ad696b5ad6ad6b5adab4b4ed4a52b6b56d4b5ed7a52d7b5ed7bd293ad69394e93ace75a56b5a5295a5eb4ad6b5a56b69c65194e739d6939ce739ce73ac2518c652, 0xad2b5b5ad5ad6b6ad6b5adab4bd2f6b5ad7bdeb3ad6959ceb5b5ed7bd293ad6b5a56b4b56b79ce739ce73956b4ad6b5a56b69ce73a56328ce539ce739ce73aca118c652, 0xad2d4ad295a5296b5ab6b56f4b4eb5a52d5ad6b3a5a95a4a95ad695ad6b5bd6949ceb4a56759d293a5255956939d273a4e74aca73a4e539d65294a339c6719ca508c650, 0xad694ad6b6b5ad6b5ad4a56b4b4ed5ad695ad6d4b5ed7a52d7b5ed7bd673ad6949d272a4e75a56b5a5295a5eb4ad6b5a56b69ca3194e739d6939ce739ce73ac2518c652, 0xad6b4ad295a5296bdad5ad6d5b4eb5ad2b5ad6b3a5ab59ca95ad695ada95b5a959d293a52959d6949ce549d6939d2939ce74ace539d2729d2729ca52946529ca5184631, 0xad6b5ace55ace77bdad6adad5bced5acab6a4ed3adab39ce73ada73a5ab5b5ab59d2b3ad293a5694a4e749ceb3a52919d252ace739d2739d2739ca5394a528ca518c631, 0xad6b5ad275ad297bdad6adad5bced5aceb6ad2d3adab49ce94ada94adab5b5ab59d2b3ad294a5694a4e749d2b3a52929d273ace739d2739d2739ca5394a5294a518c631, 0xad6b5ad6d5ad6b6b5ad5adad5b4ed6b5ab6b5eb3adab69ceb6adab7b5694b5a95a5693ad6b79d2949ce749da93a56b59d296a4e53a5652952729ce7294a73aca3184652, 0xad6b5adab5ad6b6b5ad5adad5b52f5adab6bdab3adab69ceb6adad6b5694b5ab4a5694b52979d2949ce749da94ad2959d2b5a4e72a56529527394e729ce52aca318c252, 0xad6b6ad6b5ad6b6b5ad6aded6b4ed5ad6b7b5ab3adab69d2b6adab6b56b5b5e949d2b3b52b69d294a4e94a5a93a52949d695aca739d6539d29294a5394e53a4a508c632, 0xadab5ad6b5ad6b6bdaf5adad6b4ed5b56b6b5ab3adad69ceb6adab6b5a95b5e959d693ad2b69d6959ce74a5a93a52b49d295ace539d6729d2929ca7294a53a4a5184632, 0xadab6ad695b56b7bd6f6adeb6bcef4b52b7b56d3b56d59d2b5adeb5b5ab5adeb5956b3b4eb5a5675a4e93a56b3aceb39d694ace73956739ce939c67394e339ca518c612, 0xb52b4ad295a5297b5eb5b56d4b52b5a52b5ad6b4a5a959ca95ad695adab4bd6b4a4e94a5275a52b39d254956949d2739ce74ace72a4e739565394e329c6519ca518c250, 0xb52d5b5696ad6b7bdeb6b5af4bd2d6a52d6b56d4ade95a4eb5b5ab5b5ab5bd6b5a4eb4ad675a56b3a5275956b4a5673a5294ace73a4e739d6539ce339ca719ca518c650, 0xb56d4b56b6ad697bded6b56f4bd2d6ad6d5ad6d4adeb6a4a95b5ab6adab5bd6b5a52b4a5675a56b4a5255956b4a5694a4e74ace73a4e739d6539ce539c6719ca518c650]
def slackBlock14 : Array (Nat) := #[0xb56d5b5296ad6b7bded6b5af5bd2b6a52d5ad6d4adeb6a4eb6b5695adab5bdab5a4eb4a5675a56b4a52759dab49d673a4e74ace73a4e739d6739ce339c6719ca518c650, 0xb56d5b52b6ad2b7bdeb6b56f5bd2b6ad2d6adad4a5eb5a4e96b5a96b5ab5bd6b5a4eb4a5695a56b3a52559d6b49d693a5275ace73a4e739d6539ce339c6729ca518c650]
def slackBlocks : Array (Array (Nat)) := #[slackBlock0, slackBlock1, slackBlock2, slackBlock3, slackBlock4, slackBlock5, slackBlock6, slackBlock7, slackBlock8, slackBlock9, slackBlock10, slackBlock11, slackBlock12, slackBlock13, slackBlock14]
def slack (i : Nat) : Nat := ((slackBlocks.getD (i / 24) #[]).getD (i % 24) 0)
noncomputable def rowBlock0 : Array (Arg) := #[(0,13,10,0,slack 38,[w40, w6, w5, w4, w3, w2, w52, w0]), (0,13,10,0,slack 50,[w40, w10, w6, w5, w4, w3, w1, w0, w71]), (0,13,10,0,slack 59,[w6, w23, w256, w4, w16, w3, w2, w1, w0]), (0,13,10,0,slack 60,[w10, w6, w78, w5, w4, w16, w3, w1, w0]), (0,13,10,0,slack 65,[w40, w14, w6, w5, w4, w2, w1, w0, w111]), (0,13,10,0,slack 89,[w6, w23, w256, w4, w3, w12, w2, w1, w0]), (0,13,10,0,slack 90,[w14, w6, w119, w5, w4, w12, w2, w1, w0]), (0,13,10,0,slack 91,[w8, w6, w58, w5, w4, w3, w12, w2, w0]), (0,13,10,0,slack 107,[w40, w79, w6, w5, w4, w3, w1, w0]), (0,13,10,0,slack 118,[w14, w33, w6, w5, w4, w2, w114, w1, w0]), (0,13,10,0,slack 121,[w40, w74, w6, w5, w4, w3, w1, w0]), (0,13,10,0,slack 126,[w33, w6, w5, w56, w4, w3, w2, w0]), (0,13,10,0,slack 137,[w40, w6, w5, w4, w2, w114, w1, w0]), (0,13,10,0,slack 146,[w40, w6, w5, w3, w2, w171, w1, w0]), (0,13,10,0,slack 152,[w6, w58, w5, w4, w3, w12, w2, w0]), (0,13,10,0,slack 154,[w6, w5, w56, w4, w3, w12, w2, w0]), (0,13,10,0,slack 173,[w10, w6, w5, w4, w16, w3, w1, w0, w71]), (0,13,10,0,slack 175,[w6, w78, w5, w4, w16, w3, w1, w0]), (0,13,10,0,slack 176,[w6, w23, w4, w16, w3, w2, w1, w0, w249]), (0,13,10,0,slack 178,[w40, w6, w5, w3, w2, w1, w0, w168]), (0,13,10,0,slack 179,[w33, w6, w5, w174, w3, w2, w1, w0]), (0,13,10,0,slack 181,[w6, w176, w5, w16, w3, w2, w1, w0]), (0,13,10,0,slack 192,[w33, w6, w5, w117, w4, w2, w1, w0]), (0,13,10,0,slack 202,[w40, w6, w5, w4, w2, w1, w0, w111])]
noncomputable def rowBlock1 : Array (Arg) := #[(0,13,10,0,slack 208,[w33, w6, w255, w4, w3, w2, w1, w0]), (0,13,10,0,slack 209,[w33, w6, w251, w4, w3, w2, w1, w0]), (0,13,10,0,slack 211,[w40, w6, w5, w4, w3, w2, w0, w50]), (0,13,10,0,slack 216,[w6, w253, w4, w16, w3, w2, w1, w0]), (0,13,10,0,slack 216,[w77, w6, w5, w4, w16, w3, w1, w0]), (0,13,10,0,slack 218,[w6, w255, w4, w16, w3, w2, w1, w0]), (0,13,10,0,slack 219,[w6, w176, w5, w3, w12, w2, w1, w0]), (0,13,10,0,slack 220,[w115, w33, w6, w5, w4, w2, w1, w0]), (0,13,10,0,slack 221,[w47, w6, w5, w4, w16, w3, w2, w1]), (0,13,10,0,slack 223,[w6, w5, w174, w3, w12, w2, w1, w0]), (0,13,10,0,slack 224,[w6, w532, w5, w3, w2, w1, w0]), (0,13,10,0,slack 228,[w37, w6, w5, w4, w3, w2, w0, w50]), (0,13,10,0,slack 234,[w6, w119, w5, w4, w12, w2, w1, w0]), (0,13,10,0,slack 236,[w6, w5, w117, w4, w12, w2, w1, w0]), (0,13,10,0,slack 239,[w33, w6, w5, w4, w2, w114, w1, w0]), (0,13,10,0,slack 243,[w75, w33, w6, w5, w4, w3, w1, w0]), (0,13,10,0,slack 246,[w75, w6, w5, w4, w16, w3, w1, w0]), (0,13,10,0,slack 249,[w33, w6, w5, w3, w2, w171, w1, w0]), (0,13,10,0,slack 251,[w6, w255, w4, w3, w12, w2, w1, w0]), (0,13,10,0,slack 252,[w6, w251, w4, w3, w12, w2, w1, w0]), (0,13,10,0,slack 252,[w57, w6, w5, w4, w3, w12, w2, w0]), (0,13,10,0,slack 264,[w40, w6, w175, w3, w2, w1, w0]), (0,13,10,0,slack 266,[w6, w250, w4, w3, w12, w2, w1, w0]), (0,13,10,0,slack 276,[w6, w22, w4, w3, w2, w1, w0, w249])]
noncomputable def rowBlock2 : Array (Arg) := #[(0,13,10,0,slack 300,[w6, w5, w16, w3, w2, w1, w0, w168]), (0,13,10,0,slack 301,[w6, w119, w5, w4, w2, w9, w1, w0]), (0,13,10,0,slack 311,[w6, w4, w16, w3, w2, w1, w0, w249]), (0,13,10,0,slack 317,[w43, w6, w5, w4, w3, w12, w1]), (0,13,10,0,slack 325,[w6, w172, w5, w3, w12, w1, w0]), (0,13,10,0,slack 326,[w6, w5, w3, w12, w184, w2, w1, w0]), (0,13,10,0,slack 327,[w6, w5, w3, w184, w2, w1, w0]), (0,13,11,0,slack 257,[w6, w23, w256, w4, w3, w2, w1, w0]), (0,13,11,0,slack 258,[w6, w18, w176, w5, w3, w2, w1, w0]), (0,13,11,0,slack 259,[w14, w6, w119, w5, w4, w2, w1, w0]), (0,13,11,0,slack 260,[w8, w6, w58, w5, w4, w3, w2, w0]), (0,13,11,0,slack 261,[w10, w6, w78, w5, w4, w3, w1, w0]), (0,13,11,0,slack 263,[w7, w6, w48, w5, w4, w3, w2, w1]), (0,13,11,0,slack 268,[w5, w4, w31, w378, w3, w2, w1, w0]), (0,13,11,0,slack 269,[w14, w6, w5, w117, w4, w2, w1, w0]), (0,13,11,0,slack 270,[w10, w6, w5, w76, w4, w3, w1, w0]), (0,13,11,0,slack 271,[w6, w18, w5, w174, w3, w2, w1, w0]), (0,13,11,0,slack 272,[w6, w251, w23, w4, w3, w2, w1, w0]), (0,13,11,0,slack 272,[w8, w6, w5, w56, w4, w3, w2, w0]), (0,13,11,0,slack 274,[w7, w6, w5, w46, w4, w3, w2, w1]), (0,13,11,0,slack 284,[w6, w23, w4, w3, w2, w1, w0, w252]), (0,13,11,0,slack 285,[w8, w6, w5, w4, w3, w2, w52, w0]), (0,13,11,0,slack 286,[w7, w6, w5, w4, w3, w2, w42, w1]), (0,13,11,0,slack 287,[w5, w4, w31, w3, w2, w374, w1, w0])]
noncomputable def rowBlock3 : Array (Arg) := #[(0,13,11,0,slack 288,[w14, w6, w5, w4, w2, w114, w1, w0]), (0,13,11,0,slack 288,[w74, w10, w6, w5, w4, w3, w1, w0]), (0,13,11,0,slack 289,[w6, w58, w5, w4, w3, w2, w0]), (0,13,11,0,slack 290,[w6, w18, w5, w3, w2, w171, w1, w0]), (0,13,11,0,slack 316,[w6, w18, w5, w3, w2, w1, w0, w168]), (0,13,11,0,slack 317,[w10, w6, w5, w4, w3, w1, w0, w71]), (0,13,11,0,slack 318,[w5, w4, w31, w3, w2, w1, w0, w371]), (0,13,11,0,slack 319,[w6, w78, w5, w4, w3, w1, w0]), (0,13,11,0,slack 320,[w6, w23, w4, w3, w2, w1, w0, w249]), (0,13,11,0,slack 321,[w6, w176, w5, w3, w2, w1, w0]), (0,13,11,0,slack 322,[w6, w5, w174, w3, w2, w1, w0]), (0,13,11,0,slack 323,[w14, w6, w5, w4, w2, w1, w0, w111]), (0,13,11,0,slack 324,[w6, w119, w5, w4, w2, w1, w0]), (0,13,11,0,slack 328,[w6, w255, w4, w3, w2, w1, w0]), (0,13,11,0,slack 329,[w6, w251, w4, w3, w2, w1, w0]), (0,13,11,0,slack 330,[w74, w6, w5, w4, w3, w1, w0]), (0,13,11,0,slack 331,[w75, w6, w5, w4, w3, w1, w0]), (0,13,11,0,slack 332,[w6, w5, w3, w2, w171, w1, w0]), (0,13,11,0,slack 333,[w8, w6, w5, w4, w3, w2, w0, w50]), (0,13,11,0,slack 334,[w6, w5, w3, w2, w1, w0, w168]), (0,13,11,0,slack 335,[w6, w5, w4, w2, w1, w0, w111]), (0,13,11,0,slack 336,[w6, w4, w3, w2, w1, w0, w249]), (0,13,11,0,slack 337,[w6, w5, w4, w3, w2, w0, w50]), (0,13,11,1,slack 2,[w40, w6, w5, w4, w3, w2, w472, w1, w0])]
noncomputable def rowBlock4 : Array (Arg) := #[(0,13,11,1,slack 4,[w40, w6, w5, w4, w3, w2, w1, w0, w430]), (0,13,11,1,slack 11,[w346, w40, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 12,[w346, w37, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 15,[w360, w40, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 20,[w332, w40, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 30,[w240, w37, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 34,[w332, w36, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 35,[w332, w6, w28, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 46,[w311, w40, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 48,[w33, w6, w5, w4, w3, w2, w1, w0, w431]), (0,13,11,1,slack 52,[w33, w6, w5, w432, w4, w3, w2, w1, w0]), (0,13,11,1,slack 54,[w296, w40, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 72,[w149, w37, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 73,[w6, w147, w29, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 74,[w136, w37, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 92,[w6, w5, w4, w3, w12, w2, w1, w0, w94]), (0,13,11,1,slack 94,[w6, w5, w4, w3, w2, w1, w0, w148]), (0,13,11,1,slack 95,[w6, w5, w331, w4, w3, w2, w1, w0]), (0,13,11,1,slack 96,[w6, w5, w4, w3, w2, w472, w1, w0]), (0,13,11,1,slack 97,[w6, w5, w4, w3, w2, w1, w0, w105]), (0,13,11,1,slack 98,[w325, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 99,[w6, w5, w4, w3, w2, w1, w0, w431]), (0,13,11,1,slack 100,[w6, w5, w4, w3, w2, w1, w0, w426]), (0,13,11,1,slack 101,[w6, w5, w4, w3, w2, w1, w0, w94])]
noncomputable def rowBlock5 : Array (Arg) := #[(0,13,11,1,slack 103,[w6, w5, w4, w3, w2, w1, w0, w210]), (0,13,11,1,slack 105,[w6, w5, w295, w4, w3, w2, w1, w0]), (0,13,11,1,slack 106,[w6, w466, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 108,[w6, w423, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 109,[w6, w5, w4, w3, w12, w2, w92, w1, w0]), (0,13,11,1,slack 110,[w6, w5, w4, w3, w2, w92, w1, w0]), (0,13,11,1,slack 111,[w6, w5, w4, w3, w2, w1, w0, w291]), (0,13,11,1,slack 112,[w6, w5, w432, w4, w3, w2, w1, w0]), (0,13,11,1,slack 113,[w288, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 114,[w6, w5, w4, w3, w2, w1, w0, w430]), (0,13,11,1,slack 115,[w6, w5, w4, w3, w2, w1, w0, w196]), (0,13,11,1,slack 119,[w6, w5, w4, w3, w2, w1, w0, w160]), (0,13,11,1,slack 122,[w6, w5, w4, w3, w2, w1, w0, w488]), (0,13,11,1,slack 124,[w6, w5, w4, w3, w2, w1, w0, w135]), (0,13,11,1,slack 129,[w346, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 130,[w6, w5, w4, w286, w3, w2, w1, w0]), (0,13,11,1,slack 131,[w6, w5, w4, w3, w2, w1, w0, w487]), (0,13,11,1,slack 132,[w6, w5, w4, w3, w2, w1, w0, w343]), (0,13,11,1,slack 136,[w106, w36, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 140,[w360, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 143,[w95, w36, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 144,[w6, w5, w4, w3, w420, w2, w1, w0]), (0,13,11,1,slack 147,[w332, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 148,[w6, w5, w4, w3, w285, w2, w1, w0])]
noncomputable def rowBlock6 : Array (Arg) := #[(0,13,11,1,slack 149,[w6, w93, w28, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 151,[w240, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 153,[w6, w238, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 156,[w161, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 157,[w6, w159, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 158,[w6, w5, w4, w3, w2, w1, w0, w504]), (0,13,11,1,slack 159,[w226, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 160,[w6, w28, w5, w3, w2, w1, w0, w330]), (0,13,11,1,slack 161,[w6, w224, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 162,[w6, w5, w4, w3, w2, w1, w0, w236]), (0,13,11,1,slack 163,[w6, w5, w157, w4, w3, w2, w1, w0]), (0,13,11,1,slack 164,[w311, w34, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 169,[w149, w34, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 171,[w296, w33, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 172,[w296, w6, w25, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 180,[w149, w6, w5, w4, w16, w3, w2, w1, w0]), (0,13,11,1,slack 182,[w6, w147, w5, w4, w16, w3, w2, w1, w0]), (0,13,11,1,slack 184,[w136, w33, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 186,[w6, w134, w25, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 187,[w136, w6, w5, w4, w15, w3, w2, w1, w0]), (0,13,11,1,slack 188,[w213, w34, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 189,[w106, w34, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 194,[w6, w5, w4, w3, w2, w1, w0, w67]), (0,13,11,1,slack 195,[w6, w5, w4, w3, w2, w455, w1, w0])]
noncomputable def rowBlock7 : Array (Arg) := #[(0,13,11,1,slack 197,[w311, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 198,[w6, w5, w4, w3, w2, w1, w0, w65]), (0,13,11,1,slack 200,[w199, w33, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 205,[w95, w33, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 206,[w6, w5, w4, w3, w302, w2, w1, w0]), (0,13,11,1,slack 207,[w6, w5, w4, w3, w2, w1, w438, w0]), (0,13,11,1,slack 212,[w6, w93, w25, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 213,[w296, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 214,[w6, w5, w145, w4, w16, w3, w2, w1, w0]), (0,13,11,1,slack 217,[w149, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 222,[w6, w147, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 225,[w6, w5, w4, w101, w16, w3, w2, w1, w0]), (0,13,11,1,slack 229,[w136, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 230,[w6, w134, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 231,[w6, w5, w4, w90, w15, w3, w2, w1, w0]), (0,13,11,1,slack 233,[w213, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 235,[w6, w211, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 238,[w106, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 240,[w6, w104, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 241,[w6, w5, w4, w101, w3, w13, w2, w1, w0]), (0,13,11,1,slack 244,[w199, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 245,[w6, w197, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 247,[w6, w5, w145, w4, w3, w2, w1, w0]), (0,13,11,1,slack 248,[w95, w6, w5, w4, w3, w12, w2, w1, w0])]
noncomputable def rowBlock8 : Array (Arg) := #[(0,13,11,1,slack 250,[w95, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 256,[w6, w5, w4, w3, w2, w1, w438]), (0,13,11,1,slack 256,[w6, w5, w4, w3, w2, w455, w0]), (0,13,11,1,slack 256,[w6, w5, w4, w464, w2, w1, w0]), (0,13,11,1,slack 256,[w6, w5, w465, w3, w2, w1, w0]), (0,13,11,1,slack 256,[w6, w466, w4, w3, w2, w1, w0]), (0,13,11,1,slack 262,[w6, w5, w4, w3, w2, w419, w0]), (0,13,11,1,slack 262,[w6, w5, w4, w421, w2, w1, w0]), (0,13,11,1,slack 265,[w6, w93, w5, w4, w3, w12, w2, w1, w0]), (0,13,11,1,slack 267,[w6, w93, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 273,[w6, w5, w4, w3, w2, w284, w0]), (0,13,11,1,slack 273,[w6, w5, w4, w3, w285, w1, w0]), (0,13,11,1,slack 273,[w6, w5, w4, w286, w2, w1, w0]), (0,13,11,1,slack 273,[w6, w5, w287, w3, w2, w1, w0]), (0,13,11,1,slack 273,[w288, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 275,[w6, w5, w4, w101, w3, w2, w1, w0]), (0,13,11,1,slack 277,[w6, w5, w132, w4, w3, w2, w1, w0]), (0,13,11,1,slack 278,[w6, w5, w4, w90, w3, w12, w2, w1, w0]), (0,13,11,1,slack 279,[w6, w5, w4, w90, w3, w2, w1, w0]), (0,13,11,1,slack 280,[w6, w5, w102, w4, w3, w2, w1, w0]), (0,13,11,1,slack 281,[w6, w5, w91, w4, w3, w12, w2, w1, w0]), (0,13,11,1,slack 282,[w6, w5, w91, w4, w3, w2, w1, w0]), (0,13,11,1,slack 283,[w6, w5, w3, w2, w1, w0, w330]), (0,13,11,1,slack 291,[w68, w34, w6, w5, w4, w3, w2, w1, w0])]
noncomputable def rowBlock9 : Array (Arg) := #[(0,13,11,1,slack 293,[w68, w33, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 294,[w68, w6, w5, w4, w3, w2, w9, w1, w0]), (0,13,11,1,slack 297,[w6, w5, w4, w63, w3, w2, w9, w1, w0]), (0,13,11,1,slack 298,[w6, w5, w4, w63, w16, w3, w2, w1, w0]), (0,13,11,1,slack 299,[w6, w5, w4, w63, w15, w3, w2, w1, w0]), (0,13,11,1,slack 302,[w6, w5, w4, w3, w2, w1, w0, w447]), (0,13,11,1,slack 303,[w6, w5, w4, w3, w2, w1, w0, w308]), (0,13,11,1,slack 305,[w6, w5, w64, w4, w3, w2, w9, w1, w0]), (0,13,11,1,slack 307,[w6, w5, w4, w3, w62, w2, w9, w1, w0]), (0,13,11,1,slack 308,[w68, w6, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 309,[w6, w66, w5, w4, w3, w2, w1, w0]), (0,13,11,1,slack 310,[w6, w5, w4, w3, w2, w1, w0, w143]), (0,13,11,1,slack 312,[w6, w5, w4, w63, w3, w2, w1, w0]), (0,13,11,1,slack 313,[w6, w5, w64, w4, w3, w2, w1, w0]), (0,13,11,1,slack 314,[w6, w5, w4, w3, w62, w12, w2, w1, w0]), (0,13,11,1,slack 315,[w6, w5, w4, w3, w62, w2, w1, w0]), (1,12,11,1,slack 0,[w6, w5, w4, w3, w2, w27, w1, w0, w32]), (1,12,11,1,slack 1,[w40, w6, w5, w4, w3, w2, w1, w0, w11]), (1,12,11,1,slack 3,[w6, w5, w4, w3, w2, w1, w0, w35, w24]), (1,12,11,1,slack 5,[w37, w6, w5, w4, w3, w2, w27, w1, w0]), (1,12,11,1,slack 6,[w6, w29, w5, w4, w3, w2, w1, w0, w35]), (1,12,11,1,slack 7,[w6, w29, w5, w4, w3, w2, w1, w0, w32]), (1,12,11,1,slack 8,[w40, w37, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 9,[w37, w6, w5, w4, w3, w2, w1, w0, w24])]
noncomputable def rowBlock10 : Array (Arg) := #[(1,12,11,1,slack 10,[w40, w6, w29, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 13,[w40, w38, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 14,[w38, w6, w5, w4, w3, w2, w1, w0, w24]), (1,12,11,1,slack 16,[w6, w28, w5, w4, w3, w2, w1, w0, w32]), (1,12,11,1,slack 17,[w40, w36, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 18,[w36, w6, w5, w4, w3, w2, w1, w0, w24]), (1,12,11,1,slack 19,[w40, w6, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 21,[w6, w5, w22, w4, w3, w2, w1, w0, w35]), (1,12,11,1,slack 22,[w6, w5, w22, w4, w3, w2, w1, w0, w32]), (1,12,11,1,slack 23,[w37, w38, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 24,[w38, w6, w29, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 24,[w37, w6, w30, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 24,[w40, w6, w5, w22, w4, w3, w2, w1, w0]), (1,12,11,1,slack 25,[w6, w5, w22, w4, w3, w2, w1, w0, w24]), (1,12,11,1,slack 26,[w6, w5, w4, w17, w3, w2, w1, w0, w32]), (1,12,11,1,slack 27,[w37, w36, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 28,[w36, w6, w29, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 28,[w37, w6, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 28,[w40, w6, w5, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 29,[w6, w5, w4, w17, w3, w2, w1, w0, w24]), (1,12,11,1,slack 31,[w36, w38, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 32,[w38, w6, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 32,[w36, w6, w30, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 32,[w40, w6, w5, w21, w4, w3, w2, w1, w0])]
noncomputable def rowBlock11 : Array (Arg) := #[(1,12,11,1,slack 33,[w36, w6, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 36,[w38, w6, w5, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 36,[w36, w6, w5, w22, w4, w3, w2, w1, w0]), (1,12,11,1,slack 36,[w37, w6, w5, w21, w4, w3, w2, w1, w0]), (1,12,11,1,slack 37,[w6, w28, w5, w22, w4, w3, w2, w1, w0]), (1,12,11,1,slack 37,[w6, w29, w5, w21, w4, w3, w2, w1, w0]), (1,12,11,1,slack 39,[w34, w6, w5, w4, w3, w2, w27, w1, w0]), (1,12,11,1,slack 40,[w34, w6, w5, w4, w3, w2, w1, w0, w11]), (1,12,11,1,slack 41,[w6, w26, w5, w4, w3, w2, w1, w0, w35]), (1,12,11,1,slack 42,[w6, w26, w5, w4, w3, w2, w1, w0, w32]), (1,12,11,1,slack 43,[w40, w34, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 44,[w34, w6, w5, w4, w3, w2, w1, w0, w24]), (1,12,11,1,slack 45,[w40, w6, w26, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 47,[w33, w6, w5, w4, w3, w2, w27, w1, w0]), (1,12,11,1,slack 49,[w6, w25, w5, w4, w3, w2, w1, w0, w35]), (1,12,11,1,slack 51,[w40, w33, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 53,[w40, w6, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 55,[w6, w5, w39, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 56,[w6, w5, w4, w16, w3, w2, w27, w1, w0]), (1,12,11,1,slack 57,[w6, w5, w4, w16, w3, w2, w1, w0, w11]), (1,12,11,1,slack 58,[w6, w5, w4, w16, w3, w2, w1, w0, w35]), (1,12,11,1,slack 61,[w6, w5, w4, w16, w3, w2, w1, w0, w32]), (1,12,11,1,slack 62,[w37, w34, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 63,[w34, w6, w29, w5, w4, w3, w2, w1, w0])]
noncomputable def rowBlock12 : Array (Arg) := #[(1,12,11,1,slack 63,[w37, w6, w26, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 63,[w40, w6, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 64,[w6, w5, w4, w16, w3, w2, w1, w0, w24]), (1,12,11,1,slack 66,[w6, w5, w39, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 67,[w6, w5, w4, w15, w3, w2, w27, w1, w0]), (1,12,11,1,slack 68,[w6, w5, w4, w15, w3, w2, w1, w0, w35]), (1,12,11,1,slack 69,[w37, w33, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 70,[w33, w6, w29, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 70,[w37, w6, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 70,[w40, w6, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 71,[w6, w29, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 75,[w6, w5, w20, w4, w3, w2, w1, w0, w35]), (1,12,11,1,slack 76,[w6, w5, w20, w4, w3, w2, w1, w0, w32]), (1,12,11,1,slack 77,[w38, w34, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 78,[w34, w6, w30, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 78,[w38, w6, w26, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 78,[w40, w6, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 79,[w6, w5, w20, w4, w3, w2, w1, w0, w24]), (1,12,11,1,slack 80,[w6, w5, w4, w3, w13, w2, w1, w0, w32]), (1,12,11,1,slack 81,[w36, w34, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 82,[w34, w6, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 82,[w36, w6, w26, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 82,[w40, w6, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 83,[w6, w5, w4, w3, w13, w2, w1, w0, w24])]
noncomputable def rowBlock13 : Array (Arg) := #[(1,12,11,1,slack 84,[w6, w5, w19, w4, w3, w2, w1, w0, w35]), (1,12,11,1,slack 85,[w38, w33, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 86,[w33, w6, w30, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 86,[w38, w6, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 86,[w40, w6, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 87,[w34, w6, w5, w22, w4, w3, w2, w1, w0]), (1,12,11,1,slack 87,[w38, w6, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 87,[w37, w6, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 88,[w6, w5, w39, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 93,[w36, w33, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 102,[w6, w26, w5, w22, w4, w3, w2, w1, w0]), (1,12,11,1,slack 102,[w6, w29, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 102,[w6, w30, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 104,[w33, w6, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 104,[w36, w6, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 104,[w40, w6, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 116,[w6, w25, w28, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 117,[w34, w6, w5, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 117,[w36, w6, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 117,[w37, w6, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 120,[w6, w28, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 120,[w6, w26, w5, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 120,[w6, w29, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 123,[w33, w6, w5, w22, w4, w3, w2, w1, w0])]
noncomputable def rowBlock14 : Array (Arg) := #[(1,12,11,1,slack 123,[w38, w6, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 123,[w37, w6, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 125,[w6, w25, w5, w22, w4, w3, w2, w1, w0]), (1,12,11,1,slack 125,[w6, w29, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 125,[w6, w30, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 127,[w33, w6, w5, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 127,[w36, w6, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 127,[w37, w6, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 128,[w6, w28, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 128,[w6, w25, w5, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 128,[w6, w29, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 129,[w40, w6, w29, w4, w3, w2, w1, w0]), (1,12,11,1,slack 133,[w34, w6, w5, w21, w4, w3, w2, w1, w0]), (1,12,11,1,slack 133,[w38, w6, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 133,[w36, w6, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 134,[w6, w28, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 134,[w6, w30, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 135,[w36, w6, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 138,[w33, w6, w5, w21, w4, w3, w2, w1, w0]), (1,12,11,1,slack 138,[w38, w6, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 138,[w36, w6, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 139,[w6, w28, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 139,[w6, w25, w5, w21, w4, w3, w2, w1, w0]), (1,12,11,1,slack 139,[w6, w30, w5, w4, w3, w12, w2, w1, w0])]
noncomputable def rowBlock15 : Array (Arg) := #[(1,12,11,1,slack 140,[w40, w38, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 141,[w6, w5, w20, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 141,[w6, w5, w21, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 141,[w6, w5, w22, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 142,[w36, w6, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 145,[w6, w28, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 147,[w40, w6, w28, w4, w3, w2, w1, w0]), (1,12,11,1,slack 150,[w6, w5, w19, w4, w17, w3, w2, w1, w0]), (1,12,11,1,slack 150,[w6, w5, w21, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 150,[w6, w5, w22, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 151,[w38, w6, w5, w22, w3, w2, w1, w0]), (1,12,11,1,slack 153,[w6, w29, w5, w22, w4, w2, w1, w0]), (1,12,11,1,slack 155,[w6, w5, w4, w17, w3, w12, w2, w1, w0]), (1,12,11,1,slack 156,[w36, w6, w5, w4, w17, w3, w1, w0]), (1,12,11,1,slack 156,[w37, w6, w5, w4, w17, w2, w1, w0]), (1,12,11,1,slack 156,[w37, w36, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 157,[w6, w29, w28, w4, w3, w2, w1, w0]), (1,12,11,1,slack 159,[w38, w6, w5, w21, w3, w2, w1, w0]), (1,12,11,1,slack 159,[w36, w38, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 161,[w6, w28, w5, w21, w4, w3, w1, w0]), (1,12,11,1,slack 161,[w6, w30, w28, w4, w3, w2, w1, w0]), (1,12,11,1,slack 163,[w6, w5, w22, w4, w17, w2, w1, w0]), (1,12,11,1,slack 163,[w6, w5, w22, w21, w3, w2, w1, w0]), (1,12,11,1,slack 165,[w6, w5, w4, w3, w2, w27, w9, w1, w0])]
noncomputable def rowBlock16 : Array (Arg) := #[(1,12,11,1,slack 166,[w6, w5, w4, w3, w2, w9, w1, w0, w35]), (1,12,11,1,slack 167,[w34, w33, w6, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 168,[w33, w6, w26, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 168,[w34, w6, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 168,[w40, w6, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 170,[w33, w6, w25, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 174,[w33, w6, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 174,[w34, w6, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 174,[w37, w6, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 177,[w6, w25, w5, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 177,[w6, w26, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 177,[w6, w29, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 183,[w33, w6, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 185,[w6, w25, w5, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 190,[w33, w6, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 190,[w34, w6, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 190,[w38, w6, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 191,[w6, w25, w5, w20, w4, w3, w2, w1, w0]), (1,12,11,1,slack 191,[w6, w26, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 191,[w6, w30, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 193,[w33, w6, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 193,[w34, w6, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 193,[w36, w6, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 196,[w6, w28, w5, w4, w3, w2, w9, w1, w0])]
noncomputable def rowBlock17 : Array (Arg) := #[(1,12,11,1,slack 196,[w6, w25, w5, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 196,[w6, w26, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 197,[w40, w6, w26, w4, w3, w2, w1, w0]), (1,12,11,1,slack 197,[w40, w34, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 199,[w33, w6, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 201,[w6, w25, w5, w19, w4, w3, w2, w1, w0]), (1,12,11,1,slack 203,[w6, w5, w19, w4, w16, w3, w2, w1, w0]), (1,12,11,1,slack 203,[w6, w5, w20, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 203,[w6, w5, w22, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 204,[w33, w6, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 210,[w6, w25, w5, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 213,[w40, w6, w25, w4, w3, w2, w1, w0]), (1,12,11,1,slack 213,[w40, w33, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 215,[w6, w5, w4, w15, w3, w13, w2, w1, w0]), (1,12,11,1,slack 215,[w6, w5, w4, w16, w3, w12, w2, w1, w0]), (1,12,11,1,slack 215,[w6, w5, w4, w17, w3, w2, w9, w1, w0]), (1,12,11,1,slack 217,[w34, w6, w5, w4, w16, w3, w2, w0]), (1,12,11,1,slack 217,[w37, w6, w5, w4, w16, w2, w1, w0]), (1,12,11,1,slack 222,[w6, w29, w5, w4, w16, w2, w1, w0]), (1,12,11,1,slack 226,[w6, w5, w19, w4, w15, w3, w2, w1, w0]), (1,12,11,1,slack 227,[w6, w5, w4, w15, w3, w12, w2, w1, w0]), (1,12,11,1,slack 229,[w33, w6, w5, w4, w15, w3, w2, w1]), (1,12,11,1,slack 229,[w37, w6, w5, w4, w15, w2, w1, w0]), (1,12,11,1,slack 229,[w37, w33, w5, w4, w3, w2, w1, w0])]
noncomputable def rowBlock18 : Array (Arg) := #[(1,12,11,1,slack 230,[w6, w29, w5, w4, w15, w2, w1, w0]), (1,12,11,1,slack 230,[w6, w29, w25, w4, w3, w2, w1, w0]), (1,12,11,1,slack 232,[w6, w5, w19, w4, w3, w13, w2, w1, w0]), (1,12,11,1,slack 232,[w6, w5, w20, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 232,[w6, w5, w21, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 233,[w38, w6, w5, w20, w3, w2, w1, w0]), (1,12,11,1,slack 235,[w6, w26, w5, w20, w4, w3, w2, w0]), (1,12,11,1,slack 235,[w6, w30, w5, w20, w3, w2, w1, w0]), (1,12,11,1,slack 237,[w6, w5, w4, w3, w13, w12, w2, w1, w0]), (1,12,11,1,slack 238,[w34, w6, w5, w4, w3, w13, w2, w0]), (1,12,11,1,slack 238,[w36, w6, w5, w4, w3, w13, w1, w0]), (1,12,11,1,slack 240,[w6, w28, w5, w4, w3, w13, w1, w0]), (1,12,11,1,slack 242,[w6, w5, w19, w4, w3, w12, w2, w1, w0]), (1,12,11,1,slack 244,[w38, w6, w5, w19, w3, w2, w1, w0]), (1,12,11,1,slack 245,[w6, w25, w5, w19, w4, w3, w2, w1]), (1,12,11,1,slack 245,[w6, w30, w5, w19, w3, w2, w1, w0]), (1,12,11,1,slack 247,[w6, w5, w20, w4, w16, w3, w2, w0]), (1,12,11,1,slack 247,[w6, w5, w22, w4, w16, w2, w1, w0]), (1,12,11,1,slack 247,[w6, w5, w22, w20, w3, w2, w1, w0]), (1,12,11,1,slack 250,[w33, w6, w5, w4, w3, w12, w2, w1]), (1,12,11,1,slack 250,[w36, w6, w5, w4, w3, w12, w1, w0]), (1,12,11,1,slack 253,[w40, w39, w4, w3, w2, w1, w0]), (1,12,11,1,slack 254,[w6, w28, w4, w3, w27, w1, w0]), (1,12,11,1,slack 255,[w6, w5, w4, w3, w12, w1, w11])]
noncomputable def rowBlock19 : Array (Arg) := #[(1,12,11,1,slack 256,[w36, w5, w4, w3, w1, w0, w35]), (1,12,11,1,slack 262,[w33, w5, w4, w3, w2, w1, w32]), (1,12,11,1,slack 267,[w6, w28, w5, w4, w3, w12, w1, w0]), (1,12,11,1,slack 273,[w6, w25, w4, w3, w2, w1, w24]), (1,12,11,1,slack 275,[w6, w5, w4, w16, w3, w13, w2, w0]), (1,12,11,1,slack 277,[w6, w5, w22, w19, w3, w2, w1, w0]), (1,12,11,1,slack 279,[w6, w5, w4, w15, w3, w12, w2, w1]), (1,12,11,1,slack 279,[w6, w5, w4, w17, w3, w12, w1, w0]), (1,12,11,1,slack 280,[w6, w5, w20, w4, w3, w13, w2, w0]), (1,12,11,1,slack 282,[w6, w5, w19, w4, w3, w12, w2, w1]), (1,12,11,1,slack 292,[w33, w6, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 295,[w6, w25, w5, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 296,[w6, w5, w4, w15, w3, w2, w9, w1, w0]), (1,12,11,1,slack 304,[w6, w5, w19, w4, w3, w2, w9, w1, w0]), (1,12,11,1,slack 306,[w6, w5, w4, w3, w12, w2, w9, w1, w0]), (1,12,11,1,slack 308,[w33, w6, w5, w4, w3, w2, w9, w1]), (1,12,11,1,slack 308,[w34, w6, w5, w4, w3, w2, w9, w0]), (1,12,11,1,slack 308,[w34, w33, w5, w4, w3, w2, w1, w0]), (1,12,11,1,slack 309,[w6, w25, w5, w4, w3, w2, w9, w1]), (1,12,11,1,slack 309,[w6, w26, w5, w4, w3, w2, w9, w0]), (1,12,11,1,slack 309,[w6, w26, w25, w4, w3, w2, w1, w0]), (1,12,11,1,slack 312,[w6, w5, w4, w16, w3, w2, w9, w0]), (1,12,11,1,slack 312,[w6, w5, w4, w16, w15, w2, w1, w0]), (1,12,11,1,slack 313,[w6, w5, w20, w19, w3, w2, w1, w0])]
noncomputable def rowBlock20 : Array (Arg) := #[(1,12,11,1,slack 315,[w6, w5, w4, w3, w13, w12, w1, w0])]
noncomputable def rowBlocks : Array (Array (Arg)) := #[rowBlock0, rowBlock1, rowBlock2, rowBlock3, rowBlock4, rowBlock5, rowBlock6, rowBlock7, rowBlock8, rowBlock9, rowBlock10, rowBlock11, rowBlock12, rowBlock13, rowBlock14, rowBlock15, rowBlock16, rowBlock17, rowBlock18, rowBlock19, rowBlock20]
noncomputable def row (i : Nat) : Arg := ((rowBlocks.getD (i / 24) #[]).getD (i % 24) (0,0,0,0,0,[]))
def bucketBlock0 : Array (List Nat) := #[[66,111,188,353], [132,220,377], [47], [412], [], [11,95], [45,55], [451,466], [142], [347,438], [405,464], [], [379,409,471], [37,161], [134,160,423,436], [307], [179], [428], [156,341], [159], [], [201,285,344,455,465], [], []]
def bucketBlock1 : Array (List Nat) := #[[79], [284], [], [310,380], [259], [432], [81], [434], [198], [54,72], [41,150,430], [136,151,234,349,437], [184,208,418], [128,216], [], [9,186], [346], [], [118,274,364], [43,300], [294], [], [], [38,299]]
def bucketBlock2 : Array (List Nat) := #[[109,129,171,199], [96], [301,446,480], [190], [157,204], [44,470], [], [85,93,251,267,319], [31], [75,290], [42,411,442], [144], [], [86], [33,472], [225,393,424], [194], [84,394], [], [230], [], [183,327,330], [], [221]]
def bucketBlock3 : Array (List Nat) := #[[], [166,308,337,387,444], [115,268,277], [110,404], [82], [70,100,189,243,351,355,392], [117,131,352,391], [195,305], [124,255], [], [271], [], [168], [29,200], [78,143], [1,306], [298], [185,397], [326], [77,174,203,224,239,309,361], [], [19,175], [153,287,457], [59,149,248,342]]
def bucketBlock4 : Array (List Nat) := #[[289,459], [], [16,320], [247,328,407], [155], [91,140,473,477], [133,139,169,360], [57,97], [51,318], [40,53,264], [453], [24], [5,74,162], [197,249,374], [357], [6,256,381], [], [25,384,426], [172], [414], [317], [3,417], [214,276,322], [36]]
def bucketBlock5 : Array (List Nat) := #[[22,56,359], [273], [223,297], [10,311,385,475], [121], [154,272,282], [7,138,212,303,427], [213,338], [20,476], [209], [293,336,441], [87,253], [8,246,280,416,419], [67,266,425], [167,227,302,348], [2,449], [62], [152,173], [], [127,180,372], [261,281,315,321,458], [233], [], []]
def bucketBlock6 : Array (List Nat) := #[[191,202,219,229,235], [331,358,401], [], [119,215,324], [433,468], [237,278], [], [64,148,262,350,375], [399], [236,240], [402], [58,94,104], [], [], [238,340], [390], [30], [250], [26], [122,413], [269,323], [], [291,362,420], [146,187,329,339,467]]
def bucketBlock7 : Array (List Nat) := #[[99,165,422], [50,158,333], [73,205,275,429], [32], [0,14], [27,88,105,145,406], [48,130], [252,286], [], [], [263,304], [92], [112,325,389,461], [71,80,386], [279,371], [101,218,447,479], [356,448,460], [207,382,396], [23,312,395], [21,61,217,245,343], [462], [], [228,313,435], [76]]
def bucketBlock8 : Array (List Nat) := #[[368], [46,345], [65,181,222], [34], [], [126,232], [35,378], [15], [193,363], [295], [120,431], [474], [370,450], [18,135,231], [], [], [], [], [], [108,206,316], [52,125,366], [454], [], [170,388]]
def bucketBlock9 : Array (List Nat) := #[[], [90,107,211], [244], [60,106,469], [260], [], [39,141,147,439], [270,335,373,400], [365,410], [192], [258], [182], [4,478], [], [13,292,367], [177,421], [83], [], [265,383,440,463], [], [102,123], [116,163,242], [63,89,176], [113,210]]
def bucketBlock10 : Array (List Nat) := #[[283], [28,98,314,354,398,452], [69,369,456], [12,376,415,443], [68,164,196], [114], [17], [178,241], [254], [], [49,257,296,408], [288,332,403], [137,445], [103], [226,334], []]
def bucketBlocks : Array (Array (List Nat)) := #[bucketBlock0, bucketBlock1, bucketBlock2, bucketBlock3, bucketBlock4, bucketBlock5, bucketBlock6, bucketBlock7, bucketBlock8, bucketBlock9, bucketBlock10]
def bucket (i : Nat) : List Nat := ((bucketBlocks.getD (i / 24) #[]).getD (i % 24) [])
def limit := 481
def key (tag k z : Nat) (v : List W) : Nat :=
  (z % 65521 + v.foldl (fun h w => (h*37+w.s%65521)%65521) 0 + 3*k + tag*257)%256
noncomputable def watch : Test := fun tag f k t z v =>
  if (f == 13 && (k == 10 || k == 11)) || (tag == 1 && f == 12 && k == 11) then (bucket (key tag k z v)).any (fun i => decide (i < limit) && same (tag,f,k,t,z,v) (row i)) else false
noncomputable def staged (a : Arg) : Bool :=
  match a with
  | (tag,f,k,t,z,v) => st (lz 4) fun l => st (mz 4) fun m => st budget fun g =>
      st z fun z => frc v fun v => original l m g 13 (tag,f,k,t,z,v)
theorem staged_eq (a : Arg) : staged a = original (lz 4) (mz 4) budget 13 a := by
  rcases a with ⟨tag,f,k,t,z,v⟩
  simp only [staged,st_eq,frc_eq]
noncomputable def pass (i : Nat) : Bool := !(staged (row i))
def Span (lo size : Nat) := ∀ i, lo ≤ i → i < lo+size → pass i = true
theorem ofCheck {lo size : Nat} (h : (List.range' lo size).all pass = true) : Span lo size := by
  intro i hl hu
  apply List.all_eq_true.mp h
  simpa [List.mem_range'_1] using And.intro hl hu
theorem join {a b c : Nat} (h : Span a b) (h' : Span (a+b) c) : Span a (b+c) := by
  intro i hl hu
  by_cases s : i < a+b
  · exact h i hl s
  · exact h' i (by omega) (by omega)
theorem soundWatch (all : Span 0 limit) : Valid watch (lz 4) (mz 4) budget 13 := by
  intro tag f k t z v tested
  unfold watch at tested
  split at tested <;> try contradiction
  obtain ⟨i,_,he⟩ := List.any_eq_true.mp tested
  obtain ⟨hi,eq⟩ := Bool.and_eq_true_iff.mp he
  have h := all i (Nat.zero_le _) (of_decide_eq_true hi)
  rw [(same_iff _ _).mp eq,←staged_eq]
  simpa only [pass,Bool.not_eq_true'] using h
end PEqualNP.Outside.L_meta_32632.RowData
namespace PEqualNP.Outside.L_meta_32632.RowData
theorem slice0 : Span 0 5 := ofCheck (by decide +kernel)
theorem slice5 : Span 5 5 := ofCheck (by decide +kernel)
theorem slice10 : Span 10 4 := ofCheck (by decide +kernel)
theorem slice14 : Span 14 4 := ofCheck (by decide +kernel)
theorem slice18 : Span 18 4 := ofCheck (by decide +kernel)
theorem slice22 : Span 22 5 := ofCheck (by decide +kernel)
theorem slice27 : Span 27 4 := ofCheck (by decide +kernel)
theorem slice31 : Span 31 5 := ofCheck (by decide +kernel)
theorem slice36 : Span 36 4 := ofCheck (by decide +kernel)
theorem slice40 : Span 40 4 := ofCheck (by decide +kernel)
theorem slice44 : Span 44 5 := ofCheck (by decide +kernel)
theorem slice49 : Span 49 4 := ofCheck (by decide +kernel)
theorem slice53 : Span 53 3 := ofCheck (by decide +kernel)
theorem slice56 : Span 56 1 := ofCheck (by decide +kernel)
theorem slice57 : Span 57 1 := ofCheck (by decide +kernel)
theorem slice58 : Span 58 1 := ofCheck (by decide +kernel)
theorem slice59 : Span 59 1 := ofCheck (by decide +kernel)
theorem slice60 : Span 60 2 := ofCheck (by decide +kernel)
theorem slice62 : Span 62 2 := ofCheck (by decide +kernel)
theorem slice64 : Span 64 2 := ofCheck (by decide +kernel)
theorem slice66 : Span 66 2 := ofCheck (by decide +kernel)
theorem slice68 : Span 68 2 := ofCheck (by decide +kernel)
theorem slice70 : Span 70 2 := ofCheck (by decide +kernel)
theorem slice72 : Span 72 3 := ofCheck (by decide +kernel)
theorem slice75 : Span 75 1 := ofCheck (by decide +kernel)
theorem slice76 : Span 76 1 := ofCheck (by decide +kernel)
theorem slice77 : Span 77 1 := ofCheck (by decide +kernel)
theorem slice78 : Span 78 2 := ofCheck (by decide +kernel)
theorem slice80 : Span 80 1 := ofCheck (by decide +kernel)
theorem slice81 : Span 81 2 := ofCheck (by decide +kernel)
theorem slice83 : Span 83 2 := ofCheck (by decide +kernel)
theorem slice85 : Span 85 5 := ofCheck (by decide +kernel)
theorem slice90 : Span 90 2 := ofCheck (by decide +kernel)
theorem slice92 : Span 92 4 := ofCheck (by decide +kernel)
theorem slice96 : Span 96 1 := ofCheck (by decide +kernel)
theorem slice97 : Span 97 2 := ofCheck (by decide +kernel)
theorem slice99 : Span 99 2 := ofCheck (by decide +kernel)
theorem slice101 : Span 101 2 := ofCheck (by decide +kernel)
theorem slice103 : Span 103 2 := ofCheck (by decide +kernel)
theorem slice105 : Span 105 2 := ofCheck (by decide +kernel)
theorem slice107 : Span 107 1 := ofCheck (by decide +kernel)
theorem slice108 : Span 108 3 := ofCheck (by decide +kernel)
theorem slice111 : Span 111 1 := ofCheck (by decide +kernel)
theorem slice112 : Span 112 2 := ofCheck (by decide +kernel)
theorem slice114 : Span 114 3 := ofCheck (by decide +kernel)
theorem slice117 : Span 117 2 := ofCheck (by decide +kernel)
theorem slice119 : Span 119 1 := ofCheck (by decide +kernel)
theorem slice120 : Span 120 3 := ofCheck (by decide +kernel)
theorem slice123 : Span 123 3 := ofCheck (by decide +kernel)
theorem slice126 : Span 126 2 := ofCheck (by decide +kernel)
theorem slice128 : Span 128 1 := ofCheck (by decide +kernel)
theorem slice129 : Span 129 1 := ofCheck (by decide +kernel)
theorem slice130 : Span 130 2 := ofCheck (by decide +kernel)
theorem slice132 : Span 132 2 := ofCheck (by decide +kernel)
theorem slice134 : Span 134 1 := ofCheck (by decide +kernel)
theorem slice135 : Span 135 3 := ofCheck (by decide +kernel)
theorem slice138 : Span 138 2 := ofCheck (by decide +kernel)
theorem slice140 : Span 140 2 := ofCheck (by decide +kernel)
theorem slice142 : Span 142 1 := ofCheck (by decide +kernel)
theorem slice143 : Span 143 2 := ofCheck (by decide +kernel)
theorem slice145 : Span 145 1 := ofCheck (by decide +kernel)
theorem slice146 : Span 146 2 := ofCheck (by decide +kernel)
theorem slice148 : Span 148 2 := ofCheck (by decide +kernel)
theorem slice150 : Span 150 2 := ofCheck (by decide +kernel)
theorem slice152 : Span 152 2 := ofCheck (by decide +kernel)
theorem slice154 : Span 154 3 := ofCheck (by decide +kernel)
theorem slice157 : Span 157 1 := ofCheck (by decide +kernel)
theorem slice158 : Span 158 1 := ofCheck (by decide +kernel)
theorem slice159 : Span 159 1 := ofCheck (by decide +kernel)
theorem slice160 : Span 160 1 := ofCheck (by decide +kernel)
theorem slice161 : Span 161 2 := ofCheck (by decide +kernel)
theorem slice163 : Span 163 5 := ofCheck (by decide +kernel)
theorem slice168 : Span 168 1 := ofCheck (by decide +kernel)
theorem slice169 : Span 169 1 := ofCheck (by decide +kernel)
theorem slice170 : Span 170 1 := ofCheck (by decide +kernel)
theorem slice171 : Span 171 1 := ofCheck (by decide +kernel)
theorem slice172 : Span 172 3 := ofCheck (by decide +kernel)
theorem slice175 : Span 175 1 := ofCheck (by decide +kernel)
theorem slice176 : Span 176 1 := ofCheck (by decide +kernel)
theorem slice177 : Span 177 1 := ofCheck (by decide +kernel)
theorem slice178 : Span 178 1 := ofCheck (by decide +kernel)
theorem slice179 : Span 179 1 := ofCheck (by decide +kernel)
theorem slice180 : Span 180 1 := ofCheck (by decide +kernel)
theorem slice181 : Span 181 2 := ofCheck (by decide +kernel)
theorem slice183 : Span 183 2 := ofCheck (by decide +kernel)
theorem slice185 : Span 185 1 := ofCheck (by decide +kernel)
theorem slice186 : Span 186 2 := ofCheck (by decide +kernel)
theorem slice188 : Span 188 2 := ofCheck (by decide +kernel)
theorem slice190 : Span 190 1 := ofCheck (by decide +kernel)
theorem slice191 : Span 191 1 := ofCheck (by decide +kernel)
theorem slice192 : Span 192 1 := ofCheck (by decide +kernel)
theorem slice193 : Span 193 3 := ofCheck (by decide +kernel)
theorem slice196 : Span 196 4 := ofCheck (by decide +kernel)
theorem slice200 : Span 200 1 := ofCheck (by decide +kernel)
theorem slice201 : Span 201 1 := ofCheck (by decide +kernel)
theorem slice202 : Span 202 4 := ofCheck (by decide +kernel)
theorem slice206 : Span 206 1 := ofCheck (by decide +kernel)
theorem slice207 : Span 207 1 := ofCheck (by decide +kernel)
theorem slice208 : Span 208 2 := ofCheck (by decide +kernel)
theorem slice210 : Span 210 2 := ofCheck (by decide +kernel)
theorem slice212 : Span 212 2 := ofCheck (by decide +kernel)
theorem slice214 : Span 214 2 := ofCheck (by decide +kernel)
theorem slice216 : Span 216 2 := ofCheck (by decide +kernel)
theorem slice218 : Span 218 2 := ofCheck (by decide +kernel)
theorem slice220 : Span 220 3 := ofCheck (by decide +kernel)
theorem slice223 : Span 223 2 := ofCheck (by decide +kernel)
theorem slice225 : Span 225 2 := ofCheck (by decide +kernel)
theorem slice227 : Span 227 1 := ofCheck (by decide +kernel)
theorem slice228 : Span 228 1 := ofCheck (by decide +kernel)
theorem slice229 : Span 229 1 := ofCheck (by decide +kernel)
theorem slice230 : Span 230 1 := ofCheck (by decide +kernel)
theorem slice231 : Span 231 1 := ofCheck (by decide +kernel)
theorem slice232 : Span 232 2 := ofCheck (by decide +kernel)
theorem slice234 : Span 234 2 := ofCheck (by decide +kernel)
theorem slice236 : Span 236 2 := ofCheck (by decide +kernel)
theorem slice238 : Span 238 1 := ofCheck (by decide +kernel)
theorem slice239 : Span 239 1 := ofCheck (by decide +kernel)
theorem slice240 : Span 240 1 := ofCheck (by decide +kernel)
theorem slice241 : Span 241 1 := ofCheck (by decide +kernel)
theorem slice242 : Span 242 1 := ofCheck (by decide +kernel)
theorem slice243 : Span 243 1 := ofCheck (by decide +kernel)
theorem slice244 : Span 244 1 := ofCheck (by decide +kernel)
theorem slice245 : Span 245 1 := ofCheck (by decide +kernel)
theorem slice246 : Span 246 2 := ofCheck (by decide +kernel)
theorem slice248 : Span 248 1 := ofCheck (by decide +kernel)
theorem slice249 : Span 249 2 := ofCheck (by decide +kernel)
theorem slice251 : Span 251 1 := ofCheck (by decide +kernel)
theorem slice252 : Span 252 1 := ofCheck (by decide +kernel)
theorem slice253 : Span 253 2 := ofCheck (by decide +kernel)
theorem slice255 : Span 255 1 := ofCheck (by decide +kernel)
theorem slice256 : Span 256 1 := ofCheck (by decide +kernel)
theorem slice257 : Span 257 1 := ofCheck (by decide +kernel)
theorem slice258 : Span 258 1 := ofCheck (by decide +kernel)
theorem slice259 : Span 259 2 := ofCheck (by decide +kernel)
theorem slice261 : Span 261 1 := ofCheck (by decide +kernel)
theorem slice262 : Span 262 1 := ofCheck (by decide +kernel)
theorem slice263 : Span 263 1 := ofCheck (by decide +kernel)
theorem slice264 : Span 264 2 := ofCheck (by decide +kernel)
theorem slice266 : Span 266 2 := ofCheck (by decide +kernel)
theorem slice268 : Span 268 3 := ofCheck (by decide +kernel)
theorem slice271 : Span 271 3 := ofCheck (by decide +kernel)
theorem slice274 : Span 274 1 := ofCheck (by decide +kernel)
theorem slice275 : Span 275 2 := ofCheck (by decide +kernel)
theorem slice277 : Span 277 1 := ofCheck (by decide +kernel)
theorem slice278 : Span 278 1 := ofCheck (by decide +kernel)
theorem slice279 : Span 279 1 := ofCheck (by decide +kernel)
theorem slice280 : Span 280 2 := ofCheck (by decide +kernel)
theorem slice282 : Span 282 2 := ofCheck (by decide +kernel)
theorem slice284 : Span 284 1 := ofCheck (by decide +kernel)
theorem slice285 : Span 285 1 := ofCheck (by decide +kernel)
theorem slice286 : Span 286 1 := ofCheck (by decide +kernel)
theorem slice287 : Span 287 1 := ofCheck (by decide +kernel)
theorem slice288 : Span 288 1 := ofCheck (by decide +kernel)
theorem slice289 : Span 289 1 := ofCheck (by decide +kernel)
theorem slice290 : Span 290 1 := ofCheck (by decide +kernel)
theorem slice291 : Span 291 2 := ofCheck (by decide +kernel)
theorem slice293 : Span 293 1 := ofCheck (by decide +kernel)
theorem slice294 : Span 294 1 := ofCheck (by decide +kernel)
theorem slice295 : Span 295 1 := ofCheck (by decide +kernel)
theorem slice296 : Span 296 1 := ofCheck (by decide +kernel)
theorem slice297 : Span 297 1 := ofCheck (by decide +kernel)
theorem slice298 : Span 298 2 := ofCheck (by decide +kernel)
theorem slice300 : Span 300 1 := ofCheck (by decide +kernel)
theorem slice301 : Span 301 2 := ofCheck (by decide +kernel)
theorem slice303 : Span 303 1 := ofCheck (by decide +kernel)
theorem slice304 : Span 304 1 := ofCheck (by decide +kernel)
theorem slice305 : Span 305 2 := ofCheck (by decide +kernel)
theorem slice307 : Span 307 1 := ofCheck (by decide +kernel)
theorem slice308 : Span 308 1 := ofCheck (by decide +kernel)
theorem slice309 : Span 309 1 := ofCheck (by decide +kernel)
theorem slice310 : Span 310 1 := ofCheck (by decide +kernel)
theorem slice311 : Span 311 2 := ofCheck (by decide +kernel)
theorem slice313 : Span 313 1 := ofCheck (by decide +kernel)
theorem slice314 : Span 314 1 := ofCheck (by decide +kernel)
theorem slice315 : Span 315 1 := ofCheck (by decide +kernel)
theorem slice316 : Span 316 1 := ofCheck (by decide +kernel)
theorem slice317 : Span 317 1 := ofCheck (by decide +kernel)
theorem slice318 : Span 318 1 := ofCheck (by decide +kernel)
theorem slice319 : Span 319 1 := ofCheck (by decide +kernel)
theorem slice320 : Span 320 1 := ofCheck (by decide +kernel)
theorem slice321 : Span 321 1 := ofCheck (by decide +kernel)
theorem slice322 : Span 322 1 := ofCheck (by decide +kernel)
theorem slice323 : Span 323 1 := ofCheck (by decide +kernel)
theorem slice324 : Span 324 1 := ofCheck (by decide +kernel)
theorem slice325 : Span 325 1 := ofCheck (by decide +kernel)
theorem slice326 : Span 326 1 := ofCheck (by decide +kernel)
theorem slice327 : Span 327 1 := ofCheck (by decide +kernel)
theorem slice328 : Span 328 1 := ofCheck (by decide +kernel)
theorem slice329 : Span 329 1 := ofCheck (by decide +kernel)
theorem slice330 : Span 330 1 := ofCheck (by decide +kernel)
theorem slice331 : Span 331 1 := ofCheck (by decide +kernel)
theorem slice332 : Span 332 1 := ofCheck (by decide +kernel)
theorem slice333 : Span 333 1 := ofCheck (by decide +kernel)
theorem slice334 : Span 334 1 := ofCheck (by decide +kernel)
theorem slice335 : Span 335 1 := ofCheck (by decide +kernel)
theorem slice336 : Span 336 1 := ofCheck (by decide +kernel)
theorem slice337 : Span 337 1 := ofCheck (by decide +kernel)
theorem slice338 : Span 338 1 := ofCheck (by decide +kernel)
theorem slice339 : Span 339 1 := ofCheck (by decide +kernel)
theorem slice340 : Span 340 1 := ofCheck (by decide +kernel)
theorem slice341 : Span 341 1 := ofCheck (by decide +kernel)
theorem slice342 : Span 342 1 := ofCheck (by decide +kernel)
theorem slice343 : Span 343 1 := ofCheck (by decide +kernel)
theorem slice344 : Span 344 1 := ofCheck (by decide +kernel)
theorem slice345 : Span 345 1 := ofCheck (by decide +kernel)
theorem slice346 : Span 346 1 := ofCheck (by decide +kernel)
theorem slice347 : Span 347 1 := ofCheck (by decide +kernel)
theorem slice348 : Span 348 1 := ofCheck (by decide +kernel)
theorem slice349 : Span 349 1 := ofCheck (by decide +kernel)
theorem slice350 : Span 350 1 := ofCheck (by decide +kernel)
theorem slice351 : Span 351 3 := ofCheck (by decide +kernel)
theorem slice354 : Span 354 1 := ofCheck (by decide +kernel)
theorem slice355 : Span 355 1 := ofCheck (by decide +kernel)
theorem slice356 : Span 356 1 := ofCheck (by decide +kernel)
theorem slice357 : Span 357 1 := ofCheck (by decide +kernel)
theorem slice358 : Span 358 1 := ofCheck (by decide +kernel)
theorem slice359 : Span 359 1 := ofCheck (by decide +kernel)
theorem slice360 : Span 360 1 := ofCheck (by decide +kernel)
theorem slice361 : Span 361 1 := ofCheck (by decide +kernel)
theorem slice362 : Span 362 1 := ofCheck (by decide +kernel)
theorem slice363 : Span 363 1 := ofCheck (by decide +kernel)
theorem slice364 : Span 364 1 := ofCheck (by decide +kernel)
theorem slice365 : Span 365 1 := ofCheck (by decide +kernel)
theorem slice366 : Span 366 1 := ofCheck (by decide +kernel)
theorem slice367 : Span 367 2 := ofCheck (by decide +kernel)
theorem slice369 : Span 369 1 := ofCheck (by decide +kernel)
theorem slice370 : Span 370 1 := ofCheck (by decide +kernel)
theorem slice371 : Span 371 1 := ofCheck (by decide +kernel)
theorem slice372 : Span 372 1 := ofCheck (by decide +kernel)
theorem slice373 : Span 373 1 := ofCheck (by decide +kernel)
theorem slice374 : Span 374 1 := ofCheck (by decide +kernel)
theorem slice375 : Span 375 1 := ofCheck (by decide +kernel)
theorem slice376 : Span 376 1 := ofCheck (by decide +kernel)
theorem slice377 : Span 377 1 := ofCheck (by decide +kernel)
theorem slice378 : Span 378 1 := ofCheck (by decide +kernel)
theorem slice379 : Span 379 1 := ofCheck (by decide +kernel)
theorem slice380 : Span 380 1 := ofCheck (by decide +kernel)
theorem slice381 : Span 381 1 := ofCheck (by decide +kernel)
theorem slice382 : Span 382 1 := ofCheck (by decide +kernel)
theorem slice383 : Span 383 1 := ofCheck (by decide +kernel)
theorem slice384 : Span 384 1 := ofCheck (by decide +kernel)
theorem slice385 : Span 385 1 := ofCheck (by decide +kernel)
theorem slice386 : Span 386 1 := ofCheck (by decide +kernel)
theorem slice387 : Span 387 1 := ofCheck (by decide +kernel)
theorem slice388 : Span 388 1 := ofCheck (by decide +kernel)
theorem slice389 : Span 389 1 := ofCheck (by decide +kernel)
theorem slice390 : Span 390 1 := ofCheck (by decide +kernel)
theorem slice391 : Span 391 1 := ofCheck (by decide +kernel)
theorem slice392 : Span 392 1 := ofCheck (by decide +kernel)
theorem slice393 : Span 393 1 := ofCheck (by decide +kernel)
theorem slice394 : Span 394 1 := ofCheck (by decide +kernel)
theorem slice395 : Span 395 1 := ofCheck (by decide +kernel)
theorem slice396 : Span 396 1 := ofCheck (by decide +kernel)
theorem slice397 : Span 397 1 := ofCheck (by decide +kernel)
theorem slice398 : Span 398 1 := ofCheck (by decide +kernel)
theorem slice399 : Span 399 1 := ofCheck (by decide +kernel)
theorem slice400 : Span 400 1 := ofCheck (by decide +kernel)
theorem slice401 : Span 401 2 := ofCheck (by decide +kernel)
theorem slice403 : Span 403 1 := ofCheck (by decide +kernel)
theorem slice404 : Span 404 1 := ofCheck (by decide +kernel)
theorem slice405 : Span 405 1 := ofCheck (by decide +kernel)
theorem slice406 : Span 406 1 := ofCheck (by decide +kernel)
theorem slice407 : Span 407 1 := ofCheck (by decide +kernel)
theorem slice408 : Span 408 1 := ofCheck (by decide +kernel)
theorem slice409 : Span 409 1 := ofCheck (by decide +kernel)
theorem slice410 : Span 410 1 := ofCheck (by decide +kernel)
theorem slice411 : Span 411 1 := ofCheck (by decide +kernel)
theorem slice412 : Span 412 1 := ofCheck (by decide +kernel)
theorem slice413 : Span 413 1 := ofCheck (by decide +kernel)
theorem slice414 : Span 414 1 := ofCheck (by decide +kernel)
theorem slice415 : Span 415 1 := ofCheck (by decide +kernel)
theorem slice416 : Span 416 1 := ofCheck (by decide +kernel)
theorem slice417 : Span 417 1 := ofCheck (by decide +kernel)
theorem slice418 : Span 418 1 := ofCheck (by decide +kernel)
theorem slice419 : Span 419 1 := ofCheck (by decide +kernel)
theorem slice420 : Span 420 1 := ofCheck (by decide +kernel)
theorem slice421 : Span 421 1 := ofCheck (by decide +kernel)
theorem slice422 : Span 422 1 := ofCheck (by decide +kernel)
theorem slice423 : Span 423 1 := ofCheck (by decide +kernel)
theorem slice424 : Span 424 1 := ofCheck (by decide +kernel)
theorem slice425 : Span 425 1 := ofCheck (by decide +kernel)
theorem slice426 : Span 426 1 := ofCheck (by decide +kernel)
theorem slice427 : Span 427 1 := ofCheck (by decide +kernel)
theorem slice428 : Span 428 1 := ofCheck (by decide +kernel)
theorem slice429 : Span 429 1 := ofCheck (by decide +kernel)
theorem slice430 : Span 430 1 := ofCheck (by decide +kernel)
theorem slice431 : Span 431 1 := ofCheck (by decide +kernel)
theorem slice432 : Span 432 1 := ofCheck (by decide +kernel)
theorem slice433 : Span 433 1 := ofCheck (by decide +kernel)
theorem slice434 : Span 434 1 := ofCheck (by decide +kernel)
theorem slice435 : Span 435 1 := ofCheck (by decide +kernel)
theorem slice436 : Span 436 1 := ofCheck (by decide +kernel)
theorem slice437 : Span 437 1 := ofCheck (by decide +kernel)
theorem slice438 : Span 438 1 := ofCheck (by decide +kernel)
theorem slice439 : Span 439 1 := ofCheck (by decide +kernel)
theorem slice440 : Span 440 1 := ofCheck (by decide +kernel)
theorem slice441 : Span 441 1 := ofCheck (by decide +kernel)
theorem slice442 : Span 442 1 := ofCheck (by decide +kernel)
theorem slice443 : Span 443 1 := ofCheck (by decide +kernel)
theorem slice444 : Span 444 1 := ofCheck (by decide +kernel)
theorem slice445 : Span 445 1 := ofCheck (by decide +kernel)
theorem slice446 : Span 446 1 := ofCheck (by decide +kernel)
theorem slice447 : Span 447 1 := ofCheck (by decide +kernel)
theorem slice448 : Span 448 1 := ofCheck (by decide +kernel)
theorem slice449 : Span 449 1 := ofCheck (by decide +kernel)
theorem slice450 : Span 450 1 := ofCheck (by decide +kernel)
theorem slice451 : Span 451 1 := ofCheck (by decide +kernel)
theorem slice452 : Span 452 1 := ofCheck (by decide +kernel)
theorem slice453 : Span 453 1 := ofCheck (by decide +kernel)
theorem slice454 : Span 454 1 := ofCheck (by decide +kernel)
theorem slice455 : Span 455 1 := ofCheck (by decide +kernel)
theorem slice456 : Span 456 1 := ofCheck (by decide +kernel)
theorem slice457 : Span 457 1 := ofCheck (by decide +kernel)
theorem slice458 : Span 458 1 := ofCheck (by decide +kernel)
theorem slice459 : Span 459 1 := ofCheck (by decide +kernel)
theorem slice460 : Span 460 1 := ofCheck (by decide +kernel)
theorem slice461 : Span 461 1 := ofCheck (by decide +kernel)
theorem slice462 : Span 462 1 := ofCheck (by decide +kernel)
theorem slice463 : Span 463 1 := ofCheck (by decide +kernel)
theorem slice464 : Span 464 1 := ofCheck (by decide +kernel)
theorem slice465 : Span 465 1 := ofCheck (by decide +kernel)
theorem slice466 : Span 466 1 := ofCheck (by decide +kernel)
theorem slice467 : Span 467 1 := ofCheck (by decide +kernel)
theorem slice468 : Span 468 1 := ofCheck (by decide +kernel)
theorem slice469 : Span 469 1 := ofCheck (by decide +kernel)
theorem slice470 : Span 470 1 := ofCheck (by decide +kernel)
theorem slice471 : Span 471 1 := ofCheck (by decide +kernel)
theorem slice472 : Span 472 1 := ofCheck (by decide +kernel)
theorem slice473 : Span 473 1 := ofCheck (by decide +kernel)
theorem slice474 : Span 474 1 := ofCheck (by decide +kernel)
theorem slice475 : Span 475 1 := ofCheck (by decide +kernel)
theorem slice476 : Span 476 1 := ofCheck (by decide +kernel)
theorem slice477 : Span 477 1 := ofCheck (by decide +kernel)
theorem slice478 : Span 478 1 := ofCheck (by decide +kernel)
theorem slice479 : Span 479 1 := ofCheck (by decide +kernel)
theorem slice480 : Span 480 1 := ofCheck (by decide +kernel)
theorem ready : Span 0 limit := (join (join (join (join (join (join (join (join slice0 slice5) (join slice10 (join slice14 slice18))) (join (join slice22 slice27) (join slice31 (join slice36 slice40)))) (join (join (join slice44 slice49) (join slice53 (join slice56 slice57))) (join (join slice58 (join slice59 slice60)) (join slice62 (join slice64 slice66))))) (join (join (join (join slice68 slice70) (join slice72 (join slice75 slice76))) (join (join slice77 slice78) (join slice80 (join slice81 slice83)))) (join (join (join slice85 slice90) (join slice92 (join slice96 slice97))) (join (join slice99 (join slice101 slice103)) (join slice105 (join slice107 slice108)))))) (join (join (join (join (join slice111 slice112) (join slice114 (join slice117 slice119))) (join (join slice120 slice123) (join slice126 (join slice128 slice129)))) (join (join (join slice130 slice132) (join slice134 (join slice135 slice138))) (join (join slice140 (join slice142 slice143)) (join slice145 (join slice146 slice148))))) (join (join (join (join slice150 slice152) (join slice154 (join slice157 slice158))) (join (join slice159 slice160) (join slice161 (join slice163 slice168)))) (join (join (join slice169 slice170) (join slice171 (join slice172 slice175))) (join (join slice176 (join slice177 slice178)) (join slice179 (join slice180 slice181))))))) (join (join (join (join (join (join slice183 slice185) (join slice186 (join slice188 slice190))) (join (join slice191 slice192) (join slice193 (join slice196 slice200)))) (join (join (join slice201 slice202) (join slice206 (join slice207 slice208))) (join (join slice210 (join slice212 slice214)) (join slice216 (join slice218 slice220))))) (join (join (join (join slice223 slice225) (join slice227 (join slice228 slice229))) (join (join slice230 slice231) (join slice232 (join slice234 slice236)))) (join (join (join slice238 slice239) (join slice240 (join slice241 slice242))) (join (join slice243 (join slice244 slice245)) (join slice246 (join slice248 slice249)))))) (join (join (join (join (join slice251 slice252) (join slice253 (join slice255 slice256))) (join (join slice257 slice258) (join slice259 (join slice261 slice262)))) (join (join (join slice263 slice264) (join slice266 (join slice268 slice271))) (join (join slice274 (join slice275 slice277)) (join slice278 (join slice279 slice280))))) (join (join (join (join slice282 slice284) (join slice285 (join slice286 slice287))) (join (join slice288 slice289) (join slice290 (join slice291 slice293)))) (join (join (join slice294 slice295) (join slice296 (join slice297 slice298))) (join (join slice300 (join slice301 slice303)) (join slice304 (join slice305 slice307)))))))) (join (join (join (join (join (join (join slice308 slice309) (join slice310 (join slice311 slice313))) (join (join slice314 slice315) (join slice316 (join slice317 slice318)))) (join (join (join slice319 slice320) (join slice321 (join slice322 slice323))) (join (join slice324 (join slice325 slice326)) (join slice327 (join slice328 slice329))))) (join (join (join (join slice330 slice331) (join slice332 (join slice333 slice334))) (join (join slice335 slice336) (join slice337 (join slice338 slice339)))) (join (join (join slice340 slice341) (join slice342 (join slice343 slice344))) (join (join slice345 (join slice346 slice347)) (join slice348 (join slice349 slice350)))))) (join (join (join (join (join slice351 slice354) (join slice355 (join slice356 slice357))) (join (join slice358 slice359) (join slice360 (join slice361 slice362)))) (join (join (join slice363 slice364) (join slice365 (join slice366 slice367))) (join (join slice369 (join slice370 slice371)) (join slice372 (join slice373 slice374))))) (join (join (join (join slice375 slice376) (join slice377 (join slice378 slice379))) (join (join slice380 slice381) (join slice382 (join slice383 slice384)))) (join (join (join slice385 slice386) (join slice387 (join slice388 slice389))) (join (join slice390 (join slice391 slice392)) (join slice393 (join slice394 slice395))))))) (join (join (join (join (join (join slice396 slice397) (join slice398 (join slice399 slice400))) (join (join slice401 slice403) (join slice404 (join slice405 slice406)))) (join (join (join slice407 slice408) (join slice409 (join slice410 slice411))) (join (join slice412 (join slice413 slice414)) (join slice415 (join slice416 slice417))))) (join (join (join (join slice418 slice419) (join slice420 (join slice421 slice422))) (join (join slice423 slice424) (join slice425 (join slice426 slice427)))) (join (join (join slice428 slice429) (join slice430 (join slice431 slice432))) (join (join slice433 (join slice434 slice435)) (join slice436 (join slice437 slice438)))))) (join (join (join (join (join slice439 slice440) (join slice441 (join slice442 slice443))) (join (join slice444 slice445) (join slice446 (join slice447 slice448)))) (join (join (join slice449 slice450) (join slice451 (join slice452 slice453))) (join (join slice454 (join slice455 slice456)) (join slice457 (join slice458 slice459))))) (join (join (join (join slice460 slice461) (join slice462 (join slice463 slice464))) (join (join slice465 slice466) (join slice467 (join slice468 slice469)))) (join (join (join slice470 slice471) (join slice472 (join slice473 slice474))) (join (join slice475 (join slice476 slice477)) (join slice478 (join slice479 slice480)))))))))
end PEqualNP.Outside.L_meta_32632.RowData
namespace PEqualNP.Outside.L_meta_32632.FirstCases
open PEqualNP.Outside.L_meta_32632 PEqualNP.Outside.L_meta_32632.CaseCache
open PEqualNP.Outside.L_meta_32632.RowData (table budget input key watch)
abbrev State := ℕ × List W
def blank : W := ⟨0,0,0,0,0⟩
noncomputable def initial : State :=
  let v := [input 7,input 6,input 4,input 5,input 1,input 3,input 0]
  (pL (table.map (fun e => 16 + (12 - e.2))) - sumc v,v)
def move (st : State) (c : Nat) : State :=
  if c == 0 then st else
    let n := c - 1
    let a := st.2.getD (n % 16) blank
    let b := st.2.getD ((n / 16) % 16) blank
    let keepA := n.testBit 8
    let keepB := n.testBit 9
    let tag := n / 1024
    let unary := tag == 2
    let x := if unary then a.b else if tag == 0 then a.a ||| b.a else a.a &&& b.a
    let y := if unary then a.a else if tag == 0 then a.b &&& b.b else a.b ||| b.b
    let cost := x ||| y
    let v := if unary then a.s ^^^ mz 4 else if tag == 0 then a.s &&& b.s else a.s ||| b.s
    let amount := if unary then st.1 else st.1 + (a.c &&& b.c) - cost
    let z := amount - (if keepA then a.c else 0) - (if !unary && keepB then b.c else 0)
    let rest := st.2.filter (fun w => (keepA || w.s != a.s) && (unary || keepB || w.s != b.s))
    (z, addS ⟨v,x,y,cost,0⟩ rest)
def codesP0 : Array (Nat) := #[3229953,3160338,3369217,3156293,3303698,3160389,3377409,3156327,3311890,3160423,3180869,3172711,7354369,2111762,6375681,3155986,7419905,6441217,2107683,3156003,7489537,5462273,1059124,3156020,7497729,5470465,1059158,3156054,7493633,5466369,1059141,3156037]
def codesP1 : Array (Nat) := #[7501825,5474561,1059175,3156071,3160065,2181377,6306066,7350290,1063220,5396754,7424018,3160116,1063237,5400850,7428114,3160133,1128739,5392658,3225635,7419922,1063254,5404946,7432210,3160150,1063271,5409042,7436306,3160167,1206546,3233810,5257541,7354437]
def codesP2 : Array (Nat) := #[1075542,5273925,7366725,3172438,1075559,5278021,7370821,3172455,3299329,1272065,5253445,7350341,1058919,1063015,1075508,3168308,5265733,7362629,1058902,1062998,1141027,3233827,5261637,7358533,1075303,1075286,1149219,3242019,5261671,7358567,1083717,3176517]
def codesP3 : Array (Nat) := #[5269863,7366759,3307521,1280257,5253479,7350375,1058885,1214738,3242002,5257575,7354471,1062981,2107427,1128483,1083700,3176500,5265767,7362663,1058868,1062964,2107410,6305793,6301714,6371329,6301731,5326866,5257268,5330962,5257285,5326883,5261364,5269556]
def codesP4 : Array (Nat) := #[5265494,5335075,5261398,5339171,5261415,5269573,5269590,5273669,5269607,5392385,5253172,5400577,5253206,5396481,5253189,5404673,5253223,5322787,5322770,5335058,5257302,5339154,5257319,2111489,5265460,5265477,5273652,5265511,1071156,5330979,5261381,1136658]
def codesP5 : Array (Nat) := #[1136675,1202177,1083734,3176534,5273959,7370855,1079365,1144867,5273686,5273703,1079348,1144850,1079382,1210369,770,789,839,773,775,1794,791,1796,1812,1795,1811,1797,1813,1828,1845,1829,1798,1814]
def codesP6 : Array (Nat) := #[1799,1815,1846,1847,1830,1862,1831,1863,1879]
def codesParts := #[codesP0,codesP1,codesP2,codesP3,codesP4,codesP5,codesP6]
def codes (i : Nat) : Nat := ((codesParts.getD (i/32) #[]).getD (i%32) 0)
noncomputable def row (i : ℕ) : Arg :=
  let code := codes i
  let p := move initial (code % 4096)
  let q := move p (code / 4096)
  if i < 174 then (0,13,11,0,q.1,q.2) else (1,13,12,1,q.1,q.2)
def bucketP0 : Array (List Nat) := #[[55],[100],[],[],[],[166],[15,103],[145],[173],[],[],[44],[28,53,165],[],[],[],[197],[],[0,66],[40],[133],[68],[],[],[102],[],[],[2],[],[],[90,108,175],[99]]
def bucketP1 : Array (List Nat) := #[[29],[79],[119],[96],[],[],[117],[],[],[46],[128,143,162],[],[],[],[190],[],[],[],[10],[],[48,93],[126],[],[146,171],[],[17,85],[58,169,199],[],[],[14,147],[],[]]
def bucketP2 : Array (List Nat) := #[[],[86,114],[136],[64],[],[60],[],[],[],[105],[],[],[70,109],[71,148],[],[],[20,33,118],[],[],[9,115],[],[127],[98,168],[13],[113],[88],[65],[95],[3],[7],[],[31]]
def bucketP3 : Array (List Nat) := #[[],[],[],[],[194],[122,167],[],[23,161],[],[],[144],[],[82],[151],[22],[179],[],[],[155],[135],[],[39],[41],[],[19],[186,193],[191],[],[110],[],[12,73,195],[]]
def bucketP4 : Array (List Nat) := #[[8],[],[176],[153],[37],[59,159,164],[],[],[43,101],[],[5,32,132],[],[142],[],[182],[],[63],[11],[],[57],[69],[],[18],[50,116],[107],[16,152],[],[27,172],[],[],[],[]]
def bucketP5 : Array (List Nat) := #[[42,75,77,174],[],[181],[],[187],[138],[],[84],[],[],[81,97],[177,192],[],[92,158],[137],[],[4,26],[],[120],[51,94,170],[],[72,104],[121,178,184,189,196],[],[],[154],[],[36],[6],[45],[],[91]]
def bucketP6 : Array (List Nat) := #[[],[157],[1,54],[89],[78],[21,139],[],[150],[56,198],[],[],[52],[200],[],[30],[185],[106],[83,112],[131,140],[149],[],[],[],[188],[62,124],[163],[180],[35],[25],[],[24],[]]
def bucketP7 : Array (List Nat) := #[[],[],[],[],[],[],[],[130],[111],[],[],[],[183],[],[47,160],[],[34,134],[],[67,80],[],[61],[129],[76],[49,74],[],[38,87],[141],[156],[],[123],[],[125]]
def bucketParts := #[bucketP0,bucketP1,bucketP2,bucketP3,bucketP4,bucketP5,bucketP6,bucketP7]
def bucket (i : Nat) : List Nat := ((bucketParts.getD (i/32) #[]).getD (i%32) [])
def count := 201
noncomputable def covered : Test := fun tag f k t z v =>
  if f == 13 && ((k == 12 && tag == 1) || (k == 11 && tag == 0 && t == 0)) then
    (bucket (key tag k z v)).any (fun i => decide (i < count) && same (tag,f,k,t,z,v) (row i))
  else false
noncomputable def test (v : Arg) : Bool :=
  match v with
  | (tag,f,k,t,z,xs) => st (lz 4) fun l => st (mz 4) fun m => st budget fun g =>
      st z fun b => frc xs fun w => checkpoint watch l m g 13 (tag,f,k,t,b,w)
theorem test_eq (v : Arg) : test v = checkpoint watch (lz 4) (mz 4) budget 13 v := by
  rcases v with ⟨tag,f,k,t,z,xs⟩
  simp only [test,st_eq,frc_eq]
noncomputable def pass (i : ℕ) := !(test (row i))
def Span (a n : ℕ) := ∀ i, a ≤ i → i < a+n → pass i = true
theorem ofCheck {a n : ℕ} (h : (List.range' a n).all pass = true) : Span a n := by
  intro i ha hb
  apply List.all_eq_true.mp h
  simpa [List.mem_range'_1] using And.intro ha hb
theorem join {a b c : ℕ} (ha : Span a b) (hb : Span (a+b) c) : Span a (b+c) := by
  intro i lo hi
  by_cases hh : i < a+b
  · exact ha i lo hh
  · exact hb i (by omega) (by omega)
theorem sound (all : Span 0 count) (previous : Valid watch (lz 4) (mz 4) budget 13) :
    Valid covered (lz 4) (mz 4) budget 13 := by
  intro tag f k t z v tested
  unfold covered at tested
  split at tested <;> try contradiction
  obtain ⟨i,_,he⟩ := List.any_eq_true.mp tested
  obtain ⟨hi,eq⟩ := Bool.and_eq_true_iff.mp he
  have passRow := all i (Nat.zero_le _) (of_decide_eq_true hi)
  rw [(same_iff _ _).mp eq,←checkpoint_eq previous,←test_eq]
  simpa only [pass,Bool.not_eq_true'] using passRow
end PEqualNP.Outside.L_meta_32632.FirstCases
namespace PEqualNP.Outside.L_meta_32632.FirstCases
theorem p0 : Span 0 4 := ofCheck (by decide +kernel)
theorem p4 : Span 4 4 := ofCheck (by decide +kernel)
theorem p8 : Span 8 4 := ofCheck (by decide +kernel)
theorem p12 : Span 12 4 := ofCheck (by decide +kernel)
theorem p16 : Span 16 4 := ofCheck (by decide +kernel)
theorem p20 : Span 20 4 := ofCheck (by decide +kernel)
theorem p24 : Span 24 4 := ofCheck (by decide +kernel)
theorem p28 : Span 28 4 := ofCheck (by decide +kernel)
theorem p32 : Span 32 4 := ofCheck (by decide +kernel)
theorem p36 : Span 36 4 := ofCheck (by decide +kernel)
theorem p40 : Span 40 4 := ofCheck (by decide +kernel)
theorem p44 : Span 44 4 := ofCheck (by decide +kernel)
theorem p48 : Span 48 4 := ofCheck (by decide +kernel)
theorem p52 : Span 52 4 := ofCheck (by decide +kernel)
theorem p56 : Span 56 4 := ofCheck (by decide +kernel)
theorem p60 : Span 60 4 := ofCheck (by decide +kernel)
theorem p64 : Span 64 4 := ofCheck (by decide +kernel)
theorem p68 : Span 68 4 := ofCheck (by decide +kernel)
theorem p72 : Span 72 4 := ofCheck (by decide +kernel)
theorem p76 : Span 76 4 := ofCheck (by decide +kernel)
theorem p80 : Span 80 4 := ofCheck (by decide +kernel)
theorem p84 : Span 84 4 := ofCheck (by decide +kernel)
theorem p88 : Span 88 4 := ofCheck (by decide +kernel)
theorem p92 : Span 92 4 := ofCheck (by decide +kernel)
theorem p96 : Span 96 4 := ofCheck (by decide +kernel)
theorem p100 : Span 100 4 := ofCheck (by decide +kernel)
theorem p104 : Span 104 4 := ofCheck (by decide +kernel)
theorem p108 : Span 108 4 := ofCheck (by decide +kernel)
theorem p112 : Span 112 4 := ofCheck (by decide +kernel)
theorem p116 : Span 116 4 := ofCheck (by decide +kernel)
theorem p120 : Span 120 4 := ofCheck (by decide +kernel)
theorem p124 : Span 124 4 := ofCheck (by decide +kernel)
theorem p128 : Span 128 4 := ofCheck (by decide +kernel)
theorem p132 : Span 132 4 := ofCheck (by decide +kernel)
theorem p136 : Span 136 4 := ofCheck (by decide +kernel)
theorem p140 : Span 140 4 := ofCheck (by decide +kernel)
theorem p144 : Span 144 4 := ofCheck (by decide +kernel)
theorem p148 : Span 148 4 := ofCheck (by decide +kernel)
theorem p152 : Span 152 4 := ofCheck (by decide +kernel)
theorem p156 : Span 156 4 := ofCheck (by decide +kernel)
theorem p160 : Span 160 4 := ofCheck (by decide +kernel)
theorem p164 : Span 164 4 := ofCheck (by decide +kernel)
theorem p168 : Span 168 4 := ofCheck (by decide +kernel)
theorem p172 : Span 172 2 := ofCheck (by decide +kernel)
theorem p174 : Span 174 1 := ofCheck (by decide +kernel)
theorem p175 : Span 175 1 := ofCheck (by decide +kernel)
theorem p176 : Span 176 1 := ofCheck (by decide +kernel)
theorem p177 : Span 177 1 := ofCheck (by decide +kernel)
theorem p178 : Span 178 1 := ofCheck (by decide +kernel)
theorem p179 : Span 179 1 := ofCheck (by decide +kernel)
theorem p180 : Span 180 1 := ofCheck (by decide +kernel)
theorem p181 : Span 181 1 := ofCheck (by decide +kernel)
theorem p182 : Span 182 1 := ofCheck (by decide +kernel)
theorem p183 : Span 183 1 := ofCheck (by decide +kernel)
theorem p184 : Span 184 1 := ofCheck (by decide +kernel)
theorem p185 : Span 185 1 := ofCheck (by decide +kernel)
theorem p186 : Span 186 1 := ofCheck (by decide +kernel)
theorem p187 : Span 187 1 := ofCheck (by decide +kernel)
theorem p188 : Span 188 1 := ofCheck (by decide +kernel)
theorem p189 : Span 189 1 := ofCheck (by decide +kernel)
theorem p190 : Span 190 1 := ofCheck (by decide +kernel)
theorem p191 : Span 191 1 := ofCheck (by decide +kernel)
theorem p192 : Span 192 1 := ofCheck (by decide +kernel)
theorem p193 : Span 193 1 := ofCheck (by decide +kernel)
theorem p194 : Span 194 1 := ofCheck (by decide +kernel)
theorem p195 : Span 195 1 := ofCheck (by decide +kernel)
theorem p196 : Span 196 1 := ofCheck (by decide +kernel)
theorem p197 : Span 197 1 := ofCheck (by decide +kernel)
theorem p198 : Span 198 1 := ofCheck (by decide +kernel)
theorem p199 : Span 199 1 := ofCheck (by decide +kernel)
theorem p200 : Span 200 1 := ofCheck (by decide +kernel)
theorem ready : Span 0 count := (join (join (join (join (join (join p0 p4) (join p8 p12)) (join (join p16 p20) (join p24 p28))) (join (join (join p32 p36) (join p40 p44)) (join (join p48 p52) (join p56 (join p60 p64))))) (join (join (join (join p68 p72) (join p76 p80)) (join (join p84 p88) (join p92 (join p96 p100)))) (join (join (join p104 p108) (join p112 p116)) (join (join p120 p124) (join p128 (join p132 p136)))))) (join (join (join (join (join p140 p144) (join p148 p152)) (join (join p156 p160) (join p164 (join p168 p172)))) (join (join (join p174 p175) (join p176 p177)) (join (join p178 p179) (join p180 (join p181 p182))))) (join (join (join (join p183 p184) (join p185 p186)) (join (join p187 p188) (join p189 (join p190 p191)))) (join (join (join p192 p193) (join p194 p195)) (join (join p196 p197) (join p198 (join p199 p200)))))))
end PEqualNP.Outside.L_meta_32632.FirstCases
namespace PEqualNP.Outside.L_meta_32632.Reduction
open PEqualNP.Outside.L_meta_32632 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_32632.Transfer
lemma budgetSteps (m T : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k u, k ≤ binaryCount gs + u ∧ u ≤ gs.countP isNegGate ∧ Steps m T k u S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i,rfl⟩
    exact ⟨0,0,le_rfl,le_rfl,.done (getD_mem hw h0 i)⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → ∃ k u, k ≤ binaryCount (g::gs) + u ∧ u ≤ (g::gs).countP isNegGate ∧ Steps m T k u S := by
      intro h
      obtain ⟨k,u,hk,hu,st⟩ := ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append,List.mem_singleton] at hx
        exact hx.elim (hw x) (fun e => e ▸ h)) h0 hm hgs hT
      exact ⟨k,u,by simp only [binaryCount,List.countP_cons] at hk ⊢; omega,by simp only [List.countP_cons]; omega,st⟩
    obtain ⟨k,u,hk,hu,go⟩ := ih (w ++ [gv m w g]) (insert (gv m w g) S) (fun x hx => by
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inr (hw x hx)
      · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop,_⟩ := hg g List.mem_cons_self
    obtain ⟨o,l⟩ := g
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact ⟨k+1,u,by simp [binaryCount,List.countP_cons,isBinaryGate,isNegGate] at hk ⊢; omega,by simpa [List.countP_cons,isNegGate] using hu,.bi (d := false) (rd i) (rd j) go⟩
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact ⟨k+1,u,by simp [binaryCount,List.countP_cons,isBinaryGate,isNegGate] at hk ⊢; omega,by simpa [List.countP_cons,isNegGate] using hu,.bi (d := true) (rd i) (rd j) go⟩
    · match l with
      | [] => exact stay hm
      | i :: _ => exact ⟨k+1,u+1,by simp [binaryCount,List.countP_cons,isBinaryGate,isNegGate] at hk ⊢; omega,by simp [List.countP_cons,isNegGate] at hu ⊢; omega,.un (rd i) go⟩

set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
theorem faceBridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, y 2 = false → D.eval (List.ofFn y) = f y) :
    ∃ k u, k ≤ binaryCount D.gates + u ∧ u ≤ D.gates.countP isNegGate ∧ Steps (mz 4) (tz 4) k u (C (mz 4) (WZ [] 4)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 4)
  have hinit_sub : ∀ x ∈ init, x &&& mz 4 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 4) (WZ [] 4) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 4).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 4) gates init).getD out 0 = tz 4 := by
    have ef : EF &&& mz 4 = tz 4 := by decide +kernel
    rw [← ef]
    have hsub : ∀ x ∈ ex (mz 4) gates init, x &&& mz 4 = x := ex_sub (mz 4) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 4 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 4).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 4) hk gates init hD, hinit_bits k hk]
      have zero : rawP.getD 2 0 &&& mz 4 = 0 := by decide +kernel
      have bits := congrArg (fun n : ℕ => n.testBit k) zero
      have bit : row k 2 = false := by simpa [row,Nat.testBit_and,hk] using bits
      have h := hf (row k) bit
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact budgetSteps (mz 4) (tz 4) gates init (C (mz 4) (WZ [] 4))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩
def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def label : Fin 8 → Fin 8 := ![0,1,7,2,3,4,5,6]
def rearranged (x : Fin 8 → Bool) := target (x ∘ label)
def restricted (x : Fin 7 → Bool) := rearranged (Fin.snoc x false)
set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
theorem increasing : ∃ y : Fin 7 → Bool, rearranged (Fin.snoc y true) = true ∧ restricted y = false := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
theorem nonconstant : ∃ y z : Fin 7 → Bool, restricted y ≠ restricted z := by decide +kernel
def witness : List Gate := [
  ⟨.and, [0, 3]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [2, 9]⟩,
  ⟨.and, [5, 10]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [12, 13]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [4, 15]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.and, [7, 17]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.or, [14, 19]⟩,
  ⟨.or, [16, 20]⟩,
  ⟨.or, [18, 21]⟩]
set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
theorem witnessBasis : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [witness]
set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,22⟩ (List.ofFn x) = target x := by decide +kernel
set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
theorem witnessLength : witness.length = 15 := rfl

def project : Fin 7 → Fin 8 := ![0,1,3,4,5,6,7]
set_option maxRecDepth 14000 in
set_option maxHeartbeats 5000000 in
lemma faceEq : ∀ x : Fin 8 → Bool, x 2 = false → restricted (x ∘ project) = f x := by decide +kernel
theorem reduction (grade : HasGrade 1 (4,13))
    (C : Circuit) (fit : FanInTwo C) (n : C.gates.countP isNegGate ≤ 1)
    (ev : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ gs : List Gate, ∃ out : ℕ, (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ C.gates.length ∧ ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x := by
  by_cases large : 15 ≤ C.gates.length
  · exact ⟨witness,22,witnessBasis,witnessLength ▸ large,witnessCorrect⟩
  by_cases has : ∃ g ∈ C.gates, g.op = .not
  · exfalso
    let R := relabel 8 8 label C
    have hR (x : Fin 8 → Bool) : R.eval (List.ofFn x) = rearranged x :=
      (relabelEval label C x).trans (ev (x ∘ label))
    obtain ⟨D,ok,comp,bc,nc⟩ := saveBinaryWithBudget 7 false rearranged R (relabelFan label C fit)
      ((relabelNeg label C).le.trans n) hR increasing nonconstant
    let F := relabel 7 8 project D
    have face (x : Fin 8 → Bool) (zero : x 2 = false) : F.eval (List.ofFn x) = f x :=
      (relabelEval project D x).trans ((comp _).trans (faceEq x zero))
    obtain ⟨k,u,budget,num,steps⟩ := faceBridge F (relabelFan project D ok) face
    have strict := binary_lt_length C.gates has
    have hbr : binaryCount R.gates = binaryCount C.gates := relabelBinary label C
    have hbf : binaryCount F.gates = binaryCount D.gates := relabelBinary project D
    have hnr : R.gates.countP isNegGate = C.gates.countP isNegGate := relabelNeg label C
    have hnf : F.gates.countP isNegGate = D.gates.countP isNegGate := relabelNeg project D
    exact grade k u (by omega) (by change k < 13 + u; omega) steps
  · refine ⟨C.gates,C.output,?_,le_rfl,ev⟩
    intro g hg
    obtain ⟨hop,arity⟩ := fit g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun op => has ⟨g,hg,op⟩)),arity⟩
end PEqualNP.Outside.L_meta_32632.Reduction
namespace PEqualNP.Outside.L_meta_32632.Finish
open PEqualNP.Outside.L_meta_32632 PEqualNP.Outside.L_meta_32632.CaseCache PEqualNP.Outside.L_meta_32632.RowData
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR38 : root FirstCases.covered table 13 1 0x4000000000 0 = false := by decide +kernel
theorem checkedR38 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x4000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR38
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR41 : root FirstCases.covered table 13 1 0x20000000000 0 = false := by decide +kernel
theorem checkedR41 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x20000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR41
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR57 : root FirstCases.covered table 13 1 0x200000000000000 0 = false := by decide +kernel
theorem checkedR57 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x200000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR57
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR75 : root FirstCases.covered table 13 1 0x8000000000000000000 0 = false := by decide +kernel
theorem checkedR75 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x8000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR75
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR90 : root FirstCases.covered table 13 1 0x40000000000000000000000 0 = false := by decide +kernel
theorem checkedR90 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x40000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR91 : root FirstCases.covered table 13 1 0x80000000000000000000000 0 = false := by decide +kernel
theorem checkedR91 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x80000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR91
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR94 : root FirstCases.covered table 13 1 0x400000000000000000000000 0 = false := by decide +kernel
theorem checkedR94 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x400000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR94
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR104 : root FirstCases.covered table 13 1 0x100000000000000000000000000 0 = false := by decide +kernel
theorem checkedR104 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x100000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR104
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR106 : root FirstCases.covered table 13 1 0x400000000000000000000000000 0 = false := by decide +kernel
theorem checkedR106 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x400000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR106
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR124 : root FirstCases.covered table 13 1 0x10000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR124 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x10000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR124
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR127 : root FirstCases.covered table 13 1 0x80000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR127 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x80000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR127
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR138 : root FirstCases.covered table 13 1 0x40000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR138 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x40000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR138
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR140 : root FirstCases.covered table 13 1 0x100000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR140 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x100000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR140
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR141 : root FirstCases.covered table 13 1 0x200000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR141 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x200000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR141
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR143 : root FirstCases.covered table 13 1 0x800000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR143 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x800000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR143
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR157 : root FirstCases.covered table 13 1 0x2000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR157 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x2000000000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR157
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR159 : root FirstCases.covered table 13 1 0x8000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR159 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x8000000000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR159
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR190 : root FirstCases.covered table 13 1 0x400000000000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR190 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x400000000000000000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR190
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR192 : root FirstCases.covered table 13 1 0x1000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR192 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x1000000000000000000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutR206 : root FirstCases.covered table 13 1 0x4000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem checkedR206 (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x4000000000000000000000000000000000000000000000000000 0 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutR206
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutOther : root FirstCases.covered table 13 1 0x3fbffebfffffff5fff4bff6ffffaffb3fff7fffdfffdbfffffffff 1 = false := by decide +kernel
theorem checkedOther (all : Span 0 limit) : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 0x3fbffebfffffff5fff4bff6ffffaffb3fff7fffdfffdbfffffffff 1 = false := (root_eq table 13 1 _ _ (FirstCases.sound FirstCases.ready (soundWatch all))) ▸ cutOther
def cases : List (ℕ × ℕ) := [(0x4000000000,0), (0x20000000000,0), (0x200000000000000,0), (0x8000000000000000000,0), (0x40000000000000000000000,0), (0x80000000000000000000000,0), (0x400000000000000000000000,0), (0x100000000000000000000000000,0), (0x400000000000000000000000000,0), (0x10000000000000000000000000000000,0), (0x80000000000000000000000000000000,0), (0x40000000000000000000000000000000000,0), (0x100000000000000000000000000000000000,0), (0x200000000000000000000000000000000000,0), (0x800000000000000000000000000000000000,0), (0x2000000000000000000000000000000000000000,0), (0x8000000000000000000000000000000000000000,0), (0x400000000000000000000000000000000000000000000000,0), (0x1000000000000000000000000000000000000000000000000,0), (0x4000000000000000000000000000000000000000000000000000,0), (0x3fbffebfffffff5fff4bff6ffffaffb3fff7fffdfffdbfffffffff,1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma covered : mFull cases = true := by decide +kernel
noncomputable def passes (p : ℕ × ℕ) := !BinarySearch.chk [] (pr activeBounds 4) 4 13 1 p.1 p.2
lemma consPass {a : ℕ × ℕ} {xs : List (ℕ × ℕ)} (h : BinarySearch.chk [] (pr activeBounds 4) 4 13 1 a.1 a.2 = false) (t : xs.all passes = true) : (a :: xs).all passes = true := by simp [passes,h,t,List.all_cons] at *
lemma allPass (cert : Span 0 limit) : cases.all passes = true := (consPass (checkedR38 cert) (consPass (checkedR41 cert) (consPass (checkedR57 cert) (consPass (checkedR75 cert) (consPass (checkedR90 cert) (consPass (checkedR91 cert) (consPass (checkedR94 cert) (consPass (checkedR104 cert) (consPass (checkedR106 cert) (consPass (checkedR124 cert) (consPass (checkedR127 cert) (consPass (checkedR138 cert) (consPass (checkedR140 cert) (consPass (checkedR141 cert) (consPass (checkedR143 cert) (consPass (checkedR157 cert) (consPass (checkedR159 cert) (consPass (checkedR190 cert) (consPass (checkedR192 cert) (consPass (checkedR206 cert) (consPass (checkedOther cert) rfl)))))))))))))))))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma hGrade (cert : Span 0 limit) : HasGrade 1 (4,13) := by
  have low := faceFloor
  apply gradeFromFloor (z := 4) (h := 13) (t := 1) low (by decide +kernel) (by decide +kernel)
  intro S sw hl
  refine BinarySearch.rejectMinimum (Q := pr activeBounds 4) (L := 14) (by decide +kernel) (by decide) (by decide) ?_ sw hl low cases covered ?_
  · intro e he
    exact boundsHold e (List.mem_of_mem_filter he)
  · intro e he
    have tested := List.all_eq_true.1 (allPass cert) e he
    simpa only [passes,Bool.not_eq_true'] using tested
end PEqualNP.Outside.L_meta_32632.Finish
theorem PEqualNP.Outside.L_meta_32632 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates out leg uniq ev
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,out⟩
  have fit : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨hop,ar⟩ := leg g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hop, ar⟩
  exact PEqualNP.Outside.L_meta_32632.Reduction.reduction (PEqualNP.Outside.L_meta_32632.Finish.hGrade PEqualNP.Outside.L_meta_32632.RowData.ready) C fit (PEqualNP.Outside.L_meta_32632.Transfer.countNeg_le _ uniq) ev
