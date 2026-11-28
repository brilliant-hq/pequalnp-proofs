import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48482
def bigNat_0 : Nat := 0x7ffdfffbfffbfff5fffbfffbfff5fffd5afffdfffaddaddaefff5ffeafff7fbffeefffbb6edafffefffeb5fffeffff7fff7fff7fffbfffbfffbfff0000000000000000
def bigNat_1 : Nat := 0x8040011000449125000100014a000100008000800080004000400040000000000000000000
def bigNat_2 : Nat := 0x800200040004000a00040004000a0002a5000200052252251000a001500000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0x3fff000000003fff00000180001fff80180180fff1ffe200000849c0127012048125c125c14248c1246092e092e092304970497049600000000000000001cdcb9b8b9b9f374b9b8b9b9f3749cdd5a74dcf9b845a45a27374e6ea7377f80000fff8360dafffefffe34000000007fff7fff00003fffbfffbfffdfeff7fbfdfeff7f
def bigNat_4 : Nat := 0x3fff800000003fff80001fffc40000000001c01c0e0001ffe8000010944625118461225042584004a34251a12821292128d09410949094a0000000000000000276c4ed96ed85db44ed96ed85db4776c4a1b6c2eda9ca9cae1db43b6a1db7f8000e000386e1a0000fffe85fffeffff00007fff7fff80003fffbfffeff7fbfdfeff7fbf
def bigNat_5 : Nat := 0x1fff800000001fff800000001fffd00fffc0000c00c00efff40000000021268049a2a0a8249a84928a0930849ac24d424c424d6126a1262126c000000000000000049b5736a536aa6d5736a536aa6d579b512adb55368c92c92ea6d54daaa6d7fbffe00003b0ec2fffe0000b00000ffff7fff00007fffbfff80003ffff7fbfdfeff7fbfdf
def bigNat_6 : Nat := 0x7ffc000000000001fffbfffbfff4000000fffdfffa000dda0000000000002423b0a8ec000cd88e308e30b51dd08ec047604760477823bc23bc23b0000000000000000072398473847308e5e473e473c8e5a23802ce399c72102dda4c8e591cac8e7fbffeefff800ed800000000b5fffe0000000000007fffbfffbfff8000fb7dbedf6fb7dbed
def bigNat_7 : Nat := 0x7ffdfffbfffbfff4000000000000000000fffdfffadda000000000000000483c30cf0c336000f030f030b5e1e0f0f07878787878603c303c303c30000000000000000073c1e783e783cf05878387830f05c3c002cfc19f82dda1028cf059e0acf07fbffeefffbb600000000000b5fffeffff7fff7fff00000000000000007dbedf6fb7dbedf6
def bigNat_8 : Nat := 0x7ffdfffbfffbfff5fffbfffbfff5fffd5a00000000000000000000000000703fc0eff03b6edaffc0ffc001fe00ff007f807f807f803fc03fc03fc000000000000000007c01f803f803f005f803f803f005fc015af001e0000020020f005e00af007fbffeefffbb6edafffefffe00000000000000000000000000000000007e3f1f8fc7e3f1f8
def bigNat_9 : Nat := 0x7ffdfffbfffbfff5fffbfffbfff5fffd5afffdfffaddaddaefff5ffeafff7fbffeefffbb6edafffefffeb5fffeffff7fff7fff7fffbfffbfffbfffffffffffffffffff
def bigNat_10 : Nat := Nat.lor (Nat.shiftLeft (0x7ffffffffff) 64) 0xffe0000000000000
def bigNat_11 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0xffffffff) 64) 0xfffff80000000000) 64) 0x0
def bigNat_12 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x7ffffff00000000) 64) 0x0) 64) 0x0
def bigNat_13 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xf800000000000000) 64) 0x0) 64) 0x0
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
def NN : Nat := 536
def AA : Nat := bigNat_0
def HX : Nat := bigNat_1
def HY : Nat := bigNat_2
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
def tst0 (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  bif Nat.beq (cov d l v) l then tst0 d l e v F else false
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
def segsX : List (ℕ × ℕ) := [(63, 78), (78, 94), (94, 110), (110, 127), (127, 143), (143, 159), (159, 176), (176, 193), (193, 195), (195, 198), (198, 200), (200, 216), (216, 232), (232, 234), (234, 237), (237, 240), (240, 244), (244, 247), (247, 250), (250, 254), (254, 268), (268, 272), (272, 286), (286, 295)]
def segsY : List (ℕ × ℕ) := [(295, 308), (308, 310), (310, 312), (312, 325), (325, 327), (327, 340), (340, 344), (344, 346), (346, 349), (349, 353), (353, 356), (356, 358), (358, 361), (361, 365), (365, 368), (368, 370), (370, 385), (385, 400), (400, 402), (402, 405), (405, 407), (407, 409), (409, 425), (425, 427), (427, 442), (442, 458), (458, 473), (473, 475), (475, 490), (490, 506), (506, 521), (521, 535)]
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
      obtain ⟨w, hw, hs1⟩ := hm.1.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    simp only [tst, hcov, Bool.cond_true]
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
  have : Std.Symm (fun a c : L_meta_48482.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
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
    {go : (L_meta_48482.X → L_meta_48482.X → Bool) → List L_meta_48482.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_48482.X.s e
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_48482.X → L_meta_48482.X → Bool) → List L_meta_48482.X → Bool,
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_48482.X.s e))
end sound
def rawP : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8]
def xw (e : Nat × Nat) : Nat := if e.1 < 6 then rawP.getD e.1 0 ||| rawP.getD e.2 0 else if e.1 < 12 then rawP.getD (e.1-6) 0 &&& rawP.getD e.2 0 else rawP.getD (e.1-12) 0 ^^^ ((AA ||| (2^64 - 1)) ||| (AA <<< NN))
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5), (8, 3), (8, 4), (8, 5), (9, 4), (9, 5), (10, 5), (12, 0), (13, 0), (14, 0), (15, 0), (16, 0), (17, 0)]
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := bigNat_9
def kz0 (Z : ℕ) : ℕ := (List.range 6).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def oldKz (Z : ℕ) : ℕ := (List.range 6).foldr (fun i x =>
  bif Nat.testBit Z (i + 6) then Nat.lor x (FULL ^^^ (FULL &&& (rawP.getD i 0) &&& ((rawP.getD i 0) >>> NN))) else x) (kz0 Z)
def pairDrops : List Nat := [3775753944726436782911255422352604848834881855238032582722370377290961592794718239577564525123391802848079048295609047576331987017091194202042901961102879260479, 7538206911892416683814110102872875885709575005629030980098383970081107184964865316153514466698034915760131623515978915249961504369300982640130589071350580559711, 14143201919474360833576247783026113550733957152094360236466781045300181745447890976478177965913457346696701057891610428460689574723675018830827792504453888138093, 14720291577344695937156729218472704545033479279910319595029263908683685774051928745907996271725654648693715922822270553010132176333976572451993472455725777874294, 24605901888214403180115454504243883918437718800440277681873871674645985776492990696768451480729258548588000186191322779324051270290382662768955836594506514493816, 1003149158208716147914751196660570585668239233501944416080941135623305593647620257379750585747361153500424562114032468919367320369861190691112085146729453666207, 30012953244519281317086955586528948825729657468983338641998617388753997995551588172518298505061372262743274298135166939111140166161118518845708505498193229208493, 30974912502459217975141396795500916691803093442924588821493214802822981796226748036763991114727408581090806760377223939064227114243673343198692162460830263897526, 31633953189543660790041546769566030108612936579534064978712190470589953841262527700118393403245302875124285042855479442794799518831254228420537604254684300931512, 56404615107217948746405892467528787931345070684461520536398203921769666237258335708095392308862319985831898648716177024349487975543139883640781062083392159849421, 57561328079659003983337144899646721090520702352573736240381948307992174163878921789242729416147250209386459585740157116121727486333508956757404657974062092103126, 63272839735547382312630005219014116898618329291077926900869456480970654285009931701525366975029247341856501901684947971984968365446995458188212203292825496039896, 112464317681867110316801166095159524679936032728777398844212968579744511221604599319799119719862367863865291042251687170027822850813162157922845315361255218989540, 112464264049817017926355560072743103497926185619938751290999425836501178695928990250744912967579236730551199904465894000916651314440853462989922779212611003339240, 112465979856419583256640060906421880131897688555834803112389551575146570583727634986253789460295525969765352142894106608505146061869940205385383433771189459476976, 224945689622416114888732583178303032336523342865616742677351910460201041826008971575734235636181175673570517582495441531888273432633818445748095150123297456259071, 224938878979722234586292028903568609219076308755990751910627144975395227351401941289460096560011574245652161429255892668330694773455541444164855483898872968773631, 113365268559393704820506425282563682251249840872072321847056521697836540495222795434126977730678668668803607112268697292272320212875401121645572817464229944623103, 112589549985305456432390648815555846125879469712903663449871456534895613467927697366032727632244061717899000829271025397172579871453077829808935508972469076623359, 115225712734870749133379754600284848767995853954715421719999770625817934071904001787961914269602590211086307006918165720565964423654786568279281252814233045827583, 224940541364605238274503292680655576291279752512960701851682931492382792262857502501984224077606084276749544400181938213156285364882512559154650086619551820152831, 119955474107109646092583228617588110464847217428469481353882923834697865133690991329750739720772562782311863489163986617629379800395272728642366427450080137052159, 119564397260196960100828909030961438151248492289264636096206706665624150781936680883482029719671589346104016940492194134792858237005036284203636772560988094332927, 112973990386283728263797053638480308517993814702023466036279398069481547676989328815073178563038715980816551219063734588456121800836273670456648149682169929793535, 116214273973712494163727084164135861774415076345709680923190360519954443999946877097961638989922308707290687108836468783616014077023780553856785526316055209705471, 116022053565468597977501204327225242981931212231375917815666770178345360469182025931918723829288867080395273892128701328990335942013639659397739892134027097800703, 114484291961555510554370816478715061124699940537342958245656600284846999867144756148423667684041208879109863250687681058839654933465006556302752457160443455078399, 123038090883322059345529491473862880953464969498399376175997702159922959855581434804460350648200185190961671344260541385349716591821615095135438297986556995043327, 114031201488973975867198687626644635342687329782976199044192884732615627705601136354443764192208984568657730367766401482082075951857709219146084250403012603805695, 112685660085550024371960244368980946656710485956479747366374050233992228795094056461903355655609593818128583534637242898296726665464368439830848078752946128420863]
def kz (Z : Nat) : Nat := if Z < 4096 then oldKz Z else pairDrops.getD (Z-4096) 0
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
    have : Std.Symm (fun a b : L_meta_48482.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_48482.X.s e)) hpb
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
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
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

def rt3 : List (ℕ × ℕ) := [(26, 2), (28, 2), (37, 2), (41, 2), (42, 2), (44, 2), (49, 2), (50, 2), (52, 2), (56, 2), (1600, 2), (1792, 2), (2432, 2), (2624, 2), (2688, 2), (2816, 2), (3136, 2), (3200, 2), (3328, 2), (3584, 2)]
def rt2 : List (ℕ × ℕ) := [(3, 3), (5, 2), (6, 3), (9, 2), (10, 3), (12, 3), (17, 2), (18, 3), (20, 3), (24, 5), (33, 5), (34, 3), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (129, 4), (132, 5), (136, 5), (144, 5), (160, 6), (192, 3), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (320, 3), (384, 2), (513, 5), (514, 5), (516, 5), (528, 4), (544, 5), (576, 3), (640, 2), (768, 3), (1025, 5), (1026, 5), (1028, 5), (1032, 4), (1056, 5), (1088, 3), (1152, 2), (1280, 3), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2112, 3), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def rt1 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def rt : List (ℕ × ℕ) := rt1 ++ rt2 ++ rt3
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3 : rt3.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll (T := []) r3 (by simp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2 : rt2.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1 : rt1.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := okAll r1 (apI i2 i3)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := apI (apI i1 i2) i3
def rStrong := rt1
lemma iStrong : ∀ e ∈ rStrong, Imp [] e.1 e.2 := i1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem strong_p : pOk 0 rStrong = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_p : pOk 0 rt = true := by decide +kernel
def stock (E : List (ℕ × ℕ)) (Z : ℕ) := (rawL E).map (fun w => w &&& mz Z) ++ [0, mz Z]
lemma stock_mem {E : List (ℕ × ℕ)} {Z a : ℕ} : a ∈ stock E Z ↔ a ∈ C (mz Z) (WZ E Z) := by
  simp [stock, C, WZ, eq_comm]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
def exv (e : ℕ × ℕ) (z : ℕ) := xw e &&& mz z
def projb (e : ℕ × ℕ) (z : ℕ) := (stock [] z).contains (exv e z)
lemma extra_sub (e : ℕ × ℕ) (z : ℕ) : C (mz z) (WZ [e] z) ⊆ insert (exv e z) (C (mz z) (WZ [] z)) := by
  rintro a (⟨b, hb, rfl⟩ | hc)
  · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact Or.inr (Or.inl ⟨b, by simpa [rawL] using hb, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inr (Or.inr hc)
def ip (i z : ℕ) := (rawP.getD i 0) &&& mz z
lemma ip_mem (i z : ℕ) : ip i z ∈ C (mz z) (WZ [] z) := by
  by_cases hi : i < rawP.length
  · left
    exact ⟨rawP.getD i 0, by simp only [rawL, List.map_nil, List.append_nil]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _, rfl⟩
  · rw [ip, List.getD_eq_default _ _ (by omega), Nat.zero_and]
    right; simp
def edgeVal (e : ℕ × ℕ) (z : ℕ) := if e.1 < 6 then ip e.1 z ||| ip e.2 z else if e.1 < 12 then ip (e.1 - 6) z &&& ip e.2 z else ip (e.1-12) z ^^^ mz z
def okEdge (e : ℕ × ℕ) (z : ℕ) := edgeVal e z == exv e z
lemma prefixOne {e : ℕ × ℕ} {z q : ℕ} (he : okEdge e z = true) (h : Sol Z0 (mz z) (tz z) q (C (mz z) (WZ [e] z))) :
    Sol Z0 (mz z) (tz z) (q+1) (C (mz z) (WZ [] z)) := by
  have h' := h.mono le_rfl (extra_sub e z)
  have eq : edgeVal e z = exv e z := by simpa [okEdge] using he
  rw [←eq] at h'
  unfold edgeVal at h'
  split at h'
  · exact .bi (d:=true) (ip_mem _ _) (ip_mem _ _) (al0 _ _ _) h'
  · split at h'
    · exact .bi (d:=false) (ip_mem _ _) (ip_mem _ _) (al0 _ _ _) h'
    · exact .un (ip_mem _ _) h'
def lowered (e : ℕ × ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1, if projb e p.1 then p.2 else p.2-1)
lemma giveBound {e : ℕ × ℕ} {p : ℕ × ℕ} (he : okEdge e p.1 = true) (hb : Imp [] p.1 p.2) :
    Imp [e] (lowered e p).1 (lowered e p).2 := by
  intro q hq h
  simp only [lowered] at hq h
  split at hq
  next hz =>
    apply hb q hq
    apply h.mono le_rfl
    intro a ha
    rcases extra_sub e p.1 ha with h' | h'
    · have hv : exv e p.1 ∈ stock [] p.1 := by simpa [projb] using hz
      exact h' ▸ stock_mem.mp hv
    · exact h'
  next => exact hb (q+1) (by omega) (prefixOne he h)
def subsetRows (Q : List (ℕ × ℕ)) (z : ℕ) :=
  Q.filter (fun p => p.1 != z && (mz p.1 &&& mz z) == mz p.1)
lemma subsetRows_mem {Q : List (ℕ × ℕ)} {z : ℕ} {p : ℕ × ℕ} (h : p ∈ subsetRows Q z) : p ∈ Q := List.mem_of_mem_filter h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk0 : okE [] (subsetRows rt 4096) (4096, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk1 : okE [] (subsetRows rt 4097) (4097, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk2 : okE [] (subsetRows rt 4099) (4099, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk3 : okE [] (subsetRows rt 4100) (4100, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk4 : okE [] (subsetRows rt 4101) (4101, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk5 : okE [] (subsetRows rt 4102) (4102, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk6 : okE [] (subsetRows rt 4104) (4104, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk7 : okE [] (subsetRows rt 4107) (4107, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk8 : okE [] (subsetRows rt 4120) (4120, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk9 : okE [] (subsetRows rt 4124) (4124, 11) = true := by decide +kernel
def pairBounds : List (ℕ × ℕ) := [(4096, 11), (4097, 10), (4099, 11), (4100, 11), (4101, 11), (4102, 11), (4104, 11), (4107, 11), (4120, 11), (4124, 11)]
lemma pairValid : ∀ p ∈ pairBounds, Imp [] p.1 p.2 := by
  intro p hp
  simp only [pairBounds, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact imp_okE (Or.inl rfl) pairOk0 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk1 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk2 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk3 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk4 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk5 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk6 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk7 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk8 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk9 (fun q hq => ir q (subsetRows_mem hq))
def allB := rt ++ pairBounds
lemma allValid : ∀ p ∈ allB, Imp [] p.1 p.2 := apI ir pairValid
def qual (b p : ℕ × ℕ) : Bool := b.1 == p.1 && decide (p.2 ≤ b.2)
lemma qualified {E A} {p : ℕ × ℕ} (h : (A : List (ℕ × ℕ)).any (fun b => qual b p) = true)
    (good : ∀ b ∈ A, Imp E b.1 b.2) : Imp E p.1 p.2 := by
  obtain ⟨b,hb,hh⟩ := List.any_eq_true.mp h
  obtain ⟨he,hle⟩ : b.1 = p.1 ∧ p.2 ≤ b.2 := by simpa [qual] using hh
  intro q hq hs
  apply good b hb q (by omega)
  rwa [he]
def lowAll (e : ℕ × ℕ) := allB.map (lowered e)
def lowRt (e : ℕ × ℕ) := rt.map (lowered e)
lemma lowValid {e : ℕ × ℕ} (hE : ∀ p ∈ allB, okEdge e p.1 = true) :
    ∀ p ∈ lowAll e, Imp [e] p.1 p.2 := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  exact giveBound (hE _ ha) (allValid _ ha)
lemma lowRtValid {e : ℕ × ℕ} (h : ∀ p ∈ lowAll e, Imp [e] p.1 p.2) :
    ∀ p ∈ lowRt e, Imp [e] p.1 p.2 := by
  intro p hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  apply h
  exact List.mem_map.mpr ⟨a,List.mem_append_left _ ha,rfl⟩
noncomputable def pass (e : ℕ × ℕ) (Q : List (ℕ × ℕ)) (p : ℕ × ℕ) :=
  (lowAll e).any (fun b => qual b p) ||
    (allB.any (fun b => qual b p) && okE [e] (subsetRows Q p.1) p)
lemma passValid {e p Q} (he : e ∈ six) (lo : ∀ q ∈ lowAll e, Imp [e] q.1 q.2)
    (prev : ∀ q ∈ Q, Imp [e] q.1 q.2) (h : pass e Q p = true) : Imp [e] p.1 p.2 := by
  rcases Bool.or_eq_true_iff.mp h with direct | ind
  · exact qualified direct lo
  · obtain ⟨hb,check⟩ := Bool.and_eq_true_iff.mp ind
    exact imp_okE (Or.inr ⟨e,he,rfl,qualified hb allValid⟩) check (fun q hq => prev q (subsetRows_mem hq))
def ea9 : ℕ × ℕ := (2, 3)
def q2_9 : List (ℕ × ℕ) := [(24, 5), (33, 4), (36, 5), (40, 7), (48, 6), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 4), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 4), (1026, 5), (1028, 5), (1056, 4), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 4), (2304, 5), (2560, 6), (3072, 6)]
def q1_9 : List (ℕ × ℕ) := [(1, 7), (2, 9), (4, 8), (8, 8), (16, 8), (32, 9), (64, 8), (128, 7), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_9 : List (ℕ × ℕ) := [(4120, 11)]
def edgeQ9 := q1_9 ++ q2_9 ++ extra_9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep9 : six.contains ea9 && allB.all (fun p => okEdge ea9 p.1) &&
  q2_9.all (pass ea9 (lowRt ea9)) &&
  q1_9.all (pass ea9 (q2_9 ++ lowRt ea9)) &&
  extra_9.all (fun p => (lowAll ea9).any (fun b => qual b p)) &&
  pOk 0 edgeQ9 && okEdge ea9 0 = true := by decide +kernel
def ea13 : ℕ × ℕ := (3, 5)
def q2_13 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 7), (66, 5), (68, 5), (72, 5), (80, 4), (96, 5), (132, 4), (136, 5), (144, 4), (160, 6), (257, 5), (258, 5), (264, 5), (272, 4), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_13 : List (ℕ × ℕ) := [(1, 8), (2, 8), (4, 8), (8, 8), (16, 7), (32, 10), (64, 8), (128, 7), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_13 : List (ℕ × ℕ) := [(4124, 11)]
def edgeQ13 := q1_13 ++ q2_13 ++ extra_13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep13 : six.contains ea13 && allB.all (fun p => okEdge ea13 p.1) &&
  q2_13.all (pass ea13 (lowRt ea13)) &&
  q1_13.all (pass ea13 (q2_13 ++ lowRt ea13)) &&
  extra_13.all (fun p => (lowAll ea13).any (fun b => qual b p)) &&
  pOk 0 edgeQ13 && okEdge ea13 0 = true := by decide +kernel
def ea15 : ℕ × ℕ := (6, 1)
def q2_15 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 6), (48, 6), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 4), (513, 5), (514, 5), (516, 4), (544, 5), (1025, 5), (1026, 5), (1028, 4), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 4), (2056, 4), (2064, 4), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_15 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 7), (8, 8), (16, 8), (32, 9), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_15 : List (ℕ × ℕ) := [(4096, 11)]
def edgeQ15 := q1_15 ++ q2_15 ++ extra_15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep15 : six.contains ea15 && allB.all (fun p => okEdge ea15 p.1) &&
  q2_15.all (pass ea15 (lowRt ea15)) &&
  q1_15.all (pass ea15 (q2_15 ++ lowRt ea15)) &&
  extra_15.all (fun p => (lowAll ea15).any (fun b => qual b p)) &&
  pOk 0 edgeQ15 && okEdge ea15 0 = true := by decide +kernel
def ea16 : ℕ × ℕ := (6, 2)
def q2_16 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 6), (48, 6), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 4), (516, 5), (544, 4), (1025, 5), (1026, 4), (1028, 5), (1056, 4), (1536, 4), (2049, 6), (2050, 4), (2052, 5), (2056, 4), (2064, 4), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_16 : List (ℕ × ℕ) := [(1, 8), (2, 8), (4, 8), (8, 8), (16, 8), (32, 9), (64, 9), (128, 8), (256, 8), (512, 7), (1024, 7), (2048, 9)]
def extra_16 : List (ℕ × ℕ) := [(4097, 10)]
def edgeQ16 := q1_16 ++ q2_16 ++ extra_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep16 : six.contains ea16 && allB.all (fun p => okEdge ea16 p.1) &&
  q2_16.all (pass ea16 (lowRt ea16)) &&
  q1_16.all (pass ea16 (q2_16 ++ lowRt ea16)) &&
  extra_16.all (fun p => (lowAll ea16).any (fun b => qual b p)) &&
  pOk 0 edgeQ16 && okEdge ea16 0 = true := by decide +kernel
def ea18 : ℕ × ℕ := (6, 4)
def q2_18 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 4), (40, 6), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 4), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_18 : List (ℕ × ℕ) := [(1, 8), (2, 8), (4, 8), (8, 8), (16, 8), (32, 9), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_18 : List (ℕ × ℕ) := [(4099, 11)]
def edgeQ18 := q1_18 ++ q2_18 ++ extra_18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep18 : six.contains ea18 && allB.all (fun p => okEdge ea18 p.1) &&
  q2_18.all (pass ea18 (lowRt ea18)) &&
  q1_18.all (pass ea18 (q2_18 ++ lowRt ea18)) &&
  extra_18.all (fun p => (lowAll ea18).any (fun b => qual b p)) &&
  pOk 0 edgeQ18 && okEdge ea18 0 = true := by decide +kernel
def ea19 : ℕ × ℕ := (6, 5)
def q2_19 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 4), (544, 5), (1025, 5), (1026, 5), (1028, 4), (1056, 5), (1536, 4), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_19 : List (ℕ × ℕ) := [(1, 8), (2, 8), (4, 7), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_19 : List (ℕ × ℕ) := [(4100, 11)]
def edgeQ19 := q1_19 ++ q2_19 ++ extra_19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep19 : six.contains ea19 && allB.all (fun p => okEdge ea19 p.1) &&
  q2_19.all (pass ea19 (lowRt ea19)) &&
  q1_19.all (pass ea19 (q2_19 ++ lowRt ea19)) &&
  extra_19.all (fun p => (lowAll ea19).any (fun b => qual b p)) &&
  pOk 0 edgeQ19 && okEdge ea19 0 = true := by decide +kernel
def ea20 : ℕ × ℕ := (7, 2)
def q2_20 : List (ℕ × ℕ) := [(24, 4), (33, 5), (36, 5), (40, 6), (48, 6), (66, 6), (68, 6), (72, 4), (80, 4), (96, 4), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 4), (514, 5), (516, 5), (544, 5), (1025, 4), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 4), (2064, 4), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_20 : List (ℕ × ℕ) := [(1, 7), (2, 9), (4, 8), (8, 7), (16, 7), (32, 9), (64, 8), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_20 : List (ℕ × ℕ) := [(4101, 11)]
def edgeQ20 := q1_20 ++ q2_20 ++ extra_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep20 : six.contains ea20 && allB.all (fun p => okEdge ea20 p.1) &&
  q2_20.all (pass ea20 (lowRt ea20)) &&
  q1_20.all (pass ea20 (q2_20 ++ lowRt ea20)) &&
  extra_20.all (fun p => (lowAll ea20).any (fun b => qual b p)) &&
  pOk 0 edgeQ20 && okEdge ea20 0 = true := by decide +kernel
def ea21 : ℕ × ℕ := (7, 3)
def q2_21 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 6), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 4), (258, 6), (264, 5), (272, 4), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 4), (1026, 5), (1028, 4), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 4), (2176, 5), (2304, 4), (2560, 6), (3072, 6)]
def q1_21 : List (ℕ × ℕ) := [(1, 7), (2, 9), (4, 8), (8, 8), (16, 8), (32, 9), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 7), (2048, 9)]
def extra_21 : List (ℕ × ℕ) := [(4102, 11)]
def edgeQ21 := q1_21 ++ q2_21 ++ extra_21
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep21 : six.contains ea21 && allB.all (fun p => okEdge ea21 p.1) &&
  q2_21.all (pass ea21 (lowRt ea21)) &&
  q1_21.all (pass ea21 (q2_21 ++ lowRt ea21)) &&
  extra_21.all (fun p => (lowAll ea21).any (fun b => qual b p)) &&
  pOk 0 edgeQ21 && okEdge ea21 0 = true := by decide +kernel
def ea23 : ℕ × ℕ := (7, 5)
def q2_23 : List (ℕ × ℕ) := [(24, 4), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_23 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_23 : List (ℕ × ℕ) := [(4104, 11)]
def edgeQ23 := q1_23 ++ q2_23 ++ extra_23
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep23 : six.contains ea23 && allB.all (fun p => okEdge ea23 p.1) &&
  q2_23.all (pass ea23 (lowRt ea23)) &&
  q1_23.all (pass ea23 (q2_23 ++ lowRt ea23)) &&
  extra_23.all (fun p => (lowAll ea23).any (fun b => qual b p)) &&
  pOk 0 edgeQ23 && okEdge ea23 0 = true := by decide +kernel
def ea26 : ℕ × ℕ := (8, 5)
def q2_26 : List (ℕ × ℕ) := [(24, 4), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 4), (514, 5), (516, 5), (544, 5), (1025, 4), (1026, 5), (1028, 5), (1056, 5), (1536, 4), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_26 : List (ℕ × ℕ) := [(1, 7), (2, 8), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_26 : List (ℕ × ℕ) := [(4107, 11)]
def edgeQ26 := q1_26 ++ q2_26 ++ extra_26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep26 : six.contains ea26 && allB.all (fun p => okEdge ea26 p.1) &&
  q2_26.all (pass ea26 (lowRt ea26)) &&
  q1_26.all (pass ea26 (q2_26 ++ lowRt ea26)) &&
  extra_26.all (fun p => (lowAll ea26).any (fun b => qual b p)) &&
  pOk 0 edgeQ26 && okEdge ea26 0 = true := by decide +kernel
def ea27 : ℕ × ℕ := (9, 4)
def q2_27 : List (ℕ × ℕ) := [(24, 5), (33, 4), (36, 4), (40, 7), (48, 7), (66, 5), (68, 5), (72, 5), (80, 5), (96, 5), (132, 4), (136, 5), (144, 5), (160, 6), (257, 4), (258, 5), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 4), (2052, 4), (2056, 5), (2064, 5), (2176, 4), (2304, 4), (2560, 6), (3072, 6)]
def q1_27 : List (ℕ × ℕ) := [(1, 7), (2, 8), (4, 7), (8, 8), (16, 8), (32, 9), (64, 8), (128, 7), (256, 7), (512, 8), (1024, 8), (2048, 9)]
def extra_27 : List (ℕ × ℕ) := []
def edgeQ27 := q1_27 ++ q2_27 ++ extra_27
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep27 : six.contains ea27 && allB.all (fun p => okEdge ea27 p.1) &&
  q2_27.all (pass ea27 (lowRt ea27)) &&
  q1_27.all (pass ea27 (q2_27 ++ lowRt ea27)) &&
  extra_27.all (fun p => (lowAll ea27).any (fun b => qual b p)) &&
  pOk 0 edgeQ27 && okEdge ea27 0 = true := by decide +kernel
def ea30 : ℕ × ℕ := (12, 0)
def q2_30 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_30 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_30 : List (ℕ × ℕ) := []
def edgeQ30 := q1_30 ++ q2_30 ++ extra_30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep30 : six.contains ea30 && allB.all (fun p => okEdge ea30 p.1) &&
  q2_30.all (pass ea30 (lowRt ea30)) &&
  q1_30.all (pass ea30 (q2_30 ++ lowRt ea30)) &&
  extra_30.all (fun p => (lowAll ea30).any (fun b => qual b p)) &&
  pOk 0 edgeQ30 && okEdge ea30 0 = true := by decide +kernel
def ea32 : ℕ × ℕ := (14, 0)
def q2_32 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_32 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_32 : List (ℕ × ℕ) := []
def edgeQ32 := q1_32 ++ q2_32 ++ extra_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep32 : six.contains ea32 && allB.all (fun p => okEdge ea32 p.1) &&
  q2_32.all (pass ea32 (lowRt ea32)) &&
  q1_32.all (pass ea32 (q2_32 ++ lowRt ea32)) &&
  extra_32.all (fun p => (lowAll ea32).any (fun b => qual b p)) &&
  pOk 0 edgeQ32 && okEdge ea32 0 = true := by decide +kernel
def ea34 : ℕ × ℕ := (16, 0)
def q2_34 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_34 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_34 : List (ℕ × ℕ) := []
def edgeQ34 := q1_34 ++ q2_34 ++ extra_34
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep34 : six.contains ea34 && allB.all (fun p => okEdge ea34 p.1) &&
  q2_34.all (pass ea34 (lowRt ea34)) &&
  q1_34.all (pass ea34 (q2_34 ++ lowRt ea34)) &&
  extra_34.all (fun p => (lowAll ea34).any (fun b => qual b p)) &&
  pOk 0 edgeQ34 && okEdge ea34 0 = true := by decide +kernel
def ea35 : ℕ × ℕ := (17, 0)
def q2_35 : List (ℕ × ℕ) := [(24, 5), (33, 5), (36, 5), (40, 7), (48, 7), (66, 6), (68, 6), (72, 5), (80, 5), (96, 5), (132, 5), (136, 5), (144, 5), (160, 6), (257, 5), (258, 6), (264, 5), (272, 5), (288, 5), (513, 5), (514, 5), (516, 5), (544, 5), (1025, 5), (1026, 5), (1028, 5), (1056, 5), (1536, 5), (2049, 6), (2050, 5), (2052, 5), (2056, 5), (2064, 5), (2176, 5), (2304, 5), (2560, 6), (3072, 6)]
def q1_35 : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 9)]
def extra_35 : List (ℕ × ℕ) := []
def edgeQ35 := q1_35 ++ q2_35 ++ extra_35
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep35 : six.contains ea35 && allB.all (fun p => okEdge ea35 p.1) &&
  q2_35.all (pass ea35 (lowRt ea35)) &&
  q1_35.all (pass ea35 (q2_35 ++ lowRt ea35)) &&
  extra_35.all (fun p => (lowAll ea35).any (fun b => qual b p)) &&
  pOk 0 edgeQ35 && okEdge ea35 0 = true := by decide +kernel
lemma combOr {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by simpa only [Bool.or_eq_true] using h
lemma combAnd {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa only [Bool.and_eq_true] using h
def unaryE (e : ℕ × ℕ) : Bool := decide (12 ≤ e.1)
def remT (n : Bool) (t : ℕ) := if n then t-1 else t
def classifyB (n : Bool) (a : ℕ) := (stock [] 0).contains a ||
  six.any (fun e => unaryE e == n && exv e 0 == a)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma classified : (stock [] 0).all (fun a => classifyB true (a ^^^ mz 0) &&
  (stock [] 0).all (fun b => classifyB false (a &&& b) && classifyB false (a ||| b))) = true := by decide +kernel
lemma stock_extend (e : ℕ × ℕ) : C (mz 0) (WZ [] 0) ⊆ C (mz 0) (WZ [e] 0) := by
  rintro a (⟨b, hb, rfl⟩ | hc)
  · left
    exact ⟨b, by simp only [rawL, List.mem_append]; left; simpa [rawL] using hb, rfl⟩
  · exact Or.inr hc
def Excluded (e : ℕ × ℕ) (t : ℕ) := ∀ (S : Finset ℕ), (S : Set ℕ) ⊆ C (mz 0) (WZ [e] 0) →
  ¬ Live Z0 (mz 0) (tz 0) 12 t S
lemma nextExcluded {t : ℕ} (base : Imp [] 0 13)
    (no : ∀ e ∈ six, Excluded e (remT (unaryE e) t)) {n : Bool} {s : ℕ} {U : Finset ℕ}
    (tail : Live Z0 (mz 0) (tz 0) 12 (remT n t) (insert s U))
    (keep : (U : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) (hc : classifyB n s = true) : False := by
  rcases combOr hc with hs | he
  · apply base 12 (by omega)
    apply tail.sol.mono le_rfl
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | h
    · exact stock_mem.mp (by simpa using hs)
    · exact keep h
  · obtain ⟨e, he, hit⟩ := List.any_eq_true.mp he
    obtain ⟨hn, hw⟩ : unaryE e = n ∧ exv e 0 = s := by simpa using hit
    apply no e he (insert s U)
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | h
      · left
        exact ⟨xw e, by simp [rawL], hw.symm⟩
      · exact stock_extend e (keep h)
    · simpa [hn] using tail
lemma firstExcluded {t : ℕ} (base : Imp [] 0 13)
    (no : ∀ e ∈ six, Excluded e (remT (unaryE e) t)) {S : Finset ℕ}
    (avail : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) (hl : Live Z0 (mz 0) (tz 0) 13 t S) : False := by
  have hset := List.all_eq_true.mp classified
  cases hl with
  | @un k t a U rest =>
    have ha : a ∈ stock [] 0 := stock_mem.mpr (avail (by simp))
    apply nextExcluded base no (n:=true) (s:=a ^^^ mz 0) (U:=U)
    · simpa [remT] using rest
    · intro x hx; apply avail; exact Finset.mem_insert_of_mem hx
    · exact (combAnd (hset a ha)).1
  | @bi k t d a b U hne hal rest =>
    have ha : a ∈ stock [] 0 := stock_mem.mpr (avail (by simp))
    have hb : b ∈ stock [] 0 := stock_mem.mpr (avail (by simp))
    apply nextExcluded base no (n:=false) (s:=op d a b) (U:=U)
    · simpa [remT] using rest
    · intro x hx; apply avail; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    · have hpair := combAnd ((List.all_eq_true.mp (combAnd (hset a ha)).2) b hb)
      cases d
      · exact hpair.1
      · exact hpair.2
structure WireAction where
  fn : ℕ → ℕ
  flip : Bool → Bool
  targetEq : fn (tz 0) = tz 0
  neg : ∀ a, fn (a ^^^ mz 0) = fn a ^^^ mz 0
  gate : ∀ d a b, fn (op d a b) = op (flip d) (fn a) (fn b)
  flip2 : ∀ d, flip (flip d) = d
lemma mapLive (A : WireAction) {k t : ℕ} {S : Finset ℕ} (h : Live Z0 (mz 0) (tz 0) k t S)
    (undo : ∀ a ∈ S, A.fn (A.fn a) = a) :
    Live Z0 (mz 0) (tz 0) k t (S.image A.fn) := by
  induction h with
  | stop => simpa [A.targetEq] using (Live.stop : Live Z0 (mz 0) (tz 0) 0 0 {tz 0})
  | @un k t a U _ ih =>
    have hu : ∀ u ∈ U, A.fn (A.fn u) = u := fun u h => undo _ (Finset.mem_insert_of_mem h)
    have ha := undo a (Finset.mem_insert_self a U)
    have next := ih (by
      intro u h
      rcases Finset.mem_insert.mp h with rfl | h
      · rw [A.neg, A.neg, ha]
      · exact hu _ h)
    rw [Finset.image_insert, A.neg] at next
    rw [Finset.image_insert]
    exact .un next
  | @bi k t d a b U hab _ _ ih =>
    have ha := undo a (Finset.mem_insert_self _ _)
    have hb := undo b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have next := ih (by
      intro u h
      rcases Finset.mem_insert.mp h with rfl | h
      · rw [A.gate, A.gate, A.flip2, ha, hb]
      · exact undo _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
    have ne : A.fn a ≠ A.fn b := fun he => hab (ha.symm.trans ((congrArg A.fn he).trans hb))
    rw [Finset.image_insert, A.gate] at next
    rw [Finset.image_insert, Finset.image_insert]
    exact .bi ne (al0 _ _ _) next
def mapChecks (f : ℕ → ℕ) (e e' : ℕ × ℕ) : Bool :=
  (stock [e] 0).all fun a => (stock [e'] 0).contains (f a) && (f (f a) == a)
lemma pullExcluded (A : WireAction) {e e' : ℕ × ℕ} {t : ℕ}
    (hc : mapChecks A.fn e e' = true) (done : Excluded e' t) : Excluded e t := by
  intro S hs hl
  have good := List.all_eq_true.mp hc
  have ok (a) (ha : a ∈ S) : A.fn a ∈ stock [e'] 0 ∧ A.fn (A.fn a) = a := by
    have h := good _ (stock_mem.mpr (hs ha))
    simpa using h
  apply done (S.image A.fn)
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact stock_mem.mp (ok _ ha).1
  · exact mapLive A hl (fun a ha => (ok a ha).2)
def gather (xs : List ℕ) (w : ℕ) : ℕ := xs.foldr (fun i r => Nat.bit (w.testBit i) r) 0
lemma gatherOr (xs : List ℕ) (a b : ℕ) : gather xs (a ||| b) = (gather xs a ||| gather xs b) := by
  induction xs with
  | nil => simp [gather]
  | cons x xs ih => change Nat.bit _ (gather xs (a ||| b)) = Nat.bit _ _ ||| Nat.bit _ _; rw [Nat.lor_bit, Nat.testBit_or, ih]; rfl
lemma gatherAnd (xs : List ℕ) (a b : ℕ) : gather xs (a &&& b) = (gather xs a &&& gather xs b) := by
  induction xs with
  | nil => simp [gather]
  | cons x xs ih => change Nat.bit _ (gather xs (a &&& b)) = Nat.bit _ _ &&& Nat.bit _ _; rw [Nat.land_bit, Nat.testBit_and, ih]; rfl
lemma gatherXor (xs : List ℕ) (a b : ℕ) : gather xs (a ^^^ b) = (gather xs a ^^^ gather xs b) := by
  induction xs with
  | nil => simp [gather]
  | cons x xs ih => change Nat.bit _ (gather xs (a ^^^ b)) = Nat.bit _ _ ^^^ Nat.bit _ _; rw [Nat.xor_bit, Nat.testBit_xor, ih]; rfl
def rew (xs : List ℕ) (a : ℕ) := gather xs a &&& mz 0
lemma rew_op (xs : List ℕ) (d : Bool) (a b : ℕ) : rew xs (op d a b) = op d (rew xs a) (rew xs b) := by
  cases d <;> unfold rew op <;> simp only [Bool.false_eq_true, cond_false, cond_true, gatherOr, gatherAnd] <;>
    apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases (gather xs a).testBit i <;> cases (gather xs b).testBit i <;> cases (mz 0).testBit i <;> rfl
lemma rew_xor (xs : List ℕ) (a b : ℕ) : rew xs (a ^^^ b) = rew xs a ^^^ rew xs b := by
  unfold rew
  rw [gatherXor]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases (gather xs a).testBit i <;> cases (gather xs b).testBit i <;> cases (mz 0).testBit i <;> rfl
def twist (inv : Bool) (xs : List ℕ) (a : ℕ) := bif inv then rew xs a ^^^ mz 0 else rew xs a
def twisted (inv : Bool) (xs : List ℕ) (hm : rew xs (mz 0) = mz 0)
    (ht : twist inv xs (tz 0) = tz 0) : WireAction where
  fn := twist inv xs
  flip := fun d => bif inv then !d else d
  targetEq := ht
  neg := by
    intro a
    cases inv <;> simp [twist, rew_xor, hm]
  gate := by
    intro d a b
    cases inv with
    | false => exact rew_op xs d a b
    | true =>
      simp only [twist, cond_true, rew_op]
      apply Nat.eq_of_testBit_eq; intro i
      cases d <;> simp only [op, cond_true, cond_false, Bool.not_false, Bool.not_true, rew,
        Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
        cases (gather xs a).testBit i <;> cases (gather xs b).testBit i <;> cases (mz 0).testBit i <;> rfl
  flip2 := by intro d; cases inv <;> cases d <;> rfl
def mapPool := rawP.map (fun a => a &&& mz 0) ++ [0,mz 0] ++ six.map (fun e => xw e &&& mz 0)
def factTable (kv : List (ℕ × ℕ)) := kv.map (fun (i,j) => (mapPool.getD i 0, mapPool.getD j 0))
def acceptedFacts (F : ℕ → ℕ) (tab : List (ℕ × ℕ)) := tab.all fun (a,b) => F a == b
def useFacts (tab : List (ℕ × ℕ)) (e e' : ℕ × ℕ) :=
  (stock [e] 0).all fun a => tab.any fun (u,v) => u == a && (stock [e'] 0).contains v && tab.contains (v,u)
lemma liftFacts {F : ℕ → ℕ} {tab : List (ℕ × ℕ)} {e e' : ℕ × ℕ}
    (checked : acceptedFacts F tab = true) (use : useFacts tab e e' = true) : mapChecks F e e' = true := by
  apply List.all_eq_true.mpr; intro a ha
  obtain ⟨⟨u,v⟩,hu,huse⟩ := List.any_eq_true.mp (List.all_eq_true.mp use a ha)
  obtain ⟨⟨rfl,hv⟩,hvu⟩ : (u = a ∧ v ∈ stock [e'] 0) ∧ (v,u) ∈ tab := by simpa using huse
  have h1 : F u = v := by simpa using List.all_eq_true.mp checked (u,v) hu
  have h2 : F v = u := by simpa using List.all_eq_true.mp checked (v,u) hvu
  simp [h1,h2,hv]
def lplain : List ℕ := [55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 63, 56, 58, 57, 59, 60, 61, 474, 55, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 1073, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 1073, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 1073, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 1073, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 1073, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 1073, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 1073, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 1073, 379, 1073, 394, 394, 1073, 395, 1073, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 1073, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 1073, 420, 1073, 501, 501, 1073, 517, 517, 1073, 518, 518, 518, 1073, 453, 453, 1073, 469, 469, 1073, 470, 470, 470, 1073, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 1073, 533, 533, 533, 1073, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 1073, 474, 474, 474, 474, 474, 474, 474, 474, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 532, 534, 1073, 474, 1073, 474, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 532, 534, 1073, 474, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 532, 534, 1073, 522, 528, 525, 1073, 474, 1073, 526, 527, 1073, 526, 528, 529, 1073, 527, 528, 1073, 474, 1073, 523, 524, 1073, 523, 525, 529, 1073, 524, 525, 1073, 529, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 379, 394, 530, 531, 532, 534, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 394, 395, 530, 531, 532, 534, 1073, 474, 1073, 530, 531, 1073, 530, 1073, 531, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 420, 518, 470, 532, 534, 1073, 474, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 501, 517, 532, 534, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 501, 518, 532, 533, 534, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 517, 518, 532, 534, 1073, 474, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 453, 469, 532, 534, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 453, 470, 532, 533, 534, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 469, 470, 532, 534, 1073, 522, 526, 527, 528, 523, 524, 525, 529, 530, 531, 532, 533, 534, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 843, 860, 875, 879, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 896, 900, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 896, 903, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 879, 900, 903, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 884, 888, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 884, 891, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 879, 888, 891, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 900, 888, 905, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 920, 1073, 920, 935, 1073, 935, 1073, 843, 860, 875, 920, 935, 940, 942, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 843, 860, 875, 920, 935, 940, 944, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 960, 1073, 1025, 1041, 1073, 1025, 1056, 1073, 960, 1041, 1056, 1073, 977, 993, 1073, 977, 1008, 1073, 960, 993, 1008, 1073, 843, 860, 875, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 1041, 993, 1070, 1073, 843, 860, 875, 920, 935, 960, 1025, 1041, 1056, 977, 993, 1008, 1070, 1073, 845, 847, 862, 893, 881, 937, 1010, 962, 1073, 843, 843, 843, 843, 843, 843, 843, 843, 843, 843, 843, 843, 1073, 845, 1073, 847, 1073, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 1073, 862, 1073, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 1073, 879, 879, 879, 1073, 893, 1073, 896, 896, 1073, 900, 900, 900, 1073, 903, 903, 1073, 881, 1073, 884, 884, 1073, 888, 888, 888, 1073, 891, 891, 1073, 905, 1073, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 1073, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 1073, 937, 1073, 940, 940, 1073, 942, 1073, 944, 1073, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 1073, 1010, 1073, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1073, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1073, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1073, 962, 1073, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 1073, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 1073, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1073, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1073]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mplain : rew lplain (mz 0) = mz 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tplain : twist false lplain (tz 0) = tz 0 := by decide +kernel
def actplain := twisted false lplain mplain tplain
def tblplain := factTable [(0, 0), (1, 1), (2, 2), (3, 4), (4, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 11), (11, 10), (12, 12), (13, 13), (14, 15), (15, 14), (16, 16), (17, 18), (18, 17), (19, 19), (20, 20), (21, 22), (22, 21), (23, 23), (24, 24), (25, 26), (26, 25), (27, 27), (28, 28), (29, 30), (30, 29), (31, 31), (32, 33), (33, 32), (34, 34), (35, 35), (36, 37), (37, 36), (38, 38), (39, 39), (40, 40), (41, 42), (42, 41), (43, 43)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma factsplain : acceptedFacts actplain.fn tblplain = true := by decide +kernel
def ldual : List ℕ := [1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 962, 937, 893, 881, 862, 845, 847, 843, 1010, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1073, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1073, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1073, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1073, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1073, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 1073, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 1073, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 1073, 944, 1073, 940, 940, 1073, 942, 1073, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 1073, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 1073, 905, 1073, 903, 903, 1073, 896, 896, 1073, 900, 900, 900, 1073, 891, 891, 1073, 884, 884, 1073, 888, 888, 888, 1073, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 1073, 879, 879, 879, 1073, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 1073, 843, 843, 843, 843, 843, 843, 843, 843, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 875, 860, 1073, 843, 1073, 843, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 875, 860, 1073, 843, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 875, 860, 1073, 1070, 1041, 993, 1073, 843, 1073, 1056, 1025, 1073, 1056, 1041, 960, 1073, 1025, 1041, 1073, 843, 1073, 1008, 977, 1073, 1008, 993, 960, 1073, 977, 993, 1073, 960, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 944, 940, 935, 920, 875, 860, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 940, 942, 935, 920, 875, 860, 1073, 843, 1073, 935, 920, 1073, 935, 1073, 920, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 905, 900, 888, 875, 860, 1073, 843, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 903, 896, 875, 860, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 903, 900, 875, 879, 860, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 896, 900, 875, 860, 1073, 843, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 891, 884, 875, 860, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 891, 888, 875, 879, 860, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 884, 888, 875, 860, 1073, 1070, 1056, 1025, 1041, 1008, 977, 993, 960, 935, 920, 875, 879, 860, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 474, 534, 532, 533, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 517, 518, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 517, 501, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 533, 518, 501, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 469, 470, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 469, 453, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 533, 470, 453, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 518, 470, 420, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 531, 1073, 531, 530, 1073, 530, 1073, 474, 534, 532, 531, 530, 394, 395, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 474, 534, 532, 531, 530, 394, 379, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 529, 1073, 527, 528, 1073, 527, 526, 1073, 529, 528, 526, 1073, 524, 525, 1073, 524, 523, 1073, 529, 525, 523, 1073, 474, 534, 532, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 528, 525, 522, 1073, 474, 534, 532, 531, 530, 529, 527, 528, 526, 524, 525, 523, 522, 1073, 60, 61, 59, 58, 57, 56, 55, 63, 1073, 474, 474, 474, 474, 474, 474, 474, 474, 474, 474, 474, 474, 1073, 60, 1073, 61, 1073, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 1073, 59, 1073, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 1073, 533, 533, 533, 1073, 58, 1073, 517, 517, 1073, 518, 518, 518, 1073, 501, 501, 1073, 57, 1073, 469, 469, 1073, 470, 470, 470, 1073, 453, 453, 1073, 420, 1073, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 1073, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 1073, 56, 1073, 394, 394, 1073, 395, 1073, 379, 1073, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 1073, 55, 1073, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 1073, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 1073, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 1073, 63, 1073, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 1073, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 1073, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 1073, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 1073]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mdual : rew ldual (mz 0) = mz 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tdual : twist true ldual (tz 0) = tz 0 := by decide +kernel
def actdual := twisted true ldual mdual tdual
def tbldual := factTable [(0, 1), (1, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 7), (7, 6), (8, 23), (9, 28), (10, 29), (11, 30), (12, 31), (13, 24), (14, 25), (15, 26), (16, 27), (17, 32), (18, 33), (19, 34), (20, 35), (21, 36), (22, 37), (23, 8), (24, 13), (25, 14), (26, 15), (27, 16), (28, 9), (29, 10), (30, 11), (31, 12), (32, 17), (33, 18), (34, 19), (35, 20), (36, 21), (37, 22), (38, 39), (39, 38), (40, 40), (41, 41), (42, 42), (43, 43)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma factsdual : acceptedFacts actdual.fn tbldual = true := by decide +kernel
def lboth : List ℕ := [962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1010, 937, 881, 893, 862, 845, 847, 843, 962, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1070, 1073, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1008, 1073, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 977, 1073, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 993, 1073, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 1073, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1025, 1073, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1041, 1073, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 960, 1073, 944, 1073, 940, 940, 1073, 942, 1073, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 1073, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 920, 1073, 905, 1073, 891, 891, 1073, 884, 884, 1073, 888, 888, 888, 1073, 903, 903, 1073, 896, 896, 1073, 900, 900, 900, 1073, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 875, 1073, 879, 879, 879, 1073, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 860, 1073, 843, 843, 843, 843, 843, 843, 843, 843, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 875, 860, 1073, 843, 1073, 843, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 875, 860, 1073, 843, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 875, 860, 1073, 1070, 993, 1041, 1073, 843, 1073, 1008, 977, 1073, 1008, 993, 960, 1073, 977, 993, 1073, 843, 1073, 1056, 1025, 1073, 1056, 1041, 960, 1073, 1025, 1041, 1073, 960, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 944, 940, 935, 920, 875, 860, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 940, 942, 935, 920, 875, 860, 1073, 843, 1073, 935, 920, 1073, 935, 1073, 920, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 905, 888, 900, 875, 860, 1073, 843, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 891, 884, 875, 860, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 891, 888, 875, 879, 860, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 884, 888, 875, 860, 1073, 843, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 903, 896, 875, 860, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 903, 900, 875, 879, 860, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 896, 900, 875, 860, 1073, 1070, 1008, 977, 993, 1056, 1025, 1041, 960, 935, 920, 875, 879, 860, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 1073, 474, 534, 532, 533, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 469, 470, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 469, 453, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 533, 470, 453, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 517, 518, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 517, 501, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 533, 518, 501, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 470, 518, 420, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 531, 1073, 531, 530, 1073, 530, 1073, 474, 534, 532, 531, 530, 394, 395, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 474, 534, 532, 531, 530, 394, 379, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 529, 1073, 524, 525, 1073, 524, 523, 1073, 529, 525, 523, 1073, 527, 528, 1073, 527, 526, 1073, 529, 528, 526, 1073, 474, 534, 532, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 525, 528, 522, 1073, 474, 534, 532, 531, 530, 529, 524, 525, 523, 527, 528, 526, 522, 1073, 60, 61, 59, 57, 58, 56, 63, 55, 1073, 474, 474, 474, 474, 474, 474, 474, 474, 474, 474, 474, 474, 1073, 60, 1073, 61, 1073, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 534, 1073, 59, 1073, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 532, 1073, 533, 533, 533, 1073, 57, 1073, 469, 469, 1073, 470, 470, 470, 1073, 453, 453, 1073, 58, 1073, 517, 517, 1073, 518, 518, 518, 1073, 501, 501, 1073, 420, 1073, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 531, 1073, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 530, 1073, 56, 1073, 394, 394, 1073, 395, 1073, 379, 1073, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 529, 1073, 63, 1073, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 1073, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 525, 1073, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 1073, 55, 1073, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 527, 1073, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 528, 1073, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 526, 1073, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 1073]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mboth : rew lboth (mz 0) = mz 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tboth : twist true lboth (tz 0) = tz 0 := by decide +kernel
def actboth := twisted true lboth mboth tboth
def tblboth := factTable [(0, 1), (1, 0), (2, 2), (3, 4), (4, 3), (5, 5), (6, 7), (7, 6), (8, 23), (9, 28), (10, 30), (11, 29), (12, 31), (13, 24), (14, 26), (15, 25), (16, 27), (17, 33), (18, 32), (19, 34), (20, 35), (21, 37), (22, 36), (23, 8), (24, 13), (25, 15), (26, 14), (27, 16), (28, 9), (29, 11), (30, 10), (31, 12), (32, 18), (33, 17), (34, 19), (35, 20), (36, 22), (37, 21), (38, 39), (39, 38), (40, 40), (41, 42), (42, 41), (43, 43)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma factsboth : acceptedFacts actboth.fn tblboth = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use0 : useFacts tbldual (0, 1) (6, 1) = true := by decide +kernel
lemma mirror0 (t : ℕ) : Excluded (6, 1) t → Excluded (0, 1) t := pullExcluded actdual (liftFacts factsdual use0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use1 : useFacts tbldual (0, 2) (7, 2) = true := by decide +kernel
lemma mirror1 (t : ℕ) : Excluded (7, 2) t → Excluded (0, 2) t := pullExcluded actdual (liftFacts factsdual use1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use2 : useFacts tbldual (0, 3) (7, 3) = true := by decide +kernel
lemma mirror2 (t : ℕ) : Excluded (7, 3) t → Excluded (0, 3) t := pullExcluded actdual (liftFacts factsdual use2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use3 : useFacts tblboth (0, 4) (7, 3) = true := by decide +kernel
lemma mirror3 (t : ℕ) : Excluded (7, 3) t → Excluded (0, 4) t := pullExcluded actboth (liftFacts factsboth use3)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use4 : useFacts tbldual (0, 5) (7, 5) = true := by decide +kernel
lemma mirror4 (t : ℕ) : Excluded (7, 5) t → Excluded (0, 5) t := pullExcluded actdual (liftFacts factsdual use4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use5 : useFacts tbldual (1, 2) (6, 2) = true := by decide +kernel
lemma mirror5 (t : ℕ) : Excluded (6, 2) t → Excluded (1, 2) t := pullExcluded actdual (liftFacts factsdual use5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use6 : useFacts tblboth (1, 3) (6, 4) = true := by decide +kernel
lemma mirror6 (t : ℕ) : Excluded (6, 4) t → Excluded (1, 3) t := pullExcluded actboth (liftFacts factsboth use6)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use7 : useFacts tbldual (1, 4) (6, 4) = true := by decide +kernel
lemma mirror7 (t : ℕ) : Excluded (6, 4) t → Excluded (1, 4) t := pullExcluded actdual (liftFacts factsdual use7)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use8 : useFacts tbldual (1, 5) (6, 5) = true := by decide +kernel
lemma mirror8 (t : ℕ) : Excluded (6, 5) t → Excluded (1, 5) t := pullExcluded actdual (liftFacts factsdual use8)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use10 : useFacts tblplain (2, 4) (2, 3) = true := by decide +kernel
lemma mirror10 (t : ℕ) : Excluded (2, 3) t → Excluded (2, 4) t := pullExcluded actplain (liftFacts factsplain use10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use11 : useFacts tbldual (2, 5) (8, 5) = true := by decide +kernel
lemma mirror11 (t : ℕ) : Excluded (8, 5) t → Excluded (2, 5) t := pullExcluded actdual (liftFacts factsdual use11)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use12 : useFacts tbldual (3, 4) (9, 4) = true := by decide +kernel
lemma mirror12 (t : ℕ) : Excluded (9, 4) t → Excluded (3, 4) t := pullExcluded actdual (liftFacts factsdual use12)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use14 : useFacts tblplain (4, 5) (3, 5) = true := by decide +kernel
lemma mirror14 (t : ℕ) : Excluded (3, 5) t → Excluded (4, 5) t := pullExcluded actplain (liftFacts factsplain use14)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use17 : useFacts tblplain (6, 3) (6, 4) = true := by decide +kernel
lemma mirror17 (t : ℕ) : Excluded (6, 4) t → Excluded (6, 3) t := pullExcluded actplain (liftFacts factsplain use17)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use22 : useFacts tblplain (7, 4) (7, 3) = true := by decide +kernel
lemma mirror22 (t : ℕ) : Excluded (7, 3) t → Excluded (7, 4) t := pullExcluded actplain (liftFacts factsplain use22)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use24 : useFacts tbldual (8, 3) (2, 3) = true := by decide +kernel
lemma mirror24 (t : ℕ) : Excluded (2, 3) t → Excluded (8, 3) t := pullExcluded actdual (liftFacts factsdual use24)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use25 : useFacts tblboth (8, 4) (2, 3) = true := by decide +kernel
lemma mirror25 (t : ℕ) : Excluded (2, 3) t → Excluded (8, 4) t := pullExcluded actboth (liftFacts factsboth use25)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use28 : useFacts tbldual (9, 5) (3, 5) = true := by decide +kernel
lemma mirror28 (t : ℕ) : Excluded (3, 5) t → Excluded (9, 5) t := pullExcluded actdual (liftFacts factsdual use28)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use29 : useFacts tblboth (10, 5) (3, 5) = true := by decide +kernel
lemma mirror29 (t : ℕ) : Excluded (3, 5) t → Excluded (10, 5) t := pullExcluded actboth (liftFacts factsboth use29)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use31 : useFacts tbldual (13, 0) (12, 0) = true := by decide +kernel
lemma mirror31 (t : ℕ) : Excluded (12, 0) t → Excluded (13, 0) t := pullExcluded actdual (liftFacts factsdual use31)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use33 : useFacts tblplain (15, 0) (16, 0) = true := by decide +kernel
lemma mirror33 (t : ℕ) : Excluded (16, 0) t → Excluded (15, 0) t := pullExcluded actplain (liftFacts factsplain use33)
def smallT : List ℕ := [1,2,3]
def MaskRun (e : ℕ × ℕ) (Q : List (ℕ × ℕ)) (t : ℕ) : Prop :=
  ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [e] Q 0 12 (remT (unaryE e) t) p.1 p.2 = false
def CaseData (e : ℕ × ℕ) : Prop := ∃ Q : List (ℕ × ℕ), okEdge e 0 = true ∧ pOk 0 Q = true ∧
  (∀ p ∈ Q, Imp [e] p.1 p.2) ∧ ∀ t ∈ smallT, MaskRun e Q t
lemma prepSound (e : ℕ × ℕ) (a b c : List (ℕ × ℕ))
    (hp : six.contains e && allB.all (fun p => okEdge e p.1) && b.all (pass e (lowRt e)) &&
      a.all (pass e (b ++ lowRt e)) && c.all (fun p => (lowAll e).any (fun b => qual b p)) &&
      pOk 0 (a ++ b ++ c) && okEdge e 0 = true)
    (runs : ∀ t ∈ smallT, MaskRun e (a ++ b ++ c) t) : CaseData e := by
  simp only [Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨he,edges⟩,hb⟩,ha⟩,hc⟩,hP⟩,hE⟩ := hp
  have he' : e ∈ six := by simpa using he
  have lo := lowValid edges
  have prev := lowRtValid lo
  have goodB : ∀ p ∈ b, Imp [e] p.1 p.2 := fun p h => passValid he' lo prev (hb p h)
  have goodA : ∀ p ∈ a, Imp [e] p.1 p.2 := fun p h => passValid he' lo (apI goodB prev) (ha p h)
  have goodC : ∀ p ∈ c, Imp [e] p.1 p.2 := fun p h => qualified (hc p h) lo
  refine ⟨a ++ b ++ c,hE,hP,?_,?_⟩
  · exact apI (apI goodA goodB) goodC
  · exact runs
noncomputable section
abbrev BState := Nat × Nat × Nat × Nat × List (Nat × Nat × Nat × Nat × Nat)
def budgetPack (mode k t z : Nat) (v : List W) : BState :=
  (mode,k,t,z,v.map fun w => (w.s,w.a,w.b,w.c,w.r))
def budgetEval (l m g K : Nat) (c : BState) : Bool :=
  let (mode,k,t,z,ws) := c
  let v := ws.map fun (x,a,b,c,r) => (⟨x,a,b,c,r⟩ : W)
  if mode == 0 then look l m g K k t z v else look1 l m g K K k t z v
def budgetTop (cb : Nat → Nat → Nat → Nat → List W → Bool) (l m g _K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (cb 0) l m g k t z v y) (Nat.beq ph 1)) true
      (node (cb 1 (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def budgetStart (cb : Nat → Nat → Nat → Nat → List W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => budgetTop cb l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
noncomputable def budgetWith (cb : Nat → Nat → Nat → Nat → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => budgetStart cb l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
end
lemma budgetEvalPack (l m g K mode k t z : ℕ) (v : List W) :
    budgetEval l m g K (budgetPack mode k t z v) =
      (if mode == 0 then look l m g K k t z v else look1 l m g K K k t z v) := by
  have hv : (v.map (fun w => (w.s,w.a,w.b,w.c,w.r))).map
      (fun (s,a,b,c,r) => (⟨s,a,b,c,r⟩ : W)) = v := by
    induction v with
    | nil => rfl
    | cons w v ih => cases w; simp only [List.map_cons, ih]
  simp only [budgetPack, budgetEval, hv]

noncomputable def budgetMemo (l m g K : ℕ) (cache : List BState)
    (mode k t z : ℕ) (v : List W) : Bool :=
  if budgetPack mode k t z v ∈ cache then false else
    if mode == 0 then look l m g K k t z v else look1 l m g K K k t z v

lemma budgetMemo_eq (l m g K : ℕ) (cache : List BState)
    (ok : ∀ c ∈ cache, budgetEval l m g K c = false) :
    budgetMemo l m g K cache = fun mode k t z v =>
      if mode == 0 then look l m g K k t z v else look1 l m g K K k t z v := by
  funext mode k t z v
  unfold budgetMemo
  split
  next hc => exact ((budgetEvalPack l m g K mode k t z v).symm.trans (ok _ hc)).symm
  next => rfl

lemma budgetMemo_join (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (cache : List BState)
    (ok : ∀ c ∈ cache, budgetEval (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K c = false)
    (checked : budgetWith (budgetMemo (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K cache)
       E Q Z K t H ph = false) : chk E Q Z K t H ph = false := by
  rw [budgetMemo_eq _ _ _ _ _ ok] at checked
  unfold budgetWith at checked
  unfold chk
  simp only [frc_eq, st_eq] at checked ⊢
  exact checked
def packedUniverse : ℕ := (AA ||| (2 ^ 64 - 1)) ||| (AA <<< NN)
def packedSignal0 : ℕ := bigNat_8
def packedSignal1 : ℕ := bigNat_7
def packedSignal2 : ℕ := bigNat_6
def packedSignal3 : ℕ := (bigNat_6 &&& bigNat_7)
def packedSignal4 : ℕ := bigNat_5
def packedSignal5 : ℕ := bigNat_4
def packedSignal6 : ℕ := bigNat_3
def packedSignal7 : ℕ := (bigNat_3 &&& bigNat_5)
def packedSignal8 : ℕ := (bigNat_6 ||| bigNat_7)
def packedSignal9 : ℕ := (bigNat_5 ||| bigNat_7)
def packedSignal10 : ℕ := (bigNat_5 &&& bigNat_7)
def packedSignal11 : ℕ := (bigNat_5 ||| (bigNat_3 &&& bigNat_7))
def packedSignal12 : ℕ := (bigNat_3 &&& bigNat_7)
def packedSignal13 : ℕ := (bigNat_4 &&& bigNat_5)
def packedSignal14 : ℕ := (bigNat_4 ||| bigNat_5)
def packedSignal15 : ℕ := (bigNat_3 ||| bigNat_7)
def packedSignal16 : ℕ := (bigNat_4 &&& bigNat_6)
def packedSignal17 : ℕ := (bigNat_4 ||| bigNat_6)
def packedSignal18 : ℕ := (bigNat_3 ||| bigNat_5)
def packedSignal19 : ℕ := (bigNat_6 ||| bigNat_8)
def packedSignal20 : ℕ := (bigNat_6 &&& bigNat_8)
def packedSignal21 : ℕ := (bigNat_7 ||| (bigNat_4 &&& bigNat_5))
def packedSignal22 : ℕ := (bigNat_8 ||| (bigNat_4 &&& bigNat_5))
def packedSignal23 : ℕ := (bigNat_3 ||| (bigNat_4 &&& bigNat_5))
def packedSignal24 : ℕ := (bigNat_6 ||| (bigNat_4 &&& bigNat_5))
def packedSignal25 : ℕ := (bigNat_3 ||| bigNat_6)
def packedSignal26 : ℕ := (bigNat_3 &&& bigNat_6)
def packedSignal27 : ℕ := (bigNat_3 &&& bigNat_8)
def packedSignal28 : ℕ := (bigNat_7 &&& bigNat_8)
def packedSignal29 : ℕ := (bigNat_5 &&& bigNat_6)
def packedSignal30 : ℕ := ((bigNat_7 ^^^ packedUniverse) ||| (bigNat_4 &&& bigNat_5))
def packedSignal31 : ℕ := ((bigNat_6 ^^^ packedUniverse) ||| (bigNat_4 &&& bigNat_5))
def packedSignal32 : ℕ := (bigNat_4 ||| bigNat_7)
def packedSignal33 : ℕ := (bigNat_7 ^^^ packedUniverse)
def packedSignal34 : ℕ := (bigNat_6 ^^^ packedUniverse)
def packedSignal35 : ℕ := ((bigNat_3 ^^^ packedUniverse) ||| (bigNat_4 &&& bigNat_5))
def packedSignal36 : ℕ := (bigNat_3 ||| bigNat_8)
def packedSignal37 : ℕ := (bigNat_5 &&& bigNat_8)
def packedSignal38 : ℕ := (bigNat_5 ||| bigNat_6)
def packedSignal39 : ℕ := (bigNat_3 ||| bigNat_4)
def packedSignal40 : ℕ := (bigNat_6 ||| (bigNat_7 ^^^ packedUniverse))
def packedSignal41 : ℕ := (bigNat_7 ||| (bigNat_6 ^^^ packedUniverse))
def packedSignal42 : ℕ := (bigNat_7 ||| bigNat_8)
def packedSignal43 : ℕ := (bigNat_4 ||| bigNat_8)
def packedSignal44 : ℕ := ((bigNat_5 ||| bigNat_7) ^^^ packedUniverse)
def packedSignal45 : ℕ := ((bigNat_3 ||| bigNat_7) ^^^ packedUniverse)
def packedSignal46 : ℕ := (bigNat_8 ||| (bigNat_7 ^^^ packedUniverse))
def packedSignal47 : ℕ := (bigNat_8 &&& (bigNat_7 ^^^ packedUniverse))
def packedSignal48 : ℕ := (bigNat_6 &&& (bigNat_7 ^^^ packedUniverse))
def packedSignal49 : ℕ := (bigNat_3 &&& (bigNat_7 ^^^ packedUniverse))
def packedSignal50 : ℕ := (bigNat_8 ||| (bigNat_6 ^^^ packedUniverse))
def packedSignal51 : ℕ := (bigNat_8 ||| (bigNat_3 ^^^ packedUniverse))
def packedSignal52 : ℕ := (bigNat_3 ^^^ packedUniverse)
def packedSignal53 : ℕ := (bigNat_5 ||| (bigNat_7 ^^^ packedUniverse))
def packedSignal54 : ℕ := (bigNat_4 ||| (bigNat_7 ^^^ packedUniverse))
def packedSignal55 : ℕ := (bigNat_3 ||| (bigNat_7 ^^^ packedUniverse))
def packedSignal56 : ℕ := (bigNat_7 ||| (bigNat_3 ^^^ packedUniverse))
def packedSignal57 : ℕ := (bigNat_8 &&& (bigNat_6 ^^^ packedUniverse))
def packedSignal58 : ℕ := (bigNat_7 &&& (bigNat_6 ^^^ packedUniverse))
def packedSignal59 : ℕ := (bigNat_5 ^^^ packedUniverse)
def packedSignal60 : ℕ := (bigNat_8 &&& (bigNat_5 ^^^ packedUniverse))
def packedSignal61 : ℕ := (bigNat_7 &&& (bigNat_5 ^^^ packedUniverse))
def packedSignal62 : ℕ := (bigNat_7 &&& (bigNat_3 ^^^ packedUniverse))
def packedSignal63 : ℕ := (bigNat_5 &&& (bigNat_6 ^^^ packedUniverse))
def packedSignal64 : ℕ := (bigNat_3 &&& (bigNat_6 ^^^ packedUniverse))
def packedSignal65 : ℕ := (bigNat_4 ||| (bigNat_6 ^^^ packedUniverse))
def packedSignal66 : ℕ := (bigNat_3 ||| (bigNat_6 ^^^ packedUniverse))
def packedSignal67 : ℕ := (bigNat_6 ||| (bigNat_3 ^^^ packedUniverse))
def packedSignal68 : ℕ := (bigNat_6 &&& (bigNat_3 ^^^ packedUniverse))
def packedSignal69 : ℕ := (bigNat_3 &&& (bigNat_5 ^^^ packedUniverse))
def packedSignal70 : ℕ := (bigNat_4 ||| (bigNat_5 ^^^ packedUniverse))
def packedSignal71 : ℕ := (bigNat_5 &&& (bigNat_3 ^^^ packedUniverse))
def packedSignal72 : ℕ := (bigNat_4 ||| (bigNat_3 ^^^ packedUniverse))
def packedSignal73 : ℕ := (bigNat_5 ||| bigNat_8)
def packedSignal74 : ℕ := ((bigNat_6 ||| bigNat_7) ^^^ packedUniverse)
def packedSignal75 : ℕ := ((bigNat_6 &&& bigNat_7) ^^^ packedUniverse)
def packedSignal76 : ℕ := ((bigNat_3 &&& bigNat_7) ^^^ packedUniverse)
def packedSignal77 : ℕ := ((bigNat_5 ||| bigNat_6) ^^^ packedUniverse)
def packedSignal78 : ℕ := ((bigNat_3 &&& bigNat_6) ^^^ packedUniverse)
def packedSignal79 : ℕ := ((bigNat_3 ||| bigNat_6) ^^^ packedUniverse)
def packedSignal80 : ℕ := (bigNat_5 &&& (bigNat_7 ^^^ packedUniverse))
def packedSignal81 : ℕ := (bigNat_8 &&& (bigNat_3 ^^^ packedUniverse))
def packedSignal82 : ℕ := ((bigNat_8 ^^^ packedUniverse) ||| (bigNat_4 &&& bigNat_5))
def packedSignal83 : ℕ := (bigNat_5 ||| (bigNat_6 ^^^ packedUniverse))
def packedSignal84 : ℕ := (bigNat_6 &&& (bigNat_5 ^^^ packedUniverse))
def packedSignal85 : ℕ := (bigNat_4 &&& (bigNat_5 ^^^ packedUniverse))
def packedSignal86 : ℕ := (bigNat_5 ||| (bigNat_3 ^^^ packedUniverse))
def packedSignal87 : ℕ := (bigNat_5 ||| (bigNat_4 ^^^ packedUniverse))
def packedSignal88 : ℕ := (bigNat_4 ||| (bigNat_6 &&& bigNat_7))
def packedSignal89 : ℕ := (bigNat_4 &&& (bigNat_6 &&& bigNat_7))
def packedSignal90 : ℕ := (bigNat_3 ||| (bigNat_6 &&& bigNat_7))
def packedSignal91 : ℕ := (bigNat_3 &&& (bigNat_6 &&& bigNat_7))
def packedSignal92 : ℕ := (bigNat_4 &&& bigNat_8)
def packedSignal93 : ℕ := (bigNat_4 &&& bigNat_7)
def packedSignal94 : ℕ := (bigNat_3 &&& bigNat_4)
def packedSignal95 : ℕ := (bigNat_7 ||| (bigNat_5 ^^^ packedUniverse))
def packedSignal96 : ℕ := (bigNat_7 &&& (bigNat_4 ^^^ packedUniverse))
def packedSignal97 : ℕ := (bigNat_6 ||| (bigNat_5 ^^^ packedUniverse))
def packedSignal98 : ℕ := ((bigNat_5 &&& bigNat_7) ^^^ packedUniverse)
def packedSignal99 : ℕ := (bigNat_4 &&& (bigNat_7 ^^^ packedUniverse))
def packedSignal100 : ℕ := (bigNat_4 ^^^ packedUniverse)
def packedSignal101 : ℕ := (bigNat_4 &&& (bigNat_6 ^^^ packedUniverse))
def packedSignal102 : ℕ := (bigNat_6 &&& (bigNat_4 ^^^ packedUniverse))
def packedSignal103 : ℕ := (bigNat_3 ||| (bigNat_5 ^^^ packedUniverse))
def packedSignal104 : ℕ := (bigNat_5 &&& (bigNat_4 ^^^ packedUniverse))
def packedSignal105 : ℕ := (bigNat_3 &&& (bigNat_4 ^^^ packedUniverse))
def packedSignal106 : ℕ := ((bigNat_4 ||| bigNat_7) ^^^ packedUniverse)
def packedSignal107 : ℕ := ((bigNat_4 ||| bigNat_6) ^^^ packedUniverse)
def packedSignal108 : ℕ := ((bigNat_5 &&& bigNat_6) ^^^ packedUniverse)
def packedSignal109 : ℕ := ((bigNat_4 ||| bigNat_5) ^^^ packedUniverse)
def packedSignal110 : ℕ := ((bigNat_3 &&& bigNat_5) ^^^ packedUniverse)
def packedSignal111 : ℕ := (bigNat_8 ||| (bigNat_5 ^^^ packedUniverse))
def packedSignal112 : ℕ := (bigNat_8 &&& (bigNat_4 ^^^ packedUniverse))
def packedSignal113 : ℕ := (bigNat_7 ||| (bigNat_4 ^^^ packedUniverse))
def packedSignal114 : ℕ := (bigNat_3 ||| (bigNat_4 ^^^ packedUniverse))
def packedSignal115 : ℕ := (bigNat_4 &&& (bigNat_3 ^^^ packedUniverse))
def packedSignal116 : ℕ := (bigNat_8 ||| (bigNat_4 ^^^ packedUniverse))
def packedSignal117 : ℕ := (bigNat_6 ||| (bigNat_4 ^^^ packedUniverse))
def packedSignal118 : ℕ := ((bigNat_4 &&& bigNat_7) ^^^ packedUniverse)
def packedSignal119 : ℕ := ((bigNat_4 &&& bigNat_6) ^^^ packedUniverse)
def packedSignal120 : ℕ := ((bigNat_3 ||| bigNat_5) ^^^ packedUniverse)
def packedSignal121 : ℕ := ((bigNat_4 &&& bigNat_5) ^^^ packedUniverse)
def packedSignal122 : ℕ := ((bigNat_3 ||| bigNat_4) ^^^ packedUniverse)
def packedSignal123 : ℕ := ((bigNat_3 &&& bigNat_4) ^^^ packedUniverse)
def storedWire (s a b r : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ := (s,a,b,a ||| b,r)
def storedWires : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
  storedWire packedSignal0 0x400004000040000020000200000108420000000002000000 0x1084210842100000000000000000000000000000000000080000000000000 3,
  storedWire packedSignal1 0x10000000000000000002000001000010000100001000000000100000 0x1000000000008421080000000000000000000000000000004000000000000 3,
  storedWire packedSignal2 0x800000000000000000100000080000800008001000000000008000 0x80000000008000004210800000000000000000000000000200000000000 3,
  storedWire packedSignal3 0x10800000000000000002100001080010800108001000000000108000 0x8000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal4 0x40000020000200000000000004000040000400000000000000400 0x4000000000000000000042108400000000000000000000010000000000 3,
  storedWire packedSignal5 0x2000001000010000008000000000002000000000000000000020 0x200000000000000000000000021084000000000000000000800000000 3,
  storedWire packedSignal6 0x100000080000800000400000000000000020000000000000001 0x210842000000000000040000000 3,
  storedWire packedSignal7 0x20000000040100020080200800000400004000040000420000000000000401 0 3,
  storedWire packedSignal8 0x1000000000000000 0x1080000000008421084210800000000000000000000000004200000000000 0,
  storedWire packedSignal9 0 0x1004000000008421080000042108400000000000000000004010000000000 0,
  storedWire packedSignal10 0x10040000020000200002000001004010040100401000000000100400 0 0,
  storedWire packedSignal11 0 0x4000000000000000000042108400000000000000000000010000000000 0,
  storedWire packedSignal12 0x20000010000100000080000802000401000010000100021000000000100001 0 3,
  storedWire packedSignal13 0x42000021000210000008000004000042000400000000000000420 0 0,
  storedWire packedSignal14 0 0x4200000000000000000042108421084000000000000000010800000000 0,
  storedWire packedSignal15 0 0x1000000000008421080000000000000000210842000000004000040000000 0,
  storedWire packedSignal16 0x802000001000010000108000080000802008001000000000008020 0 0,
  storedWire packedSignal17 0 0x80200000008000004210800000021084000000000000000200800000000 0,
  storedWire packedSignal7 0x40100020080200800000400004000040000420000000000000401 0 0,
  storedWire packedSignal18 0 0x4000000000000000000042108400000210842000000000010040000000 0,
  storedWire packedSignal19 0x8000000000000000000 0x1084210842108000004210800000000000000000000000080200000000000 0,
  storedWire packedSignal20 0x800000400004000040100020080200800108421000000002008000 0x80000000000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal13 0x20000000042000021000210000008000004000042000400000000000000420 0 3,
  storedWire packedSignal21 0 0x1000000000008421080000000000000000000000000000004000000000000 0,
  storedWire packedSignal22 0x400000000000000000 0x1084210842100000000000000000000000000000000000080000000000000 0,
  storedWire packedSignal23 0 0x210842000000000000040000000 0,
  storedWire packedSignal24 0 0x80000000008000004210800000000000000000000000000200000000000 0,
  storedWire packedSignal25 0 0x80000000008000004210800000000000210842000000000200040000000 0,
  storedWire packedSignal12 0x10000100000080000802000401000010000100021000000000100001 0 0,
  storedWire packedSignal26 0x800100000080000800100400080000800008021000000000008001 0 0,
  storedWire packedSignal27 0x100400084000840000420000200000108420000000002000001 0 0,
  storedWire packedSignal28 0x10000000400004000042000021000210000108421000000002100000 0x1000000000000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal29 0x840000020000200000100000084000840008401000000000008400 0 0,
  storedWire packedSignal30 0x21000000000000000000000000000000000000000000000 0x10000000000000000002000001000010000100001000000000100000 0,
  storedWire packedSignal31 0x210000000000000000000000000000000000000000 0x800000000000000000100000080000800008001000000000008000 0,
  storedWire packedSignal32 0 0x1000200000008421080000000000021084000000000000004000800000000 0,
  storedWire packedSignal33 0x1000000000008421080000000000000000000000000000004000000000000 0x10000000000000000002000001000010000100001000000000100000 0,
  storedWire packedSignal34 0x80000000008000004210800000000000000000000000000200000000000 0x800000000000000000100000080000800008001000000000008000 0,
  storedWire packedSignal35 0x42000000000000000000000 0x100000080000800000400000000000000020000000000000001 0,
  storedWire packedSignal36 0x20000000000000000 0x1084210842100000000000000000000000210842000000080000040000000 0,
  storedWire packedSignal37 0x40000420004200040000020004200040108420000000002000400 0x4000000000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal38 0 0x84000000008000004210842108400000000000000000000210000000000 0,
  storedWire packedSignal39 0 0x200000000000000000000000021084210842000000000000840000000 0,
  storedWire packedSignal40 0 0x80010000008000004210802000001000010000100001000200000100000 0,
  storedWire packedSignal41 0 0x1000000800008421080000000100000080000800008001004000000008000 0,
  storedWire packedSignal42 0x100000000000000000000 0x1084210842108421080000000000000000000000000000084000000000000 0,
  storedWire packedSignal43 0 0x1084210842100000000000000000021084000000000000080000800000000 0,
  storedWire packedSignal44 0x1004000000008421080000042108400000000000000000004010000000000 0 0,
  storedWire packedSignal45 0x1000000000008421080000000000000000210842000000004000040000000 0 0,
  storedWire packedSignal46 0x400000000000000000000000000000000000000000000000 0x1084210842100000000000002000001000010000100001080000000100000 0,
  storedWire packedSignal47 0x1000000000008421084000040000020000200000108420004000002000000 0x10000000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal48 0x1000000800008421080000000100000080000800008001004000000008000 0 0,
  storedWire packedSignal49 0x1000000000108421080000800000400000000000000020004000000000001 0x10000000000000000000000000 0,
  storedWire packedSignal50 0x4000000000000000000000000000000000000000000 0x1084210842100000000000000100000080000800008001080000000008000 0,
  storedWire packedSignal51 0x200000000000000000000000000 0x1084210842100000080000800000400000000000000020080000000000001 0,
  storedWire packedSignal52 0x210842000000000000040000000 0x100000080000800000400000000000000020000000000000001 0,
  storedWire packedSignal53 0x20000000000000000000000000000000000000000000000 0x4010000000000000000042108401000010000100001000010000100000 0,
  storedWire packedSignal54 0x1000000000000000000000000000000000000000000000 0x210000000000000000002000021084010000100001000000800100000 0,
  storedWire packedSignal55 0x80000000000000000000000000000000000000000000 0x10000000000000000002000001000210842100001000000040100000 0,
  storedWire packedSignal56 0x10000000000000000000000000 0x1000000000108421080000800000400000000000000020004000000000001 0,
  storedWire packedSignal57 0x80000000008400004210840000020000200000108420000200002000000 0x800000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal58 0x80010000008000004210802000001000010000100001000200000100000 0 0,
  storedWire packedSignal59 0x4000000000000000000042108400000000000000000000010000000000 0x40000020000200000000000004000040000400000000000000400 0,
  storedWire packedSignal60 0x4000000000400004000042108420000200000108420000010002000000 0x40000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal61 0x4010000000000000000042108401000010000100001000010000100000 0x20000000000000000000000000000000000000000000000 0,
  storedWire packedSignal62 0x10000000000000000002000001000210842100001000000040100000 0x80000000000000000000000000000000000000000000 0,
  storedWire packedSignal63 0x80000040008020004210800000000004000040000400000200000000400 0x100000000000000000000000000000000000 0,
  storedWire packedSignal64 0x80000000108000084210800000400000000000000020000200000000001 0x800000000000000000000000 0,
  storedWire packedSignal65 0x10000000000000000000000000000000000000000 0x200800000000000000000100021084000800008001000000800008000 0,
  storedWire packedSignal66 0x800000000000000000000000000000000000000 0x800000000000000000100000080210842008001000000040008000 0,
  storedWire packedSignal67 0x800000000000000000000000 0x80000000108000084210800000400000000000000020000200000000001 0,
  storedWire packedSignal68 0x800000000000000000100000080210842008001000000040008000 0x800000000000000000000000000000000000000 0,
  storedWire packedSignal69 0x4000000100000080000842108400000000000000020000010000000001 0x40000000000000000000000 0,
  storedWire packedSignal70 0x8000000000000000000000000000000000 0x40000020000200000000000004000040000400000000000000400 0,
  storedWire packedSignal71 0x40000020000200000000000004210842000400000000040000400 0x400000000000000000000000000000000 0,
  storedWire packedSignal72 0x2000000000000000000000 0x200000100000080000800000421084000000000020000000800000001 0,
  storedWire packedSignal73 0x400000000000000000 0x1084210842100000000000042108400000000000000000080010000000000 0,
  storedWire packedSignal74 0x1080000000008421084210800000000000000000000000004200000000000 0x1000000000000000 0,
  storedWire packedSignal75 0x8000000000000000000000000000000000000000000000000 0x10800000000000000002100001080010800108001000000000108000 0,
  storedWire packedSignal76 0 0x10000100000080000802000401000010000100021000000000100001 0,
  storedWire packedSignal77 0x84000000008000004210842108400000000000000000000210000000000 0 0,
  storedWire packedSignal78 0 0x800100000080000800100400080000800008021000000000008001 0,
  storedWire packedSignal79 0x80000000008000004210800000000000210842000000000200040000000 0 0,
  storedWire packedSignal80 0x1000000040008421080200000000000004000040000400004000000000400 0x2000000000000000000000000000000000000 0,
  storedWire packedSignal81 0x400004000040000020000210842108420000000042000000 0x100000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal82 0x42000000000000000000000000000000000000000000000000000 0x400004000040000020000200000108420000000002000000 0,
  storedWire packedSignal83 0x200000000000000000000000000000000000000000 0x4000800000000000000042108400080000800008001000010000008000 0,
  storedWire packedSignal84 0x4000800000000000000042108400080000800008001000010000008000 0x200000000000000000000000000000000000000000 0,
  storedWire packedSignal85 0x4000002000001000010042108400000000002000000000010000000020 0x4000000000000000000000000000 0,
  storedWire packedSignal86 0x40000000000000000000000 0x4000000100000080000842108400000000000000020000010000000001 0,
  storedWire packedSignal70 0x8000000000000000000000000000000000 0x200040000020000200000000021084000040000400000000800000400 0,
  storedWire packedSignal87 0x4000000000000000000000000000 0x2000001000010000008000000000002000000000000000000020 0,
  storedWire packedSignal3 0x10800000000000000002100001080010800108001000000000108000 0x8000000000000000000000000000000000000000000000000 3,
  storedWire packedSignal88 0 0x200000008000000000000000021084000000000000000000800000000 0,
  storedWire packedSignal89 0x10802000001000010002108001080010802108001000000000108020 0 0,
  storedWire packedSignal90 0 0x8000000000000000000000210842000000000000040000000 0,
  storedWire packedSignal91 0x10800100000080000802100401080010800108021000000000108001 0 0,
  storedWire packedSignal92 0x2000401004010040008020000200002108420000000002000020 0x200000000000000000000000000000000000000000000000000000000 0,
  storedWire packedSignal52 0x210842000000000000040000000 0x100000080000800000400000000000000020000000000000001 3,
  storedWire packedSignal93 0x10002000001000010002008001000010002100001000000000100020 0 0,
  storedWire packedSignal59 0x4000000000000000000042108400000000000000000000010000000000 0x40000020000200000000000004000040000400000000000000400 3,
  storedWire packedSignal94 0x2100001080010800008400000000002000020000000000000021 0 0,
  storedWire packedSignal33 0x1000000000008421080000000000000000000000000000004000000000000 0x10000000000000000002000001000010000100001000000000100000 3,
  storedWire packedSignal0 33554432 0x80000000000000 3,
  storedWire packedSignal1 1048576 0x4000000000000 3,
  storedWire packedSignal38 0 36283883716608 0,
  storedWire packedSignal2 32768 35184372088832 3,
  storedWire packedSignal4 1024 1099511627776 3,
  storedWire packedSignal5 32 34359738368 3,
  storedWire packedSignal6 1 1073741824 3,
  storedWire packedSignal9 0 0x4010000000000 0,
  storedWire packedSignal29 33792 0 0,
  storedWire packedSignal10 1049600 0 0,
  storedWire packedSignal12 1048577 0 0,
  storedWire packedSignal26 32769 0 0,
  storedWire packedSignal25 0 35185445830656 0,
  storedWire packedSignal15 0 0x4000040000000 0,
  storedWire packedSignal8 0 0x4200000000000 0,
  storedWire packedSignal3 1081344 0 0,
  storedWire packedSignal14 0 1133871366144 0,
  storedWire packedSignal7 1025 0 0,
  storedWire packedSignal17 0 35218731827200 0,
  storedWire packedSignal32 0 0x4000800000000 0,
  storedWire packedSignal18 0 1100585369600 0,
  storedWire packedSignal93 1048608 0 0,
  storedWire packedSignal16 32800 0 0,
  storedWire packedSignal13 1056 0 0,
  storedWire packedSignal39 0 35433480192 0,
  storedWire packedSignal94 33 0 0,
  storedWire packedSignal41 0 0x4000000008000 0,
  storedWire packedSignal95 0 0x4000000000400 0,
  storedWire packedSignal58 35184373137408 0 0,
  storedWire packedSignal61 1099512676352 0 0,
  storedWire packedSignal96 34360786944 0 0,
  storedWire packedSignal97 0 35184372089856 0,
  storedWire packedSignal67 0 35184372088833 0,
  storedWire packedSignal98 0 1049600 0,
  storedWire packedSignal76 0 1048577 0,
  storedWire packedSignal48 0x4000000008000 0 0,
  storedWire packedSignal33 0x4000000000000 1048576 0,
  storedWire packedSignal80 0x4000000000400 0 0,
  storedWire packedSignal99 0x4000000000020 0 0,
  storedWire packedSignal49 0x4000000000001 0 0,
  storedWire packedSignal40 0 35184373137408 0,
  storedWire packedSignal34 35184372088832 32768 0,
  storedWire packedSignal53 0 1099512676352 0,
  storedWire packedSignal59 1099511627776 1024 0,
  storedWire packedSignal54 0 34360786944 0,
  storedWire packedSignal55 0 1074790400 0,
  storedWire packedSignal56 0 0x4000000000001 0,
  storedWire packedSignal100 34359738368 32 0,
  storedWire packedSignal63 35184372089856 0 0,
  storedWire packedSignal101 35184372088864 0 0,
  storedWire packedSignal64 35184372088833 0 0,
  storedWire packedSignal83 0 1099511660544 0,
  storedWire packedSignal65 0 34359771136 0,
  storedWire packedSignal66 0 1073774592 0,
  storedWire packedSignal52 1073741824 1 0,
  storedWire packedSignal84 1099511660544 0 0,
  storedWire packedSignal102 34359771136 0 0,
  storedWire packedSignal85 1099511627808 0 0,
  storedWire packedSignal69 1099511627777 0 0,
  storedWire packedSignal70 0 34359739392 0,
  storedWire packedSignal103 0 1073742848 0,
  storedWire packedSignal86 0 1099511627777 0,
  storedWire packedSignal104 34359739392 0 0,
  storedWire packedSignal105 34359738369 0 0,
  storedWire packedSignal72 0 34359738369 0,
  storedWire packedSignal74 0x4200000000000 0 0,
  storedWire packedSignal44 0x4010000000000 0 0,
  storedWire packedSignal106 0x4000800000000 0 0,
  storedWire packedSignal75 0 1081344 0,
  storedWire packedSignal77 36283883716608 0 0,
  storedWire packedSignal107 35218731827200 0 0,
  storedWire packedSignal108 0 33792 0,
  storedWire packedSignal78 0 32769 0,
  storedWire packedSignal109 1133871366144 0 0,
  storedWire packedSignal110 0 1025 0,
  storedWire packedSignal47 0x4000002000000 0 0,
  storedWire packedSignal57 35184405643264 0 0,
  storedWire packedSignal46 0 0x80000000100000 0,
  storedWire packedSignal50 0 0x80000000008000 0,
  storedWire packedSignal111 0 0x80000000000400 0,
  storedWire packedSignal51 0 0x80000000000001 0,
  storedWire packedSignal60 1099545182208 0 0,
  storedWire packedSignal112 34393292800 0 0,
  storedWire packedSignal113 0 0x4000000000020 0,
  storedWire packedSignal114 0 1073741856 0,
  storedWire packedSignal115 1073741856 0 0,
  storedWire packedSignal116 0 0x80000000000020 0,
  storedWire packedSignal81 1107296256 0 0,
  storedWire packedSignal62 1074790400 0 0,
  storedWire packedSignal117 0 35184372088864 0,
  storedWire packedSignal68 1073774592 0 0,
  storedWire packedSignal87 0 1099511627808 0,
  storedWire packedSignal71 1073742848 0 0,
  storedWire packedSignal45 0x4000040000000 0 0,
  storedWire packedSignal118 0 1048608 0,
  storedWire packedSignal79 35185445830656 0 0,
  storedWire packedSignal119 0 32800 0,
  storedWire packedSignal120 1100585369600 0 0,
  storedWire packedSignal121 0 1056 0,
  storedWire packedSignal122 35433480192 0 0,
  storedWire packedSignal123 0 33 0 ]
noncomputable def edgeCase9 (t H ph : ℕ) : Bool := chk [ea9] edgeQ9 0 12 (remT (unaryE ea9) t) H ph
noncomputable def edgeCase13 (t H ph : ℕ) : Bool := chk [ea13] edgeQ13 0 12 (remT (unaryE ea13) t) H ph
noncomputable def edgeCase15 (t H ph : ℕ) : Bool := chk [ea15] edgeQ15 0 12 (remT (unaryE ea15) t) H ph
noncomputable def edgeCase16 (t H ph : ℕ) : Bool := chk [ea16] edgeQ16 0 12 (remT (unaryE ea16) t) H ph
noncomputable def edgeCase18 (t H ph : ℕ) : Bool := chk [ea18] edgeQ18 0 12 (remT (unaryE ea18) t) H ph
noncomputable def edgeCase19 (t H ph : ℕ) : Bool := chk [ea19] edgeQ19 0 12 (remT (unaryE ea19) t) H ph
noncomputable def edgeCase20 (t H ph : ℕ) : Bool := chk [ea20] edgeQ20 0 12 (remT (unaryE ea20) t) H ph
noncomputable def edgeCase21 (t H ph : ℕ) : Bool := chk [ea21] edgeQ21 0 12 (remT (unaryE ea21) t) H ph
noncomputable def edgeCase23 (t H ph : ℕ) : Bool := chk [ea23] edgeQ23 0 12 (remT (unaryE ea23) t) H ph
noncomputable def edgeCase26 (t H ph : ℕ) : Bool := chk [ea26] edgeQ26 0 12 (remT (unaryE ea26) t) H ph
noncomputable def edgeCase27 (t H ph : ℕ) : Bool := chk [ea27] edgeQ27 0 12 (remT (unaryE ea27) t) H ph
noncomputable def edgeCase30 (t H ph : ℕ) : Bool := chk [ea30] edgeQ30 0 12 (remT (unaryE ea30) t) H ph
noncomputable def edgeCase32 (t H ph : ℕ) : Bool := chk [ea32] edgeQ32 0 12 (remT (unaryE ea32) t) H ph
noncomputable def edgeCase34 (t H ph : ℕ) : Bool := chk [ea34] edgeQ34 0 12 (remT (unaryE ea34) t) H ph
noncomputable def edgeCase35 (t H ph : ℕ) : Bool := chk [ea35] edgeQ35 0 12 (remT (unaryE ea35) t) H ph
def storedState (mode k t z : ℕ) (indices : List ℕ) : BState :=
  (mode,k,t,z,indices.map fun i => storedWires.getD i (0,0,0,0,0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t1m0 : edgeCase9 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t1m1 : edgeCase9 1 0x200832206c0041010c06501000a281c0330c140230000190008100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t1m2 : edgeCase9 1 0x6a08c0c100180100090000898005009c8036140444040240e0280 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t1m3 : edgeCase9 1 0x1010410003260a8800090220061c0c06042008a488803802a02800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t1m4 : edgeCase9 1 0x94500918090304681000806610000200040800003068609115405 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t1m5 : edgeCase9 1 0x20042004804207260a5c100412210009002190039004040007a 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t2m0 : edgeCase9 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep9k12t3m0 : edgeCase9 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases9 : ∀ t ∈ smallT, MaskRun ea9 edgeQ9 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x200832206c0041010c06501000a281c0330c140230000190008100, 0), (0x6a08c0c100180100090000898005009c8036140444040240e0280, 0), (0x1010410003260a8800090220061c0c06042008a488803802a02800, 0), (0x94500918090304681000806610000200040800003068609115405, 0), (0x20042004804207260a5c100412210009002190039004040007a, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep9k12t1m0
    · exact budgetRep9k12t1m1
    · exact budgetRep9k12t1m2
    · exact budgetRep9k12t1m3
    · exact budgetRep9k12t1m4
    · exact budgetRep9k12t1m5
  · exact one budgetRep9k12t2m0
  · exact one budgetRep9k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data9 : CaseData ea9 := prepSound ea9 q1_9 q2_9 extra_9 edgePrep9 budgetCases9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t1m0 : edgeCase13 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t1m1 : edgeCase13 1 0x88518021104086093404400130b9400242092920cc0a1483c0244 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t1m2 : edgeCase13 1 0x1284680a083048a00990884a0540a820140614913014a01028522 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t1m3 : edgeCase13 1 0x1202a0244a1841052c0281510880403510970800003c1496001881 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t1m4 : edgeCase13 1 0x245001590460b2104024322a44202148ca080424e0020020c16018 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t2m0 : edgeCase13 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep13k12t3m0 : edgeCase13 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases13 : ∀ t ∈ smallT, MaskRun ea13 edgeQ13 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x88518021104086093404400130b9400242092920cc0a1483c0244, 0), (0x1284680a083048a00990884a0540a820140614913014a01028522, 0), (0x1202a0244a1841052c0281510880403510970800003c1496001881, 0), (0x245001590460b2104024322a44202148ca080424e0020020c16018, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep13k12t1m0
    · exact budgetRep13k12t1m1
    · exact budgetRep13k12t1m2
    · exact budgetRep13k12t1m3
    · exact budgetRep13k12t1m4
  · exact one budgetRep13k12t2m0
  · exact one budgetRep13k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data13 : CaseData ea13 := prepSound ea13 q1_13 q2_13 extra_13 edgePrep13 budgetCases13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t1m0 : edgeCase15 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t1m1 : edgeCase15 1 0x1a0d6821ca8100005a1102240060201002104c025003826910087e 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t1m2 : edgeCase15 1 0x24e08640145202808448954321010464040210200e004812a9c281 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t1m3 : edgeCase15 1 0x11062124396a2104289050921281f1a8a14d20802000043000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t1m4 : edgeCase15 1 0x11200980008c41500a240088e0cc90a08450290817c1584420500 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t2m0 : edgeCase15 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep15k12t3m0 : edgeCase15 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases15 : ∀ t ∈ smallT, MaskRun ea15 edgeQ15 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x1a0d6821ca8100005a1102240060201002104c025003826910087e, 0), (0x24e08640145202808448954321010464040210200e004812a9c281, 0), (0x11062124396a2104289050921281f1a8a14d20802000043000, 0), (0x11200980008c41500a240088e0cc90a08450290817c1584420500, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep15k12t1m0
    · exact budgetRep15k12t1m1
    · exact budgetRep15k12t1m2
    · exact budgetRep15k12t1m3
    · exact budgetRep15k12t1m4
  · exact one budgetRep15k12t2m0
  · exact one budgetRep15k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data15 : CaseData ea15 := prepSound ea15 q1_15 q2_15 extra_15 edgePrep15 budgetCases15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m0 : edgeCase16 1 0 1 = false := by decide +kernel
def budgetRep16k12t1m1Batch0 : List BState := [storedState 1 11 1 0x2339d6b4a52d3a56759d6759d673a52939d2b39ce929529394e739ca518ca72 [0,1,2,3,4,5,6,7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m1Batch0OK : budgetRep16k12t1m1Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ16.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep16k12t1m1Batch1 : List BState := [storedState 1 11 1 0x232956b5ad2d3a52549525495694a5294a52b4a4e939d29394a539ca5294a72 [0,8,1,2,4,5,6,7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m1Batch1OK : budgetRep16k12t1m1Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ16.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep16k12t1m1Batch2 : List BState := [storedState 1 11 1 0x232a4eb5b4ed3a525495a76a4e7394a94aceb4aca93a4e9494a919ca529c672 [0,9,1,2,4,5,6,7],
  storedState 1 11 1 0x233a52b4b4ad3ad6559da56a52749ce93acab3ac692a4a9394e929ca519c272 [0,1,2,4,10,5,6,7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m1Batch2OK : budgetRep16k12t1m1Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ16.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep16k12t1m1Cache : List BState := budgetRep16k12t1m1Batch0 ++ (budgetRep16k12t1m1Batch1 ++ (budgetRep16k12t1m1Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m1Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ16.map fun _ => 16)) 12 budgetRep16k12t1m1Cache) [ea16] edgeQ16 0 12 (remT (unaryE ea16) 1) 0x202c00000040018600000408040004510000000100000000208020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m1 : edgeCase16 1 0x202c00000040018600000408040004510000000100000000208020 0 = false := by
  apply budgetMemo_join [ea16] edgeQ16 0 12 (remT (unaryE ea16) 1) 0x202c00000040018600000408040004510000000100000000208020 0 budgetRep16k12t1m1Cache _ budgetRep16k12t1m1Lookup
  intro c hc
  simp only [budgetRep16k12t1m1Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep16k12t1m1Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep16k12t1m1Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep16k12t1m1Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m2 : edgeCase16 1 0x88040904010200000005000820080000800014005008000040000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m3 : edgeCase16 1 0x114080008000000100000080000000080001020140100420e81 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m4 : edgeCase16 1 0x10002040d00000041880100200801024000000008000200001100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m5 : edgeCase16 1 0x21000400000041008000080002000200020120010011820900002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m6 : edgeCase16 1 0x10000000000002280404a044008000000012000000602090010000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m7 : edgeCase16 1 0x201201200004000000000101000008048002002000441002044 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m8 : edgeCase16 1 0x80000004080020010020000000001000000840000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m9 : edgeCase16 1 0x4000002000400002020000000040000400000600000000000008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m10 : edgeCase16 1 0x8000000060001000060084220500808082000e000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m11 : edgeCase16 1 0x8010023000110000001410138000000440000004000080010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t1m12 : edgeCase16 1 0x40020028000900080000a02004002080100a80000080000004000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t2m0 : edgeCase16 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t2m1 : edgeCase16 2 0x4a319022c08cc80248e2a97243266c8d1f03e4b4105440000a444 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t2m2 : edgeCase16 2 0x391044e40043337d924084400acc80152007408084aa8bd5ab4112 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t2m3 : edgeCase16 2 0x24ca219d3b4000249315128d10119220e0881343a50302a541aa9 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep16k12t3m0 : edgeCase16 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases16 : ∀ t ∈ smallT, MaskRun ea16 edgeQ16 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x202c00000040018600000408040004510000000100000000208020, 0), (0x88040904010200000005000820080000800014005008000040000, 0), (0x114080008000000100000080000000080001020140100420e81, 0), (0x10002040d00000041880100200801024000000008000200001100, 0), (0x21000400000041008000080002000200020120010011820900002, 0), (0x10000000000002280404a044008000000012000000602090010000, 0), (0x201201200004000000000101000008048002002000441002044, 0), (0x80000004080020010020000000001000000840000000000000, 0), (0x4000002000400002020000000040000400000600000000000008, 0), (0x8000000060001000060084220500808082000e000000, 0), (0x8010023000110000001410138000000440000004000080010, 0), (0x40020028000900080000a02004002080100a80000080000004000, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep16k12t1m0
    · exact budgetRep16k12t1m1
    · exact budgetRep16k12t1m2
    · exact budgetRep16k12t1m3
    · exact budgetRep16k12t1m4
    · exact budgetRep16k12t1m5
    · exact budgetRep16k12t1m6
    · exact budgetRep16k12t1m7
    · exact budgetRep16k12t1m8
    · exact budgetRep16k12t1m9
    · exact budgetRep16k12t1m10
    · exact budgetRep16k12t1m11
    · exact budgetRep16k12t1m12
  · refine ⟨[(0, 1), (0x4a319022c08cc80248e2a97243266c8d1f03e4b4105440000a444, 0), (0x391044e40043337d924084400acc80152007408084aa8bd5ab4112, 0), (0x24ca219d3b4000249315128d10119220e0881343a50302a541aa9, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact budgetRep16k12t2m0
    · exact budgetRep16k12t2m1
    · exact budgetRep16k12t2m2
    · exact budgetRep16k12t2m3
  · exact one budgetRep16k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data16 : CaseData ea16 := prepSound ea16 q1_16 q2_16 extra_16 edgePrep16 budgetCases16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m0 : edgeCase18 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m1 : edgeCase18 1 0x288040028084bd04e4a009282a0b6080a3018040082003037420c0 0 = false := by decide +kernel
def budgetRep18k12t1m2Batch0 : List BState := [storedState 1 11 1 0x214a4eb4ad2b3ad695a56b5a4e7394e94ad2b4ace92a569494e719ca529ca72 [0,1,2,11,4,5,6],
  storedState 1 11 1 0x214a5294ace73ad673a5693a527494e73a4eb4aca52a529494e7294a529c632 [0,1,2,4,5,6,12,13]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m2Batch0OK : budgetRep18k12t1m2Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ18.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep18k12t1m2Batch1 : List BState := [storedState 1 11 1 0x214a4e74ad293ad694a56b4a4e5394a529ceb4ace72a569494e718ca529ca52 [0,1,2,14,4,5,6,12],
  storedState 1 11 1 0x212a56b3ad6b29ce73956d59d675a4e93ad6729ca51a5a73946739c2519ce71 [0,15,1,2,4,5,6,12],
  storedState 1 11 1 0x2149d6949d673a56b3a52b39d693952739d2b49d25295a9294e5394a528ce32 [0,1,2,4,5,6,12,16],
  storedState 1 11 1 0x21495674a56939d6b4a4e93956949d2529ceb4a52729da9394e338ca5294e52 [0,1,17,2,4,5,6,12],
  storedState 1 11 1 0x212956b3a56b39ce7394e9395674a5293a56b3a52919da92946339ca5194e72 [0,8,1,2,4,5,6,12]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m2Batch1OK : budgetRep18k12t1m2Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ18.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep18k12t1m2Batch2 : List BState := [storedState 1 11 1 0x2139d6b29d6b39d2949d2b49d653a52929d6b29d29095a9294a539ca508ce72 [0,1,2,3,4,5,6,12],
  storedState 1 11 1 0x214a52b4aceb1ad67595695952749ca94ace93a4a72a525494e729c6529c670 [0,1,2,4,5,6,12,18],
  storedState 1 11 1 0x214a4eb4ad2b2ad6959d6b59ce5394a94ad2729ca52a567494e719c2529ca71 [0,1,2,19,4,5,6,12],
  storedState 1 11 1 0x21294e729ce719d2b5a4e9395294a5274a5694a52919567384e339ca3294e72 [20,0,1,2,4,5,6,12],
  storedState 1 11 1 0x213952939d292a4eb5a4eb49ce93a52549d6749d290952528ce539ca128ce72 [0,1,2,21,4,5,6,12],
  storedState 1 11 1 0x213a56b4ad6b2a52949d6d59d695a4e94ad6739ca52a5a7494a739c2529ce71 [0,15,2,4,5,6,12],
  storedState 1 11 1 0x212a56b3ad6b39ce739d6d5a5675a5293ad693a4e71a5a93946739c6519ce72 [0,15,1,2,4,5,12],
  storedState 1 11 1 0x213a56b4ad6b3a5294a56d5a5695a5294ad694a4e72a5a9494a739c6529ce72 [0,15,2,4,5,12]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m2Batch2OK : budgetRep18k12t1m2Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ18.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep18k12t1m2Cache : List BState := budgetRep18k12t1m2Batch0 ++ (budgetRep18k12t1m2Batch1 ++ (budgetRep18k12t1m2Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m2Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ18.map fun _ => 16)) 12 budgetRep18k12t1m2Cache) [ea18] edgeQ18 0 12 (remT (unaryE ea18) 1) 0x4211e88034000c21a547092c084065114b4000115042880018408 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m2 : edgeCase18 1 0x4211e88034000c21a547092c084065114b4000115042880018408 0 = false := by
  apply budgetMemo_join [ea18] edgeQ18 0 12 (remT (unaryE ea18) 1) 0x4211e88034000c21a547092c084065114b4000115042880018408 0 budgetRep18k12t1m2Cache _ budgetRep18k12t1m2Lookup
  intro c hc
  simp only [budgetRep18k12t1m2Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep18k12t1m2Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep18k12t1m2Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep18k12t1m2Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m3 : edgeCase18 1 0x34e21656c204208000306041130912008404206429100288a1a04 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t1m4 : edgeCase18 1 0x10108010101b0031010880410440080e400a3db8a04ad454004133 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t2m0 : edgeCase18 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep18k12t3m0 : edgeCase18 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases18 : ∀ t ∈ smallT, MaskRun ea18 edgeQ18 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x288040028084bd04e4a009282a0b6080a3018040082003037420c0, 0), (0x4211e88034000c21a547092c084065114b4000115042880018408, 0), (0x34e21656c204208000306041130912008404206429100288a1a04, 0), (0x10108010101b0031010880410440080e400a3db8a04ad454004133, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep18k12t1m0
    · exact budgetRep18k12t1m1
    · exact budgetRep18k12t1m2
    · exact budgetRep18k12t1m3
    · exact budgetRep18k12t1m4
  · exact one budgetRep18k12t2m0
  · exact one budgetRep18k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data18 : CaseData ea18 := prepSound ea18 q1_18 q2_18 extra_18 edgePrep18 budgetCases18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t1m0 : edgeCase19 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t1m1 : edgeCase19 1 0x12600361011888018934108034b00048472a0c7004e0009406022 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t1m2 : edgeCase19 1 0x1e1130c882a650420020b00508b4561020004100cb003402b21000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t1m3 : edgeCase19 1 0x20c04e014c402310a74000628000a02302040c101010c3240c8b15 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t1m4 : edgeCase19 1 0x881002108042d400c0e90740009c85989122824a108d00104c8 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t2m0 : edgeCase19 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep19k12t3m0 : edgeCase19 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases19 : ∀ t ∈ smallT, MaskRun ea19 edgeQ19 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x12600361011888018934108034b00048472a0c7004e0009406022, 0), (0x1e1130c882a650420020b00508b4561020004100cb003402b21000, 0), (0x20c04e014c402310a74000628000a02302040c101010c3240c8b15, 0), (0x881002108042d400c0e90740009c85989122824a108d00104c8, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep19k12t1m0
    · exact budgetRep19k12t1m1
    · exact budgetRep19k12t1m2
    · exact budgetRep19k12t1m3
    · exact budgetRep19k12t1m4
  · exact one budgetRep19k12t2m0
  · exact one budgetRep19k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data19 : CaseData ea19 := prepSound ea19 q1_19 q2_19 extra_19 edgePrep19 budgetCases19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m0 : edgeCase20 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m1 : edgeCase20 1 0x300010400040840100040004040308290010104050a4012800148 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m2 : edgeCase20 1 0x60402020a02004c0110081050003210040000120041808051000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m3 : edgeCase20 1 0x2000080014010010044014400a3000104908002042500201500c00 0 = false := by decide +kernel
def budgetRep20k12t1m4Batch0 : List BState := [storedState 1 11 1 0x2139d6b4a52949d273ad273ad6739d6939d2d4a4e72952b494a539ce5294a34 [0,1,2,3,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m4Batch0OK : budgetRep20k12t1m4Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t1m4Batch1 : List BState := [storedState 1 11 1 0x214a4e76b4e74ad673b5673b4e738ce539cad6b4a54a4eb694e718ce54a4614 [0,1,2,14,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m4Batch1OK : budgetRep20k12t1m4Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t1m4Batch2 : List BState := [storedState 1 11 1 0x212a56b5b52949ce73a5694b56959d694ad2d5b4e73a52b5946739ce53a4a34 [0,23,1,2,4,5,6],
  storedState 1 11 1 0x212956b5ad2949ce52a4e52a56949d694a52d5ace739d2b4946339ce539ca34 [0,8,1,2,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m4Batch2OK : budgetRep20k12t1m4Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t1m4Batch3 : List BState := [storedState 1 11 1 0x214a5276b5274ad693b5693b5294952539ced6b4e54a52b694e728ce54a4a14 [0,1,2,14,5,6,22],
  storedState 1 11 1 0x214a4e96b4e94ad674b5674b4e7394e74a4ed6b4a74a4eb694e7194e54a4634 [0,1,2,14,4,6,22],
  storedState 1 11 1 0x214a5296b5294ad694b5694b52949d274a52d6b4e74a52b694e7294e54a4a34 [0,1,2,14,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m4Batch3OK : budgetRep20k12t1m4Batch3.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t1m4Cache : List BState := budgetRep20k12t1m4Batch0 ++ (budgetRep20k12t1m4Batch1 ++ (budgetRep20k12t1m4Batch2 ++ (budgetRep20k12t1m4Batch3)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m4Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 budgetRep20k12t1m4Cache) [ea20] edgeQ20 0 12 (remT (unaryE ea20) 1) 0x22000000808800040000000000440090000008010140000010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m4 : edgeCase20 1 0x22000000808800040000000000440090000008010140000010 0 = false := by
  apply budgetMemo_join [ea20] edgeQ20 0 12 (remT (unaryE ea20) 1) 0x22000000808800040000000000440090000008010140000010 0 budgetRep20k12t1m4Cache _ budgetRep20k12t1m4Lookup
  intro c hc
  simp only [budgetRep20k12t1m4Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t1m4Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t1m4Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t1m4Batch2OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t1m4Batch3OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m5 : edgeCase20 1 0x8000080000000008200902000900000200008800008080002004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m6 : edgeCase20 1 0x140400810200400001000010008480080420d04280a00024024083 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m7 : edgeCase20 1 0x8181450880002020008822410020c000006220000002400208220 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t1m8 : edgeCase20 1 0x38002415a152122822008a000400020000c1010000000080000 0 = false := by decide +kernel
def budgetRep20k12t2m0Batch0 : List BState := [storedState 1 11 2 0x2139d295ad293ad694b5694b56b59d695ad2d6b4e74a52b68ce739ce54a4a34 [24,1,2,4,5,6],
  storedState 1 11 2 0x214a56b6b5293ad694ad694ad6b59d295ad294a4a54a529694e739c654a4a33 [0,1,2,4,5,25,6],
  storedState 1 11 2 0x212a56b5b52949ce73a5694b56959d694ad2d5b4e73a52b5946739ce53a4a34 [0,23,1,2,4,5,6],
  storedState 1 11 2 0x214956b6ad2949d694b4e73a56b49d695a52d6ace749d2b594e339ce549ca34 [0,1,26,2,4,5,6],
  storedState 1 11 2 0x212956b5ad2949ce52a4e52a56949d694a52d5ace739d2b4946339ce539ca34 [0,8,1,2,4,5,6,22],
  storedState 1 11 2 0x212a56b5b52939ce52a5694ad6959d294ad294a4633a5295946739c653a4a33 [0,15,1,2,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0Batch0OK : budgetRep20k12t2m0Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t2m0Batch1 : List BState := [storedState 1 11 2 0x2139d6b4a52949d273ad273ad6739d6939d2d4a4e72952b494a539ce5294a34 [0,1,2,3,4,5,6,22],
  storedState 1 11 2 0x214956b6ad2939d694ace52a56b49d295a5294a46349d29594e339c6549ca33 [0,1,27,2,4,5,6,22],
  storedState 1 11 2 0x21294e74a4e72ad294b5294b52b59d675ad2b6b4e739ce9684e739ce34a4a34 [24,0,1,2,4,5,6],
  storedState 1 11 2 0x213a56b4b5292a5273a5694a56759ce93ad2b4aca52a527494a739ca52a4a32 [0,1,2,4,5,6,28,22],
  storedState 1 11 2 0x2149d6b6a5292a5694a5273a56b39ce959d2b5a4a549527494e539ca5494a32 [0,1,2,4,5,6,29,22],
  storedState 1 11 2 0x214a4eb6b4e93ad674ad674ace738ce95ace94a4634a4e9694e719c654a4633 [0,1,2,19,4,5,6,22],
  storedState 1 11 2 0x2139d295ace72ace94a4e94a4eb59ce55ad295aca5294a768ce739ca14a4a32 [0,1,2,4,5,6,30,22],
  storedState 1 11 2 0x214a4e96b4e94ad674b5674b4e7394e74a4ed6b4a74a4eb694e7194e54a4634 [0,1,2,14,4,6,22],
  storedState 1 11 2 0x214a52b6b4a92ad654a5654a529494e95acab5ac654a4a7694e729ca54a4232 [0,1,2,4,5,6,22,18],
  storedState 1 11 2 0x2129d294ace73a4e73ace94b4e759d653ad294b4e7294a748ca739ce12a4a34 [0,1,31,2,4,5,6,22],
  storedState 1 11 2 0x21395295a4e73a4e94b4e73aceb39d6559d296a4e7294a748ce539ce1494a34 [0,1,2,21,4,5,6,22],
  storedState 1 11 2 0x213a52b4b4a94a5253ad654b527495293acad4b4672a4ab494a729ce52a4234 [0,1,2,4,10,5,6,22],
  storedState 1 11 2 0x2149d2b6a4a94a5654b5253ad293952959cad6a467494ab494e529ce5494234 [0,1,2,4,5,6,32,22],
  storedState 0 10 1 0x212a56b3b52949ce52a5694b56559d692ad2d3b4e71a52b3946739ce51a4a34 [0,1,2,4,5,6,33],
  storedState 0 10 1 0x214956b69d2949d694b4e52a56b29d695952d69ce748d2b394e339ce548ca34 [0,1,2,34,4,5,6],
  storedState 1 11 2 0x212a4eb5b4e949ce52a5674b4e738ce94aced5b4a73a4eb5946719ce53a4634 [0,9,1,2,4,5,6,22],
  storedState 1 11 2 0x212a5675b52749ce52a5693b5695956539cad5b4e53a52b5946738ce53a4a14 [0,35,1,2,4,5,6,22],
  storedState 1 11 2 0x214a4e76b4e74ad673b5673b4e738ce539cad6b4a54a4eb694e718ce54a4614 [0,1,2,14,4,5,6,22],
  storedState 1 11 2 0x214a5276b5274ad693b5693b5294952539ced6b4e54a52b694e728ce54a4a14 [0,1,2,14,5,6,22],
  storedState 0 10 1 0x212a56b3b52949ce52a5694b56559d692ad2d3b4e71a52b3946739ce51a4a34 [0,2,4,5,6,33,36],
  storedState 0 10 1 0x214956b69d2949d694b4e52a56b29d695952d69ce748d2b394e339ce548ca34 [0,1,34,37,4,5,6],
  storedState 0 10 1 0x214a56b6b5291ad6949d6949d6b59ca95ad294a4634a525694e739c654a4a31 [0,1,38,2,4,5,6],
  storedState 1 11 2 0x21294e74a4a52ad294ad294ad2b59d275ad294a46339ce7684e739c634a4a33 [39,0,1,2,4,5,6,22],
  storedState 1 11 2 0x2139ce95aca73ace54b4e54b4e9495255aca96b467294a768ce729ce14a4234 [0,1,2,4,40,5,6,22],
  storedState 1 11 2 0x21494eb6ace949d674b4e52a4e738ce95a4ed6aca749ceb594e319ce549c634 [0,1,41,2,4,5,6,22],
  storedState 1 11 2 0x21495676ad2749d693b4e52a56b4956539cad6ace549d2b594e338ce549ca14 [0,1,17,2,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0Batch1OK : budgetRep20k12t2m0Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t2m0Batch2 : List BState := [storedState 1 11 2 0x214a5676b5273ad693ad693ad6b5952539ca94a4634a529694e738c654a4a13 [0,1,2,4,42,5,6,22],
  storedState 0 10 1 0x212956b3ad29494e52a4e52a56549d692a52d3ace719d2b3946339ce519ca34 [0,43,2,4,5,6,36,22],
  storedState 0 10 1 0x212956b3ad29494e52a4e52a56549d692a52d3ace719d2b3946339ce519ca34 [0,1,43,2,4,5,6,22],
  storedState 0 10 1 0x212956b59d29494e52a4e52a56929d694952d59ce738d2b3946339ce538ca34 [0,44,1,37,4,5,6,22],
  storedState 1 11 2 0x21294e74a4a529ce52a5294b52959d674ad2b5b4e729ce95846739ce33a4a34 [45,0,1,2,4,5,6,22],
  storedState 1 11 2 0x21294e74a4a52ad293b5293b52b5956539cab6b4e539ce9684e738ce34a4a14 [46,0,1,2,4,5,6,22],
  storedState 0 9 0 0x211a4ab4b4a9494a119d654b4a3284a93acad4b4672a4ab4942709ce52a4234 [0,1,2,4,5,6,47,22],
  storedState 0 9 0 0x211a56b4b529294a3195694a56759ce93ad2729c212a5274942739c252a4a32 [0,1,2,4,5,6,48,22],
  storedState 0 10 1 0x21194e73a4a529ca52a5294b52559d672ad2b3b4e719ce93846739ce31a4a34 [49,0,2,4,5,6,36,22],
  storedState 0 10 1 0x2119d293ace7394a319ce94b4e759d653ad294b4e7194a748c2739ce12a4a34 [0,2,4,5,6,36,50,22],
  storedState 0 10 1 0x2119d293ace7394a319ce94b4e759d653ad294b4e7194a748c2739ce12a4a34 [0,1,2,4,5,6,50,22],
  storedState 0 10 1 0x2119d6b4a529494a319d273ad6739d6939d2d4a4e72952b3942539ce5294a34 [0,2,4,5,6,36,51,22],
  storedState 0 10 1 0x2119d6b4a529494a319d273ad6739d6939d2d4a4e72952b3942539ce5294a34 [0,1,2,4,5,6,51,22],
  storedState 0 10 1 0x211a56b4b529294a319d694a56759ce93ad2b3aca52a5274942739ca52a4a32 [0,2,4,5,6,36,52,22],
  storedState 0 10 1 0x211a56b4b529294a319d694a56759ce93ad2b3aca52a5274942739ca52a4a32 [0,1,2,4,5,6,52,22],
  storedState 0 10 1 0x2128ce749ca529d294b4a52a52b29d675952b69ce738ce9384e339ce348ca34 [53,0,1,2,4,5,6,22],
  storedState 0 10 1 0x21294e74a4a51ad2949d2949d2b59ca75ad274a46339ce5684e739c634a4a31 [54,0,1,55,2,4,5,22],
  storedState 0 10 1 0x212956b59d29494e52a4e52a56929d694952d59ce738d2b3946339ce538ca34 [0,44,1,2,4,5,6,22],
  storedState 0 10 1 0x212a4eb3b4e949ce32a5674b4e538ce92aced3b4a71a4eb3946719ce51a4634 [0,2,56,4,5,6,36,22],
  storedState 0 10 1 0x212a5673b52749ce51a5693b5655956529cad3b4e51a52b3946738ce51a4a14 [0,1,2,4,57,5,6,22],
  storedState 0 10 1 0x212a56b3b52939ce529d694ad6559d292ad293a4631a5293946739c651a4a33 [0,2,4,5,58,6,36,22],
  storedState 0 10 1 0x212a56b5b52919ce529d6949d6959ca94ad293a4633a5255946739c653a4a31 [0,59,1,2,4,5,6,22],
  storedState 0 10 1 0x212a56b5b52919ce529d6949d6959ca94ad293a4633a5255946739c653a4a31 [0,59,1,55,2,4,5,22],
  storedState 0 10 1 0x2138d2959ce7394e94b4a319ceb39d6559d296a4e728ca748ce139ce1494a34 [0,1,37,60,4,5,6,22],
  storedState 0 10 1 0x2138d6b4a529495273aca319d6739d6939d2d4a4e72952b394a139ce5294a34 [0,1,37,61,4,5,6,22],
  storedState 0 10 1 0x2138d6b4a529495273aca319d6739d6939d2d4a4e72952b394a139ce5294a34 [0,1,2,61,4,5,6,22],
  storedState 0 10 1 0x2139ca95ac673ace54b4e54b4a5284a55aca96b4672946768ce709ce14a4234 [0,1,62,63,2,5,6,22],
  storedState 0 10 1 0x213a4ab4b4a94a5233ad654b4a5284a93acad4b4672a4ab494a709ce52a4234 [0,1,64,2,4,5,6,22],
  storedState 0 10 1 0x213a56b4b5292a52739d694a56759ce93ad2739c212a527494a739c252a4a32 [0,1,55,65,2,4,5,22],
  storedState 0 10 1 0x2148d2b6a4a9495654b4a319d292952959cad6a467494ab494e129ce5494234 [0,1,2,4,66,5,6,22],
  storedState 0 10 1 0x2148d6b69529495694b4a319d6b19d6958d2d694e74852b294e139ce5484a34 [0,1,2,34,37,4,5,6],
  storedState 0 10 1 0x2148d6b6a529295694a4a319d6b39ce959d2b59ca549527494e139ca5494a32 [0,1,2,4,5,6,67,22],
  storedState 0 10 1 0x214956769d2749d693b4e51a56b29565394ad69ce548d2b394e338ce548ca14 [0,1,68,37,4,5,6,22],
  storedState 0 10 1 0x214956b69d2939d694ace529d6b29d295952949c6348d29394e339c6548ca33 [0,1,69,37,4,5,6,22],
  storedState 0 10 1 0x214956b69d2939d694ace529d6b29d295952949c6348d29394e339c6548ca33 [0,1,2,69,4,5,6,22],
  storedState 0 10 1 0x214956b6ad2919d6949ce529d6b49ca95a52949c6349d25594e339c6549ca31 [0,1,70,2,4,5,6,22],
  storedState 0 10 1 0x214956b6ad2919d6949ce529d6b49ca95a52949c6349d25594e339c6549ca31 [0,1,70,55,2,4,5,22],
  storedState 0 10 1 0x2149d6b6a5292a5694a52739d6b39ce959d2739c2149527494e539c25494a32 [0,1,2,71,4,5,6,22],
  storedState 0 10 1 0x214a4ab6b4a92ad654a5654a4a5284a95acab5ac254a4a7694e709ca54a4232 [0,1,62,2,5,6,72,22],
  storedState 0 10 1 0x214a4eb6b4a94ad654b5654b4e738ce95acad6b4674a4ab694e719ce54a4234 [0,1,73,2,4,5,6],
  storedState 0 10 1 0x214a4eb6b4a94ad654b5654b4e738ce95acad6b4674a4ab694e719ce54a4234 [0,1,73,62,2,5,6],
  storedState 0 10 1 0x214a52b6b4a92ad654a5654a529494a95aca739c214a4a7694e729c254a4232 [0,1,55,2,4,74,5,22],
  storedState 0 10 1 0x214a5676b5271ad6939d6939d6b594a539ca94a4614a525694e738c654a4a11 [0,1,75,2,4,5,6,22],
  storedState 0 10 1 0x214a5676b5271ad6939d6939d6b594a539ca94a4614a525694e738c654a4a11 [0,1,75,55,2,4,5,22],
  storedState 0 10 1 0x214a56b6b5290ad69495694956b59c695ad2739c214a523694e739c254a4a30 [0,1,38,55,2,4,5,6],
  storedState 0 10 1 0x214a56b6b5291ad6949d6949d6b59ca95ad294a4634a525694e739c654a4a31 [0,1,38,55,2,4,5],
  storedState 1 11 2 0x21294e74a4a529d294b4e52a52b49d675a52b6ace7394e9584e339ce349ca34 [20,0,1,2,4,5,6,22],
  storedState 1 11 2 0x21294e74a4a52ad274b5274b4e738ce75aceb6b4a739ca9684e719ce34a4634 [76,0,1,2,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0Batch2OK : budgetRep20k12t2m0Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t2m0Batch3 : List BState := [storedState 0 9 0 0x2118d6b4a52948ca319ca319d6739d6939d2d4a4e72952b2942139ce5294a34 [0,1,2,4,5,6,77,22],
  storedState 0 9 0 0x211956b29d29484a319ce52a56329d691952d29ce708d2b1942339ce508ca34 [0,1,2,78,4,5,6,36,22],
  storedState 0 9 0 0x211a56b2b529094a3185694956359c691ad2709c210a5232942739c250a4a30 [0,1,79,55,2,4,5,6,36,22],
  storedState 0 9 0 0x211a56b2b529194a318d6949d6359ca91ad291a4630a5252942739c650a4a31 [0,1,79,2,4,5,6,36,22],
  storedState 0 9 0 0x2128d6b39529484e52a4a319d6519d6928d2d394e71852b1946139ce5184a34 [0,1,2,78,37,4,5,6,22],
  storedState 0 9 0 0x212956b39d2948ce52a4e52a56529d692952d39ce718d2b2946339ce518ca34 [0,1,2,78,4,5,6,22],
  storedState 0 9 0 0x212a56b3b52909ce528d694956559c692ad2719c211a5233946739c251a4a30 [0,1,79,55,2,4,5,6,22],
  storedState 0 9 0 0x212a56b3b52919ce52956949d6559ca92ad292a4631a5253946739c651a4a31 [0,1,79,2,4,5,6,22],
  storedState 0 9 0 0x2148cab6a4a9495654b4a119ca5184a959cad6a467494ab494e109ce5494234 [0,1,2,4,80,5,6,22],
  storedState 0 9 0 0x2148d6b6952909569494a31856b19c6958d273842148523294e139c25484a30 [0,81,1,55,2,37,4,5,6,22],
  storedState 0 9 0 0x2148d6b695291956949ca318d6b19ca958d2948c6348525294e139c65484a31 [0,81,1,2,37,4,5,6,22],
  storedState 0 9 0 0x2148d6b6a529295694a4a31956b39ce959d273942149527494e139c25494a32 [0,1,2,82,4,5,6,22],
  storedState 0 9 0 0x214956b69d2909d69494e528d6b29c695952738c2148d23394e339c2548ca30 [0,81,1,55,2,4,5,6,22],
  storedState 0 9 0 0x214956b69d2919d6949ce52956b29ca9595294946348d25394e339c6548ca31 [0,81,1,2,4,5,6,22],
  storedState 0 10 1 0x21094e72a4a52946319d294b52359d671ad2b2b4e709ce92842739ce30a4a34 [49,0,1,2,4,5,6,36,22],
  storedState 0 10 1 0x21194e73a4a529ca52a5294b52559d672ad2b3b4e719ce93846739ce31a4a34 [49,0,1,2,4,5,6,22],
  storedState 0 10 1 0x211956b2ad2948ca319ce52a56349d691a52d2ace709d2b2942339ce509ca34 [0,1,43,2,4,5,6,36,22],
  storedState 0 10 1 0x211a4eb2b4e9494a119d674b4e338ce91aced2b4a70a4eb2942719ce50a4634 [0,1,2,56,4,5,6,36,22],
  storedState 0 10 1 0x211a52b4b4a9494a319d654b525495293acad4b4672a4ab4942729ce52a4234 [0,2,4,5,6,36,83,22],
  storedState 0 10 1 0x211a52b4b4a9494a319d654b525495293acad4b4672a4ab4942729ce52a4234 [0,1,2,4,5,6,83,22],
  storedState 0 10 1 0x211a5672b527494a309d693b5635956519cad2b4e50a52b2942738ce50a4a14 [0,1,2,4,57,5,6,36,22],
  storedState 0 10 1 0x211a56b2b529394a3195694ad6359d291ad292a4630a5292942739c650a4a33 [0,1,2,4,5,58,6,36,22],
  storedState 0 10 1 0x211a56b2b529494a319d694b56359d691ad2d2b4e70a52b2942739ce50a4a34 [0,1,2,4,5,6,33,36],
  storedState 0 10 1 0x21284e7494a5295294b46319d2b19d6758d2b694e7384e9284e139ce3484a34 [53,0,1,2,37,4,5,6,22],
  storedState 0 10 1 0x2128ce749ca529d294b4a52a52b29d675952b69ce738ce9384e339ce348ca34 [53,0,1,37,4,5,6,22],
  storedState 0 10 1 0x2128d6b5952948ce52a4a319d6919d6948d2d594e73852b2946139ce5384a34 [0,44,1,2,37,4,5,6,22],
  storedState 0 10 1 0x21294e74a4a50ad29495294952b59c675ad2539c2139ce3684e739c234a4a30 [54,0,1,55,2,4,5,6,22],
  storedState 0 10 1 0x21294e74a4a51ad2949d2949d2b59ca75ad274a46339ce5684e739c634a4a31 [54,0,1,2,4,5,6,22],
  storedState 0 10 1 0x212a4eb3b4e949ce32a5674b4e538ce92aced3b4a71a4eb3946719ce51a4634 [0,1,2,56,4,5,6,22],
  storedState 0 10 1 0x212a5673b52749ce51a5693b5655956529cad3b4e51a52b3946738ce51a4a14 [0,2,4,57,5,6,36,22],
  storedState 0 10 1 0x212a56b3b52939ce529d694ad6559d292ad293a4631a5293946739c651a4a33 [0,1,2,4,5,58,6,22],
  storedState 0 10 1 0x212a56b5b52909ce5295694956959c694ad2729c213a5235946739c253a4a30 [0,59,1,55,2,4,5,6,22],
  storedState 0 10 1 0x2138d2959ce7394e94b4a319ceb39d6559d296a4e728ca748ce139ce1494a34 [0,1,2,60,4,5,6,22],
  storedState 0 10 1 0x2139ca95ac673ace54b4e54b4a5284a55aca96b4672946768ce709ce14a4234 [0,1,63,2,4,5,6,22],
  storedState 0 10 1 0x2139d295ace71ace94a4e94a4eb59ce55ad2739c21294a568ce739c214a4a32 [0,1,84,2,4,5,6,22],
  storedState 0 10 1 0x2139d295ace71ace94a4e94a4eb59ce55ad2739c21294a568ce739c214a4a32 [0,1,55,84,2,4,5,22],
  storedState 0 10 1 0x2139d295ace73ace94b4e94b4eb59d655ad296b4e7294e768ce739ce14a4a34 [1,2,4,5,6,85],
  storedState 0 10 1 0x213a4ab4b4a94a5233ad654b4a5284a93acad4b4672a4ab494a709ce52a4234 [0,1,62,64,2,5,6,22],
  storedState 0 10 1 0x213a56b4b5292a52739d694a56759ce93ad2739c212a527494a739c252a4a32 [0,1,65,2,4,5,6,22],
  storedState 0 10 1 0x2148ceb694e9495674b4a119ce718ce958ced694a7484eb294e119ce5484634 [0,1,2,86,37,4,5,6,22],
  storedState 0 10 1 0x2148d2b6a4a9495654b4a319d292952959cad6a467494ab494e129ce5494234 [0,1,37,4,66,5,6,22],
  storedState 0 10 1 0x2148d6769527495693b4a309d6b1956538cad694e54852b294e138ce5484a14 [0,1,2,68,37,4,5,6,22],
  storedState 0 10 1 0x2148d6b69529395694aca31956b19d2958d294946348529294e139c65484a33 [0,1,2,69,37,4,5,6,22],
  storedState 0 10 1 0x2148d6b6a529295694a4a319d6b39ce959d2b59ca549527494e139ca5494a32 [0,1,37,4,5,6,67,22],
  storedState 0 10 1 0x21494eb69ce949d674b4e32a4e728ce9594ed69ca748ceb394e319ce548c634 [0,1,86,37,4,5,6,22],
  storedState 0 10 1 0x21494eb69ce949d674b4e32a4e728ce9594ed69ca748ceb394e319ce548c634 [0,1,2,86,4,5,6,22],
  storedState 0 10 1 0x214956769d2749d693b4e51a56b29565394ad69ce548d2b394e338ce548ca14 [0,1,2,68,4,5,6,22],
  storedState 0 10 1 0x214956b6ad2909d69494e52956b49c695a5273942149d23594e339c2549ca30 [0,1,70,55,2,4,5,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0Batch3OK : budgetRep20k12t2m0Batch3.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t2m0Batch4 : List BState := [storedState 0 10 1 0x2149cab6a4a94a5654b5233aca5284a959cad6a467494ab494e509ce5494234 [0,1,2,87,4,5,6,22],
  storedState 0 10 1 0x2149cab6a4a94a5654b5233aca5284a959cad6a467494ab494e509ce5494234 [0,1,62,2,87,5,6,22],
  storedState 0 10 1 0x2149d6b6a5292a5694a52739d6b39ce959d2739c2149527494e539c25494a32 [0,1,55,2,71,4,5,22],
  storedState 0 10 1 0x214a4ab6b4a74ad653b5653b4a528ca95acad6b4654a4ab694e709ce54a4214 [0,1,2,4,88,6,22],
  storedState 0 10 1 0x214a4ab6b4a74ad653b5653b4a528ca95acad6b4654a4ab694e709ce54a4214 [0,1,62,2,88,6,22],
  storedState 0 10 1 0x214a4ab6b4a92ad654a5654a4a5284a95acab5ac254a4a7694e709ca54a4232 [0,1,2,4,5,6,72,22],
  storedState 0 10 1 0x214a4eb6b4e91ad6749d6749ce738ca95ace94a4234a4e5694e719c654a4631 [0,1,89,2,4,5,6,22],
  storedState 0 10 1 0x214a4eb6b4e91ad6749d6749ce738ca95ace94a4234a4e5694e719c654a4631 [0,1,89,55,2,4,5,22],
  storedState 0 10 1 0x214a5276b4a74ad653b5653b52948d2539cad6b4654a4ab694e728ce54a4214 [0,1,90,2,5,6,22],
  storedState 0 10 1 0x214a52b6b4a92ad654a5654a529494a95aca739c214a4a7694e729c254a4232 [0,1,2,4,74,5,6,22],
  storedState 0 10 1 0x214a52b6b4e94ad674b5674b529495295aced6b4a74a4eb694e729ce54a4634 [0,1,73,2,5,6],
  storedState 0 10 1 0x214a5696b5274ad693b5693b56b595674a4ed6b4e54a52b694e7394e54a4a14 [0,1,91,2,4,6],
  storedState 1 11 2 0x214a5296b5294ad694b5694b52949d274a52d6b4e74a52b694e7294e54a4a34 [0,1,2,14,6,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0Batch4OK : budgetRep20k12t2m0Batch4.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep20k12t2m0Cache : List BState := budgetRep20k12t2m0Batch0 ++ (budgetRep20k12t2m0Batch1 ++ (budgetRep20k12t2m0Batch2 ++ (budgetRep20k12t2m0Batch3 ++ (budgetRep20k12t2m0Batch4))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ20.map fun _ => 16)) 12 budgetRep20k12t2m0Cache) [ea20] edgeQ20 0 12 (remT (unaryE ea20) 2) 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t2m0 : edgeCase20 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by
  apply budgetMemo_join [ea20] edgeQ20 0 12 (remT (unaryE ea20) 2) 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 budgetRep20k12t2m0Cache _ budgetRep20k12t2m0Lookup
  intro c hc
  simp only [budgetRep20k12t2m0Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t2m0Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t2m0Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t2m0Batch2OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t2m0Batch3OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep20k12t2m0Batch4OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep20k12t3m0 : edgeCase20 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases20 : ∀ t ∈ smallT, MaskRun ea20 edgeQ20 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x300010400040840100040004040308290010104050a4012800148, 0), (0x60402020a02004c0110081050003210040000120041808051000, 0), (0x2000080014010010044014400a3000104908002042500201500c00, 0), (0x22000000808800040000000000440090000008010140000010, 0), (0x8000080000000008200902000900000200008800008080002004, 0), (0x140400810200400001000010008480080420d04280a00024024083, 0), (0x8181450880002020008822410020c000006220000002400208220, 0), (0x38002415a152122822008a000400020000c1010000000080000, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep20k12t1m0
    · exact budgetRep20k12t1m1
    · exact budgetRep20k12t1m2
    · exact budgetRep20k12t1m3
    · exact budgetRep20k12t1m4
    · exact budgetRep20k12t1m5
    · exact budgetRep20k12t1m6
    · exact budgetRep20k12t1m7
    · exact budgetRep20k12t1m8
  · exact one budgetRep20k12t2m0
  · exact one budgetRep20k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data20 : CaseData ea20 := prepSound ea20 q1_20 q2_20 extra_20 edgePrep20 budgetCases20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t1m0 : edgeCase21 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t1m1 : edgeCase21 1 0x9802202084028010021310602abe120205822009044540cad0d6 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t1m2 : edgeCase21 1 0x3023b55099719114244c40200440002010403018e0c800a5002300 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t1m3 : edgeCase21 1 0x104088100082c2b08008c0b1b004108c992098716030208310809 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t1m4 : edgeCase21 1 0xe40400e46024040c3b120c4809500c5242844400030b812040420 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t2m0 : edgeCase21 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep21k12t3m0 : edgeCase21 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases21 : ∀ t ∈ smallT, MaskRun ea21 edgeQ21 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x9802202084028010021310602abe120205822009044540cad0d6, 0), (0x3023b55099719114244c40200440002010403018e0c800a5002300, 0), (0x104088100082c2b08008c0b1b004108c992098716030208310809, 0), (0xe40400e46024040c3b120c4809500c5242844400030b812040420, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep21k12t1m0
    · exact budgetRep21k12t1m1
    · exact budgetRep21k12t1m2
    · exact budgetRep21k12t1m3
    · exact budgetRep21k12t1m4
  · exact one budgetRep21k12t2m0
  · exact one budgetRep21k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data21 : CaseData ea21 := prepSound ea21 q1_21 q2_21 extra_21 edgePrep21 budgetCases21
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep23k12t1m0 : edgeCase23 1 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep23k12t2m0 : edgeCase23 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep23k12t3m0 : edgeCase23 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases23 : ∀ t ∈ smallT, MaskRun ea23 edgeQ23 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact one budgetRep23k12t1m0
  · exact one budgetRep23k12t2m0
  · exact one budgetRep23k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data23 : CaseData ea23 := prepSound ea23 q1_23 q2_23 extra_23 edgePrep23 budgetCases23
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep26k12t1m0 : edgeCase26 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep26k12t1m1 : edgeCase26 1 0x1044f5229024125a1e310a92a3a902cb10115f0442840092414b81 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep26k12t1m2 : edgeCase26 1 0x2989085c668300a1418864210c52bc202ce8a0820d3ad445860402 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep26k12t1m3 : edgeCase26 1 0x63202810958ed04a046914c50044114c3060079b0412b2838b07c 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep26k12t2m0 : edgeCase26 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep26k12t3m0 : edgeCase26 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases26 : ∀ t ∈ smallT, MaskRun ea26 edgeQ26 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x1044f5229024125a1e310a92a3a902cb10115f0442840092414b81, 0), (0x2989085c668300a1418864210c52bc202ce8a0820d3ad445860402, 0), (0x63202810958ed04a046914c50044114c3060079b0412b2838b07c, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact budgetRep26k12t1m0
    · exact budgetRep26k12t1m1
    · exact budgetRep26k12t1m2
    · exact budgetRep26k12t1m3
  · exact one budgetRep26k12t2m0
  · exact one budgetRep26k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data26 : CaseData ea26 := prepSound ea26 q1_26 q2_26 extra_26 edgePrep26 budgetCases26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m0 : edgeCase27 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m1 : edgeCase27 1 0x1000000000000000000440800000014000005016400a100000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m2 : edgeCase27 1 0x8801002060001000001040100004010000010000000020002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m3 : edgeCase27 1 0xd480000000000480040000120000800000000000000040410001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m4 : edgeCase27 1 0x20000004000000200001000000000000042000000000004000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m5 : edgeCase27 1 0x40000000040000000080000000000000000000000200000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m6 : edgeCase27 1 0x1000000000000000000000000000000000000011000040000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m7 : edgeCase27 1 0x40410006000880000000100018000c200004000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m8 : edgeCase27 1 0x2019000000200082000002400000800081000208000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m9 : edgeCase27 1 0x40000000000000000001000080001020000000000100040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m10 : edgeCase27 1 0x100000000000000000 0 = false := by decide +kernel
def budgetRep27k12t1m11Batch0 : List BState := [storedState 1 11 1 0x139dad4a5ad4a5294a5294a5694ada94a5ab4a56b295ad494a54a4e5295274 [0,8,92,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m11Batch0OK : budgetRep27k12t1m11Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m11Batch1 : List BState := [storedState 1 11 1 0x1295ad39dad494e739ce739d673ada939dab39d6b18dad294634a4e518d274 [0,8,1,2,92,4,5,6],
  storedState 1 11 1 0x129dad3a5ad49ce739d294a5674ada93a5ab3a56b195ad394654a4e5195274 [0,8,1,92,4,5,6],
  storedState 1 11 1 0x1395ad49dad49d294a4e739d693ada949dab49d6b28dad394a34a4e528d274 [0,8,2,92,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m11Batch1OK : budgetRep27k12t1m11Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m11Cache : List BState := budgetRep27k12t1m11Batch0 ++ (budgetRep27k12t1m11Batch1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m11Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 budgetRep27k12t1m11Cache) [ea27] edgeQ27 0 12 (remT (unaryE ea27) 1) 0x8000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m11 : edgeCase27 1 0x8000000000000000000000000000000000000000 0 = false := by
  apply budgetMemo_join [ea27] edgeQ27 0 12 (remT (unaryE ea27) 1) 0x8000000000000000000000000000000000000000 0 budgetRep27k12t1m11Cache _ budgetRep27k12t1m11Lookup
  intro c hc
  simp only [budgetRep27k12t1m11Cache, List.mem_append] at hc
  rcases hc with hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m11Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m11Batch1OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m12 : edgeCase27 1 0x2000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m13 : edgeCase27 1 0x400000000004000000000000000800000000080000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m14 : edgeCase27 1 0x10000000002110000100e00800002420000000000000002800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m15 : edgeCase27 1 0x4008000a11000002000004080220200080000000000000400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m16 : edgeCase27 1 0x800000000000000000040000000000000200000000000000000 0 = false := by decide +kernel
def budgetRep27k12t1m17Batch0 : List BState := [storedState 1 11 1 0x14a56d4a52d2a56759d6759d273a5294a52939ce929529494e73a4a5294a72 [0,1,2,92,4,5,6,18]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m17Batch0OK : budgetRep27k12t1m17Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m17Batch1 : List BState := [storedState 1 11 1 0x14a52d4a56d3a5695a5695a4e529d294a567294e72956b494e72a465294e73 [0,1,2,92,19,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m17Batch1OK : budgetRep27k12t1m17Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m17Cache : List BState := budgetRep27k12t1m17Batch0 ++ (budgetRep27k12t1m17Batch1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m17Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 budgetRep27k12t1m17Cache) [ea27] edgeQ27 0 12 (remT (unaryE ea27) 1) 0x100000000000000000000000000000000004000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m17 : edgeCase27 1 0x100000000000000000000000000000000004000000000000000000 0 = false := by
  apply budgetMemo_join [ea27] edgeQ27 0 12 (remT (unaryE ea27) 1) 0x100000000000000000000000000000000004000000000000000000 0 budgetRep27k12t1m17Cache _ budgetRep27k12t1m17Lookup
  intro c hc
  simp only [budgetRep27k12t1m17Cache, List.mem_append] at hc
  rcases hc with hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m17Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m17Batch1OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m18 : edgeCase27 1 0x80000000000000000000000000000008000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m19 : edgeCase27 1 0x40000000000000010000002000009000400000400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m20 : edgeCase27 1 0x202020100020004000100004000400010000000002800800200000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m21 : edgeCase27 1 0x801000a0800000008400010000040000008000c00000000001004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m22 : edgeCase27 1 0x200200100400002820000008000000000003000000091000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m23 : edgeCase27 1 0x200080800000020000220000000000000060002808308 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m24 : edgeCase27 1 0x10000000000000200090000000000000000000020084000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m25 : edgeCase27 1 0x4000000000000000400000010 0 = false := by decide +kernel
def budgetRep27k12t1m26Batch0 : List BState := [storedState 1 11 1 0x14a5a94a5ab49d6b4ad6b4ad694a5a539d2b4a569295ad494e7494e5295254 [0,1,93,2,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m26Batch0OK : budgetRep27k12t1m26Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m26Batch1 : List BState := [storedState 1 11 1 0x14a5a939dab4956b4ad6b4ad673a5a52952b39d6918dad394e7494e518d254 [0,1,93,2,92,4,5,6],
  storedState 1 11 1 0x14a5ab39da94a56b3ad6b3ad6739da739d6b39d6718dad394e749ce518d234 [0,1,2,4,5,6,94]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m26Batch1OK : budgetRep27k12t1m26Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m26Batch2 : List BState := [storedState 1 11 1 0x129529295292a52b5a52b5a5294ad674a5a7294e718d69484e74a463295273 [39,0,1,2,92,4,5,6],
  storedState 1 11 1 0x14a5ab295a949d6b3ad6b3ad6529da72956b29567085ad294e749ce5085234 [0,1,2,92,4,5,6,94],
  storedState 1 11 1 0x139d6b39d6b2a4eb59ceb59ce94ad254a5a739d290852948ce74a4a1295272 [0,1,2,92,4,5,6,30]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m26Batch2OK : budgetRep27k12t1m26Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t1m26Cache : List BState := budgetRep27k12t1m26Batch0 ++ (budgetRep27k12t1m26Batch1 ++ (budgetRep27k12t1m26Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m26Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 budgetRep27k12t1m26Cache) [ea27] edgeQ27 0 12 (remT (unaryE ea27) 1) 0x18000000000000100000000080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t1m26 : edgeCase27 1 0x18000000000000100000000080 0 = false := by
  apply budgetMemo_join [ea27] edgeQ27 0 12 (remT (unaryE ea27) 1) 0x18000000000000100000000080 0 budgetRep27k12t1m26Cache _ budgetRep27k12t1m26Lookup
  intro c hc
  simp only [budgetRep27k12t1m26Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m26Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m26Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t1m26Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m0 : edgeCase27 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m1 : edgeCase27 2 0x1ca1024204050058c009000a19098070c42300200011680080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m2 : edgeCase27 2 0x32e22200a400905234000910c0240044090008840012010c001442 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m3 : edgeCase27 2 0x500000c00216308890202e01f1164023400030044000000902118 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m4 : edgeCase27 2 0x94010508c0000020504020000029040031058ba4da260044205 0 = false := by decide +kernel
def budgetRep27k12t2m5Batch0 : List BState := [storedState 1 11 2 0x139dad4a5ad4a5294a5294a5694ada94a5ab4a56b295ad494a54a4e5295274 [0,8,92,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m5Batch0OK : budgetRep27k12t2m5Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t2m5Batch1 : List BState := [storedState 1 11 2 0x14a56d4a52d2a56759d6759d273a5294a52939ce929529494e73a4a5294a72 [0,1,2,92,4,5,6,18],
  storedState 1 11 2 0x14a5ad4a5ad39d6b5a56b5a5694ad694a5a739ce7295ab494e74a465295273 [0,1,95,2,4,5,6],
  storedState 1 11 2 0x14a52d4a56d3a5695a5695a4e529d294a567294e72956b494e72a465294e73 [0,1,2,92,19,4,5,6],
  storedState 1 11 2 0x129dad3a5ad49ce739d294a5674ada93a5ab3a56b195ad394654a4e5195274 [0,8,1,92,4,5,6],
  storedState 1 11 2 0x1395ad49dad49d294a4e739d693ada949dab49d6b28dad394a34a4e528d274 [0,8,2,92,4,5,6],
  storedState 1 11 2 0x14a5ad39dad2a56b59d6b59d673ad2939da939d2918da9394e74a4a518d272 [0,1,2,4,5,6,96],
  storedState 1 11 2 0x129529295292a52b4ad2b4ad294a5a5295294a56918d6b484e7494e3295254 [46,0,1,2,92,4,5,6],
  storedState 1 11 2 0x14a5ad39dad3956b5a56b5a5673ad6939da7294e718dab394e74a46518d273 [0,1,95,2,92,4,5,6],
  storedState 1 11 2 0x1295ad39dad494e739ce739d673ada939dab39d6b18dad294634a4e518d274 [0,8,1,2,92,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m5Batch1OK : budgetRep27k12t2m5Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t2m5Batch2 : List BState := [storedState 1 11 2 0x14a5ad295ad29d6b59d6b59d652ad29295a929529085a9294e74a4a5085272 [0,1,2,92,4,5,6,96],
  storedState 1 11 2 0x139d6939d693a4eb3aceb3ace949da539d674a5670852948ce749ce1295234 [0,1,2,92,4,5,97,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m5Batch2OK : budgetRep27k12t2m5Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep27k12t2m5Cache : List BState := budgetRep27k12t2m5Batch0 ++ (budgetRep27k12t2m5Batch1 ++ (budgetRep27k12t2m5Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m5Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ27.map fun _ => 16)) 12 budgetRep27k12t2m5Cache) [ea27] edgeQ27 0 12 (remT (unaryE ea27) 2) 0x108042091008a00020300000408000000c000000000c00010020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m5 : edgeCase27 2 0x108042091008a00020300000408000000c000000000c00010020 0 = false := by
  apply budgetMemo_join [ea27] edgeQ27 0 12 (remT (unaryE ea27) 2) 0x108042091008a00020300000408000000c000000000c00010020 0 budgetRep27k12t2m5Cache _ budgetRep27k12t2m5Lookup
  intro c hc
  simp only [budgetRep27k12t2m5Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t2m5Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t2m5Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep27k12t2m5Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t2m6 : edgeCase27 2 0x80401000000000040800004208000200280200001805082028800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep27k12t3m0 : edgeCase27 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases27 : ∀ t ∈ smallT, MaskRun ea27 edgeQ27 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x1000000000000000000440800000014000005016400a100000000, 0), (0x8801002060001000001040100004010000010000000020002, 0), (0xd480000000000480040000120000800000000000000040410001, 0), (0x20000004000000200001000000000000042000000000004000000, 0), (0x40000000040000000080000000000000000000000200000000000, 0), (0x1000000000000000000000000000000000000011000040000, 0), (0x40410006000880000000100018000c200004000000000, 0), (0x2019000000200082000002400000800081000208000000, 0), (0x40000000000000000001000080001020000000000100040, 0), (0x100000000000000000, 0), (0x8000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000000, 0), (0x400000000004000000000000000800000000080000000000, 0), (0x10000000002110000100e00800002420000000000000002800, 0), (0x4008000a11000002000004080220200080000000000000400, 0), (0x800000000000000000040000000000000200000000000000000, 0), (0x100000000000000000000000000000000004000000000000000000, 0), (0x80000000000000000000000000000008000000000000, 0), (0x40000000000000010000002000009000400000400000000000, 0), (0x202020100020004000100004000400010000000002800800200000, 0), (0x801000a0800000008400010000040000008000c00000000001004, 0), (0x200200100400002820000008000000000003000000091000020, 0), (0x200080800000020000220000000000000060002808308, 0), (0x10000000000000200090000000000000000000020084000, 0), (0x4000000000000000400000010, 0), (0x18000000000000100000000080, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep27k12t1m0
    · exact budgetRep27k12t1m1
    · exact budgetRep27k12t1m2
    · exact budgetRep27k12t1m3
    · exact budgetRep27k12t1m4
    · exact budgetRep27k12t1m5
    · exact budgetRep27k12t1m6
    · exact budgetRep27k12t1m7
    · exact budgetRep27k12t1m8
    · exact budgetRep27k12t1m9
    · exact budgetRep27k12t1m10
    · exact budgetRep27k12t1m11
    · exact budgetRep27k12t1m12
    · exact budgetRep27k12t1m13
    · exact budgetRep27k12t1m14
    · exact budgetRep27k12t1m15
    · exact budgetRep27k12t1m16
    · exact budgetRep27k12t1m17
    · exact budgetRep27k12t1m18
    · exact budgetRep27k12t1m19
    · exact budgetRep27k12t1m20
    · exact budgetRep27k12t1m21
    · exact budgetRep27k12t1m22
    · exact budgetRep27k12t1m23
    · exact budgetRep27k12t1m24
    · exact budgetRep27k12t1m25
    · exact budgetRep27k12t1m26
  · refine ⟨[(0, 1), (0x1ca1024204050058c009000a19098070c42300200011680080, 0), (0x32e22200a400905234000910c0240044090008840012010c001442, 0), (0x500000c00216308890202e01f1164023400030044000000902118, 0), (0x94010508c0000020504020000029040031058ba4da260044205, 0), (0x108042091008a00020300000408000000c000000000c00010020, 0), (0x80401000000000040800004208000200280200001805082028800, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep27k12t2m0
    · exact budgetRep27k12t2m1
    · exact budgetRep27k12t2m2
    · exact budgetRep27k12t2m3
    · exact budgetRep27k12t2m4
    · exact budgetRep27k12t2m5
    · exact budgetRep27k12t2m6
  · exact one budgetRep27k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data27 : CaseData ea27 := prepSound ea27 q1_27 q2_27 extra_27 edgePrep27 budgetCases27
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t1m0 : edgeCase30 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t1m1 : edgeCase30 1 0x32c42f000c060024006040182b21040020050a0012c20100060002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t1m2 : edgeCase30 1 0x18002aa180c041840004800440004a4022609b480000e1280105 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t1m3 : edgeCase30 1 0x800804100000e8021988a02101443319d88004021110400401880 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t1m4 : edgeCase30 1 0x5225000004831180000312440829080021081040420f214004618 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t1m5 : edgeCase30 1 0x10094523100025a0700418008280400401420800c080a91a060 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m0 : edgeCase30 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m1 : edgeCase30 2 0x31400000080a680018000880012040081100600021201104001201 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m2 : edgeCase30 2 0x80a000300102400860601204100020014104014000620260100 0 = false := by decide +kernel
def budgetRep30k12t2m3Batch0 : List BState := [storedState 1 11 1 0x12a5674ad6939ce73956b4a56959d2539ce93a4e529d694946738c6329ce32 [0,35,1,98,2,4,5,6],
  storedState 1 11 1 0x1494eb5a52b49d695ace739ce7394e95a52b5a4e93952b494e319ca3394a53 [0,1,98,41,2,4,5],
  storedState 1 11 1 0x14956b5a56b29d6b59ce739d6b4a4e95a56949ce739567494e339c63394e51 [0,1,70,2,4,5,6],
  storedState 1 11 1 0x12a5674ad6949ce739d6b4ad6959d6539ceb4ad2729d6b4946738ca329ce33 [0,35,1,98,2,4,5],
  storedState 1 11 1 0x1494eb5a52b39d695a4e7394e7394a95a52949ca739529494e319c63394a52 [0,1,98,41,2,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m3Batch0OK : budgetRep30k12t2m3Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ30.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep30k12t2m3Batch1 : List BState := [storedState 1 11 1 0x149d2b59ceb3a5675a52749d2939ce959ce94946738ce9394e529c6338c652 [0,1,98,2,4,5,6,32],
  storedState 1 11 1 0x149d2b59ceb4a5675ad274a52939d2959ceb59ca938ceb394e529ca338c653 [0,1,98,2,4,5,32],
  storedState 1 11 1 0x13a56b3ad6b2a52949d6b59d675a4e93ad693a4e719d67394a739c6319ce51 [0,1,98,2,4,5,28],
  storedState 1 11 1 0x14956b5a56b29d6b59ce739d6b4a4e95a56949ce739567494e339c63394e51 [0,1,70,98,2,4,5],
  storedState 1 11 1 0x13a5693ad673a52939d6b3a567595273a5292a4e319d69394a73946319ce12 [0,1,98,2,4,5,99,6],
  storedState 1 11 1 0x13a5693ad674a5293a56b3ad67595673a52b3ad2519d6b394a7394a319ce13 [0,1,98,2,4,5,99],
  storedState 1 11 1 0x149d6b59d6b3a56b5a52949d6b3a52959d6739ca538d69394e539c2338ce52 [0,1,98,2,71,4,5],
  storedState 1 11 1 0x1294e739ce72ad295ad295ace7394e75ad295ace9294e9584e719ca139ca53 [76,0,1,98,2,4,5]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m3Batch1OK : budgetRep30k12t2m3Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ30.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep30k12t2m3Batch2 : List BState := [storedState 1 11 1 0x12a56b4ad6b39ce739d6b5a5695a5294ad6739ca529d694946739c2329ce52 [0,15,1,98,2,4,5],
  storedState 1 11 1 0x149d6b59d6b3a56b5a52949d6b3a52959d6739ca538d69394e539c2338ce52 [0,1,2,71,4,5,6],
  storedState 1 11 1 0x1294e739ce71ad295a5295a4e7394a75ad274a4a7294e7584e719c6139ca52 [76,0,1,98,2,4,5,6],
  storedState 1 11 1 0x13a56b3ad6b1a5294956b595675a4a93ad6729ca519d65394a739c2319ce50 [0,1,98,2,4,5,6,28],
  storedState 1 11 1 0x14956b5a56b19d6b594e73956b4a4a95a567394a539565494e339c23394e50 [0,1,70,98,2,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m3Batch2OK : budgetRep30k12t2m3Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ30.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep30k12t2m3Cache : List BState := budgetRep30k12t2m3Batch0 ++ (budgetRep30k12t2m3Batch1 ++ (budgetRep30k12t2m3Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m3Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ30.map fun _ => 16)) 12 budgetRep30k12t2m3Cache) [ea30] edgeQ30 0 12 (remT (unaryE ea30) 2) 0x2118000c0804022209114008014100640008040400050080028 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m3 : edgeCase30 2 0x2118000c0804022209114008014100640008040400050080028 0 = false := by
  apply budgetMemo_join [ea30] edgeQ30 0 12 (remT (unaryE ea30) 2) 0x2118000c0804022209114008014100640008040400050080028 0 budgetRep30k12t2m3Cache _ budgetRep30k12t2m3Lookup
  intro c hc
  simp only [budgetRep30k12t2m3Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep30k12t2m3Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep30k12t2m3Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep30k12t2m3Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m4 : edgeCase30 2 0x20084508010040140180008c808a00008010a1202100001012004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m5 : edgeCase30 2 0x40100005400001a85000042100600804028842080000080904012 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m6 : edgeCase30 2 0x8240022000501800040002002100b2100820004000be800000840 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t2m7 : edgeCase30 2 0x90600d202002000001600004000044a00001090884000a408480 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t3m0 : edgeCase30 3 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t3m1 : edgeCase30 3 0x1004018800035181c01c2106410511c201332120485844903142a0 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t3m2 : edgeCase30 3 0x719004122640c023700c42006186a08c040020230a2312c082108 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t3m3 : edgeCase30 3 0x20826026c598006008600ad898a284153a08841100040002021045 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep30k12t3m4 : edgeCase30 3 0x8609e101800a21c0083100120400020048458cc87018a41c48c12 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases30 : ∀ t ∈ smallT, MaskRun ea30 edgeQ30 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x32c42f000c060024006040182b21040020050a0012c20100060002, 0), (0x18002aa180c041840004800440004a4022609b480000e1280105, 0), (0x800804100000e8021988a02101443319d88004021110400401880, 0), (0x5225000004831180000312440829080021081040420f214004618, 0), (0x10094523100025a0700418008280400401420800c080a91a060, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep30k12t1m0
    · exact budgetRep30k12t1m1
    · exact budgetRep30k12t1m2
    · exact budgetRep30k12t1m3
    · exact budgetRep30k12t1m4
    · exact budgetRep30k12t1m5
  · refine ⟨[(0, 1), (0x31400000080a680018000880012040081100600021201104001201, 0), (0x80a000300102400860601204100020014104014000620260100, 0), (0x2118000c0804022209114008014100640008040400050080028, 0), (0x20084508010040140180008c808a00008010a1202100001012004, 0), (0x40100005400001a85000042100600804028842080000080904012, 0), (0x8240022000501800040002002100b2100820004000be800000840, 0), (0x90600d202002000001600004000044a00001090884000a408480, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep30k12t2m0
    · exact budgetRep30k12t2m1
    · exact budgetRep30k12t2m2
    · exact budgetRep30k12t2m3
    · exact budgetRep30k12t2m4
    · exact budgetRep30k12t2m5
    · exact budgetRep30k12t2m6
    · exact budgetRep30k12t2m7
  · refine ⟨[(0, 1), (0x1004018800035181c01c2106410511c201332120485844903142a0, 0), (0x719004122640c023700c42006186a08c040020230a2312c082108, 0), (0x20826026c598006008600ad898a284153a08841100040002021045, 0), (0x8609e101800a21c0083100120400020048458cc87018a41c48c12, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep30k12t3m0
    · exact budgetRep30k12t3m1
    · exact budgetRep30k12t3m2
    · exact budgetRep30k12t3m3
    · exact budgetRep30k12t3m4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data30 : CaseData ea30 := prepSound ea30 q1_30 q2_30 extra_30 edgePrep30 budgetCases30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m0 : edgeCase32 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m1 : edgeCase32 1 0x2e00026010010048804aa04006000c00800980004000000c408000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m2 : edgeCase32 1 0x1900000c00002004800001a004440040002290484340020040292 0 = false := by decide +kernel
def budgetRep32k12t1m3Batch0 : List BState := [storedState 1 11 0 0x12952b4a52b49ce539ce539d2739d294a52b4a4e92952b3946329ca3294a53 [0,8,1,100,2,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m3Batch0OK : budgetRep32k12t1m3Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep32k12t1m3Batch1 : List BState := [storedState 1 11 0 0x139d2b39d2b49d274a5274a52529d2939d2b39ce918d2b394a529ca318ca53 [0,1,100,2,3,4,5,6],
  storedState 1 11 0 0x12a5274ad2949ce539d694ad274952539cab4ace729d2b4946728ca329ca33 [0,35,1,100,2,4,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m3Batch1OK : budgetRep32k12t1m3Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep32k12t1m3Batch2 : List BState := [storedState 1 11 0 0x14a4eb5acab2ad6559d6559ce7394a95aca94a46739ca7594e719c6339c251 [0,1,100,2,4,5,6,18],
  storedState 1 11 0 0x14a5295ad272ad6939d6939d2948ca74a4e94a4a539d27594e72946339ca11 [0,1,100,2,4,5,6,101],
  storedState 1 11 0 0x13a5293ad274a5273a5693ad2548d273a4eb3ace519d2b394a7294a319ca13 [0,1,100,2,4,5,99,6],
  storedState 1 11 0 0x14a4ab5aceb3ad675a5675a4a528ca95ace739c6539ce9594e709c2339c652 [0,1,100,2,19,4,5,6],
  storedState 1 11 0 0x14a5275ad293ad694a5694a529494e539ca739c6539d29594e728c2339ca32 [0,1,100,2,4,42,5,6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m3Batch2OK : budgetRep32k12t1m3Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep32k12t1m3Cache : List BState := budgetRep32k12t1m3Batch0 ++ (budgetRep32k12t1m3Batch1 ++ (budgetRep32k12t1m3Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m3Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 budgetRep32k12t1m3Cache) [ea32] edgeQ32 0 12 (remT (unaryE ea32) 1) 0x800000182509100100000000000824404422002039502a10108 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m3 : edgeCase32 1 0x800000182509100100000000000824404422002039502a10108 0 = false := by
  apply budgetMemo_join [ea32] edgeQ32 0 12 (remT (unaryE ea32) 1) 0x800000182509100100000000000824404422002039502a10108 0 budgetRep32k12t1m3Cache _ budgetRep32k12t1m3Lookup
  intro c hc
  simp only [budgetRep32k12t1m3Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep32k12t1m3Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep32k12t1m3Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep32k12t1m3Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m4 : edgeCase32 1 0x42b0020030000002004080800210180b40100b30882000001004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m5 : edgeCase32 1 0x100008992400202401040200480083202090041000000801100021 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m6 : edgeCase32 1 0x21050400040c002021010100a1200110200080000002d0086840 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t1m7 : edgeCase32 1 0x440000a48810214801c24311800400000004009404000020400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m0 : edgeCase32 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m1 : edgeCase32 2 0x10000000004000000040040200000000000008000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m2 : edgeCase32 2 0x10020108000000008000002000000000000000002000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m3 : edgeCase32 2 0x1604800000802010000001000040100000200400000200000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m4 : edgeCase32 2 0x240000081000080000011628120200000442100000139020000881 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m5 : edgeCase32 2 0x800000224086000200040200005102002028d804000290050 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m6 : edgeCase32 2 0xa02040804101428020800000002002400908014020004440c000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m7 : edgeCase32 2 0x1208002200200010008a49100048090000800100000c0001120300 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m8 : edgeCase32 2 0x40c0142000000003500080000090a08304404000000910801008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m9 : edgeCase32 2 0x100014a08408004000006080004000010802832400402040420 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t2m10 : edgeCase32 2 0x80013000580100400000000851502480800041000002088000006 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t3m0 : edgeCase32 3 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t3m1 : edgeCase32 3 0x11340a0a2a10304012a250091806841109800711281402326049 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t3m2 : edgeCase32 3 0x2080c30481004c052c8c00867246815080041908881160204c0132 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t3m3 : edgeCase32 3 0x120608e15090a0000321182104a02821488240a042468a50811a04 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep32k12t3m4 : edgeCase32 3 0xd680010244503ca904045088001500a267026502480018d008480 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases32 : ∀ t ∈ smallT, MaskRun ea32 edgeQ32 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x2e00026010010048804aa04006000c00800980004000000c408000, 0), (0x1900000c00002004800001a004440040002290484340020040292, 0), (0x800000182509100100000000000824404422002039502a10108, 0), (0x42b0020030000002004080800210180b40100b30882000001004, 0), (0x100008992400202401040200480083202090041000000801100021, 0), (0x21050400040c002021010100a1200110200080000002d0086840, 0), (0x440000a48810214801c24311800400000004009404000020400, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep32k12t1m0
    · exact budgetRep32k12t1m1
    · exact budgetRep32k12t1m2
    · exact budgetRep32k12t1m3
    · exact budgetRep32k12t1m4
    · exact budgetRep32k12t1m5
    · exact budgetRep32k12t1m6
    · exact budgetRep32k12t1m7
  · refine ⟨[(0, 1), (0x10000000004000000040040200000000000008000000000000000, 0), (0x10020108000000008000002000000000000000002000, 0), (0x1604800000802010000001000040100000200400000200000000, 0), (0x240000081000080000011628120200000442100000139020000881, 0), (0x800000224086000200040200005102002028d804000290050, 0), (0xa02040804101428020800000002002400908014020004440c000, 0), (0x1208002200200010008a49100048090000800100000c0001120300, 0), (0x40c0142000000003500080000090a08304404000000910801008, 0), (0x100014a08408004000006080004000010802832400402040420, 0), (0x80013000580100400000000851502480800041000002088000006, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep32k12t2m0
    · exact budgetRep32k12t2m1
    · exact budgetRep32k12t2m2
    · exact budgetRep32k12t2m3
    · exact budgetRep32k12t2m4
    · exact budgetRep32k12t2m5
    · exact budgetRep32k12t2m6
    · exact budgetRep32k12t2m7
    · exact budgetRep32k12t2m8
    · exact budgetRep32k12t2m9
    · exact budgetRep32k12t2m10
  · refine ⟨[(0, 1), (0x11340a0a2a10304012a250091806841109800711281402326049, 0), (0x2080c30481004c052c8c00867246815080041908881160204c0132, 0), (0x120608e15090a0000321182104a02821488240a042468a50811a04, 0), (0xd680010244503ca904045088001500a267026502480018d008480, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep32k12t3m0
    · exact budgetRep32k12t3m1
    · exact budgetRep32k12t3m2
    · exact budgetRep32k12t3m3
    · exact budgetRep32k12t3m4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data32 : CaseData ea32 := prepSound ea32 q1_32 q2_32 extra_32 edgePrep32 budgetCases32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m0 : edgeCase34 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m1 : edgeCase34 1 0x24004000401802209440220000488080005021840000020080002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m2 : edgeCase34 1 0x1098f0200000284000100000430000080289880380000200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m3 : edgeCase34 1 0x10280ac30002048800028110012000901000000004000000000059 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m4 : edgeCase34 1 0x24002000030048004000040804010000001080001200e013406084 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m5 : edgeCase34 1 0x80d008400010018410008000080000a602342000040800048400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m6 : edgeCase34 1 0x1700200008000422002002028204204800000000201400910920 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m7 : edgeCase34 1 0x80001000004015010001041084061040028010500420048001000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t1m8 : edgeCase34 1 0x10000042000020000810804e010120001c040c020110004220000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m0 : edgeCase34 2 0 1 = false := by decide +kernel
def budgetRep34k12t2m1Batch0 : List BState := [storedState 1 11 1 0x13a4e74ad294a5273a5694ace5394e529ceb4ace729d2b494a718ca329ca33 [0,1,2,14,4,5,6,102],
  storedState 1 11 1 0x14a4e75ad294ad694ad694ace7394e539ceb5ace739d2b594e718ca339ca33 [0,2,14,4,5,6,102],
  storedState 1 11 1 0x12a56b4ad6b29ce739d6b59d695a4e94ad693a4e729d674946739c6329ce51 [0,1,2,4,5,6,52],
  storedState 1 11 1 0x14a5295ace74ad673ad673ad29495274a4eb5aca539ceb594e7294a339c613 [0,2,4,5,6,102,13]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m1Batch0OK : budgetRep34k12t2m1Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep34k12t2m1Batch1 : List BState := [storedState 1 11 1 0x12a52b4aceb49ce739d675ad2749d294aceb4aca929ceb4946729ca329c653 [0,1,2,4,5,6,83],
  storedState 1 11 1 0x13a5294ace74a5252a5673ad27495273a4eb4aca529ceb494a7294a329c613 [0,1,2,4,5,6,102,13],
  storedState 1 11 1 0x12a52b4aceb49ce739d675ad2749d294aceb4aca929ceb4946729ca329c653 [0,2,4,5,6,102,83],
  storedState 1 11 1 0x13a4eb3ad2b4a5274a5695ace7394e93ad2b3ace919d2b394a719ca319ca53 [0,1,2,56,4,5,6],
  storedState 1 11 1 0x12a56b4ad6b29ce739d6b59d695a4e94ad693a4e729d674946739c6329ce51 [0,2,4,5,6,102,52],
  storedState 1 11 1 0x13a4eb3ad2b4a5274a5695ace7394e93ad2b3ace919d2b394a719ca319ca53 [0,2,56,4,5,6,102]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m1Batch1OK : budgetRep34k12t2m1Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep34k12t2m1Batch2 : List BState := [storedState 1 11 1 0x13a56b3ad6b3a52949d6b5a5675a5293ad6739ca519d69394a739c2319ce52 [0,2,4,5,58,6,102],
  storedState 1 11 1 0x13a56b3ad6b3a52949d6b5a5675a5293ad6739ca519d69394a739c2319ce52 [0,1,2,4,5,58,6],
  storedState 1 11 1 0x11a52b3aceb494a5295675ad2549d293aceb3aca919ceb3942729ca319c653 [0,1,2,4,5,6,102,83],
  storedState 1 11 1 0x11a56b3ad6b294a52956b59d675a4e93ad692a4e719d673942739c6319ce51 [0,1,2,4,5,6,102,52],
  storedState 1 11 1 0x12a4eb2ad2b49ce539d695ace5394e92ad2b2ace909d2b2946719ca309ca53 [0,1,2,56,4,5,6,102],
  storedState 1 11 1 0x12a56b2ad6b39ce73956b5a5655a5292ad6729ca509d692946739c2309ce52 [0,1,2,4,5,58,6,102]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m1Batch2OK : budgetRep34k12t2m1Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRep34k12t2m1Cache : List BState := budgetRep34k12t2m1Batch0 ++ (budgetRep34k12t2m1Batch1 ++ (budgetRep34k12t2m1Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m1Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 budgetRep34k12t2m1Cache) [ea34] edgeQ34 0 12 (remT (unaryE ea34) 2) 0x10c0000100011000020640004000000000a8020018800520440d40 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m1 : edgeCase34 2 0x10c0000100011000020640004000000000a8020018800520440d40 0 = false := by
  apply budgetMemo_join [ea34] edgeQ34 0 12 (remT (unaryE ea34) 2) 0x10c0000100011000020640004000000000a8020018800520440d40 0 budgetRep34k12t2m1Cache _ budgetRep34k12t2m1Lookup
  intro c hc
  simp only [budgetRep34k12t2m1Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep34k12t2m1Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep34k12t2m1Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRep34k12t2m1Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m2 : edgeCase34 2 0x30060188360000000800004040024202002150024000000182000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m3 : edgeCase34 2 0x9108000008a20084002a9200210024000204041008080008000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m4 : edgeCase34 2 0x6600802008000010c400120000400040011000400470042a2 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m5 : edgeCase34 2 0x601022480001800001110800441008001408080320810200000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m6 : edgeCase34 2 0x80080004004004080082000024082811c40880400413000030000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m7 : edgeCase34 2 0x40008041010600324208002009808100010002000000200800015 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t2m8 : edgeCase34 2 0x203000000008050451100000180100480300000a02084008001008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t3m0 : edgeCase34 3 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t3m1 : edgeCase34 3 0x8c950404121007b6000090a21020872068768043aa1a008008080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t3m2 : edgeCase34 3 0x122200198c405084802c26a0c645050001480320041044c02c6512 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t3m3 : edgeCase34 3 0x251423a010122b000c03d05008082001a820145a004e0012511244 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep34k12t3m4 : edgeCase34 3 0x8c06228c840013d0000510b0d28c50108081c1001b25820829 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases34 : ∀ t ∈ smallT, MaskRun ea34 edgeQ34 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x24004000401802209440220000488080005021840000020080002, 0), (0x1098f0200000284000100000430000080289880380000200, 0), (0x10280ac30002048800028110012000901000000004000000000059, 0), (0x24002000030048004000040804010000001080001200e013406084, 0), (0x80d008400010018410008000080000a602342000040800048400, 0), (0x1700200008000422002002028204204800000000201400910920, 0), (0x80001000004015010001041084061040028010500420048001000, 0), (0x10000042000020000810804e010120001c040c020110004220000, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep34k12t1m0
    · exact budgetRep34k12t1m1
    · exact budgetRep34k12t1m2
    · exact budgetRep34k12t1m3
    · exact budgetRep34k12t1m4
    · exact budgetRep34k12t1m5
    · exact budgetRep34k12t1m6
    · exact budgetRep34k12t1m7
    · exact budgetRep34k12t1m8
  · refine ⟨[(0, 1), (0x10c0000100011000020640004000000000a8020018800520440d40, 0), (0x30060188360000000800004040024202002150024000000182000, 0), (0x9108000008a20084002a9200210024000204041008080008000, 0), (0x6600802008000010c400120000400040011000400470042a2, 0), (0x601022480001800001110800441008001408080320810200000, 0), (0x80080004004004080082000024082811c40880400413000030000, 0), (0x40008041010600324208002009808100010002000000200800015, 0), (0x203000000008050451100000180100480300000a02084008001008, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep34k12t2m0
    · exact budgetRep34k12t2m1
    · exact budgetRep34k12t2m2
    · exact budgetRep34k12t2m3
    · exact budgetRep34k12t2m4
    · exact budgetRep34k12t2m5
    · exact budgetRep34k12t2m6
    · exact budgetRep34k12t2m7
    · exact budgetRep34k12t2m8
  · refine ⟨[(0, 1), (0x8c950404121007b6000090a21020872068768043aa1a008008080, 0), (0x122200198c405084802c26a0c645050001480320041044c02c6512, 0), (0x251423a010122b000c03d05008082001a820145a004e0012511244, 0), (0x8c06228c840013d0000510b0d28c50108081c1001b25820829, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact budgetRep34k12t3m0
    · exact budgetRep34k12t3m1
    · exact budgetRep34k12t3m2
    · exact budgetRep34k12t3m3
    · exact budgetRep34k12t3m4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data34 : CaseData ea34 := prepSound ea34 q1_34 q2_34 extra_34 edgePrep34 budgetCases34
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t1m0 : edgeCase35 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t1m1 : edgeCase35 1 0x5c41023144c190746220481a48cd00282a521320cd21c25e84768 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t1m2 : edgeCase35 1 0x818ac04e283c49880ddea1a40202e38544816c18224225a058802 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t1m3 : edgeCase35 1 0x322343d809302260390011641b5301c52912c80c7109c180123095 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t2m0 : edgeCase35 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t2m1 : edgeCase35 2 0x8100800002a18ae0248592900c0000020c5481488200001862400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t2m2 : edgeCase35 2 0x20011032600020001022082a011cd084002054a43c028a2080800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t2m3 : edgeCase35 2 0x20c5c45009402510000080400c280001013820002002d040114159 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t2m4 : edgeCase35 2 0x102208c0085400118210614420230708a0080000401070c201282 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t2m5 : edgeCase35 2 0x14280220d0108040e494000011040286140012a1101c0010408024 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t3m0 : edgeCase35 3 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t3m1 : edgeCase35 3 0x8c2a04d06ca40208a558050440712f5c2034e6451438082d31845 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t3m2 : edgeCase35 3 0x213504101910950575020cad9900890a016c909106bc7c69282102 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRep35k12t3m3 : edgeCase35 3 0x16085ba2e0252ada00a8730222f864003c90210aa800031404c6b8 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetCases35 : ∀ t ∈ smallT, MaskRun ea35 edgeQ35 t := by
  intro t ht
  simp only [smallT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨[(0, 1), (0x5c41023144c190746220481a48cd00282a521320cd21c25e84768, 0), (0x818ac04e283c49880ddea1a40202e38544816c18224225a058802, 0), (0x322343d809302260390011641b5301c52912c80c7109c180123095, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact budgetRep35k12t1m0
    · exact budgetRep35k12t1m1
    · exact budgetRep35k12t1m2
    · exact budgetRep35k12t1m3
  · refine ⟨[(0, 1), (0x8100800002a18ae0248592900c0000020c5481488200001862400, 0), (0x20011032600020001022082a011cd084002054a43c028a2080800, 0), (0x20c5c45009402510000080400c280001013820002002d040114159, 0), (0x102208c0085400118210614420230708a0080000401070c201282, 0), (0x14280220d0108040e494000011040286140012a1101c0010408024, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact budgetRep35k12t2m0
    · exact budgetRep35k12t2m1
    · exact budgetRep35k12t2m2
    · exact budgetRep35k12t2m3
    · exact budgetRep35k12t2m4
    · exact budgetRep35k12t2m5
  · refine ⟨[(0, 1), (0x8c2a04d06ca40208a558050440712f5c2034e6451438082d31845, 0), (0x213504101910950575020cad9900890a016c909106bc7c69282102, 0), (0x16085ba2e0252ada00a8730222f864003c90210aa800031404c6b8, 0)], by decide +kernel, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact budgetRep35k12t3m0
    · exact budgetRep35k12t3m1
    · exact budgetRep35k12t3m2
    · exact budgetRep35k12t3m3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma data35 : CaseData ea35 := prepSound ea35 q1_35 q2_35 extra_35 edgePrep35 budgetCases35
lemma excludeOfData (base : Imp [] 0 13) {t : ℕ} (ht : t ∈ smallT) {e : ℕ × ℕ} (he : e ∈ six) (h : CaseData e) : Excluded e (remT (unaryE e) t) := by
  intro S hs hl
  obtain ⟨Q,hE,hP,hQ,hRun⟩ := h
  have hmin : ∀ q < 12, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [e] 0)) :=
    fun q hq h => base (q+1) (by omega) (prefixOne hE h)
  exact imp_of_live (L:=13) (Or.inr ⟨e,he,rfl,base⟩) hP (by norm_num) hQ (by norm_num) hs hl hmin (Or.inr (hRun t ht))
lemma allExcluded (base : Imp [] 0 13) {t : ℕ} (ht : t ∈ smallT) :
    ∀ e ∈ six, Excluded e (remT (unaryE e) t) := by
  intro e he
  simp only [six,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mirror0 _ (excludeOfData base ht (e:=ea15) (by decide +kernel) data15)
  · exact mirror1 _ (excludeOfData base ht (e:=ea20) (by decide +kernel) data20)
  · exact mirror2 _ (excludeOfData base ht (e:=ea21) (by decide +kernel) data21)
  · exact mirror3 _ (excludeOfData base ht (e:=ea21) (by decide +kernel) data21)
  · exact mirror4 _ (excludeOfData base ht (e:=ea23) (by decide +kernel) data23)
  · exact mirror5 _ (excludeOfData base ht (e:=ea16) (by decide +kernel) data16)
  · exact mirror6 _ (excludeOfData base ht (e:=ea18) (by decide +kernel) data18)
  · exact mirror7 _ (excludeOfData base ht (e:=ea18) (by decide +kernel) data18)
  · exact mirror8 _ (excludeOfData base ht (e:=ea19) (by decide +kernel) data19)
  · exact excludeOfData base ht (e:=ea9) (by decide +kernel) data9
  · exact mirror10 _ (excludeOfData base ht (e:=ea9) (by decide +kernel) data9)
  · exact mirror11 _ (excludeOfData base ht (e:=ea26) (by decide +kernel) data26)
  · exact mirror12 _ (excludeOfData base ht (e:=ea27) (by decide +kernel) data27)
  · exact excludeOfData base ht (e:=ea13) (by decide +kernel) data13
  · exact mirror14 _ (excludeOfData base ht (e:=ea13) (by decide +kernel) data13)
  · exact excludeOfData base ht (e:=ea15) (by decide +kernel) data15
  · exact excludeOfData base ht (e:=ea16) (by decide +kernel) data16
  · exact mirror17 _ (excludeOfData base ht (e:=ea18) (by decide +kernel) data18)
  · exact excludeOfData base ht (e:=ea18) (by decide +kernel) data18
  · exact excludeOfData base ht (e:=ea19) (by decide +kernel) data19
  · exact excludeOfData base ht (e:=ea20) (by decide +kernel) data20
  · exact excludeOfData base ht (e:=ea21) (by decide +kernel) data21
  · exact mirror22 _ (excludeOfData base ht (e:=ea21) (by decide +kernel) data21)
  · exact excludeOfData base ht (e:=ea23) (by decide +kernel) data23
  · exact mirror24 _ (excludeOfData base ht (e:=ea9) (by decide +kernel) data9)
  · exact mirror25 _ (excludeOfData base ht (e:=ea9) (by decide +kernel) data9)
  · exact excludeOfData base ht (e:=ea26) (by decide +kernel) data26
  · exact excludeOfData base ht (e:=ea27) (by decide +kernel) data27
  · exact mirror28 _ (excludeOfData base ht (e:=ea13) (by decide +kernel) data13)
  · exact mirror29 _ (excludeOfData base ht (e:=ea13) (by decide +kernel) data13)
  · exact excludeOfData base ht (e:=ea30) (by decide +kernel) data30
  · exact mirror31 _ (excludeOfData base ht (e:=ea30) (by decide +kernel) data30)
  · exact excludeOfData base ht (e:=ea32) (by decide +kernel) data32
  · exact mirror33 _ (excludeOfData base ht (e:=ea34) (by decide +kernel) data34)
  · exact excludeOfData base ht (e:=ea34) (by decide +kernel) data34
  · exact excludeOfData base ht (e:=ea35) (by decide +kernel) data35
def tight : List (ℕ × ℕ) := [(1, 8), (2, 9), (4, 8), (8, 8), (16, 8), (32, 10), (64, 9), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tightCheck : tight.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
lemma iTight : ∀ e ∈ tight, Imp [] e.1 e.2 := okAll tightCheck (apI i2 i3)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tightP : pOk 0 tight = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m0 : chk [] tight 0 12 0 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m1 : chk [] tight 0 12 0 0x28a1b08400802402840510201401036a00104048145006211040 0 = false := by decide +kernel
def budgetRoot12k12t0m2Batch0 : List BState := [storedState 1 11 0 0x8ce319ca3394a53 [103,104,105,106,107,108,109],
  storedState 1 11 0 0x8c6719ca329ca53 [103,110,104,106,107,108,109],
  storedState 1 11 0 0x8ce529ca338c653 [103,104,106,107,108,109,111]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m2Batch0OK : budgetRoot12k12t0m2Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRoot12k12t0m2Batch1 : List BState := [storedState 1 11 0 0x8ca729ca319c653 [103,104,106,107,112,108,109],
  storedState 1 11 0 0x8ca739c6319ce51 [103,104,106,107,108,109,113],
  storedState 1 11 0 0x8ce539c6338ce51 [103,104,106,107,108,109,114],
  storedState 1 11 0 0x8ce339c23394e52 [103,104,115,106,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m2Batch1OK : budgetRoot12k12t0m2Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRoot12k12t0m2Batch2 : List BState := [storedState 1 11 0 0x8c6739c2329ce52 [103,116,104,106,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m2Batch2OK : budgetRoot12k12t0m2Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRoot12k12t0m2Cache : List BState := budgetRoot12k12t0m2Batch0 ++ (budgetRoot12k12t0m2Batch1 ++ (budgetRoot12k12t0m2Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m2Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 budgetRoot12k12t0m2Cache) [] tight 0 12 0 0x2410480070302800800300a488820e5000490304244001001a8201 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m2 : chk [] tight 0 12 0 0x2410480070302800800300a488820e5000490304244001001a8201 0 = false := by
  apply budgetMemo_join [] tight 0 12 0 0x2410480070302800800300a488820e5000490304244001001a8201 0 budgetRoot12k12t0m2Cache _ budgetRoot12k12t0m2Lookup
  intro c hc
  simp only [budgetRoot12k12t0m2Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot12k12t0m2Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot12k12t0m2Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot12k12t0m2Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m3 : chk [] tight 0 12 0 0x1802044a0902101a2c1810004509008000a2081012012c0104009c 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m4 : chk [] tight 0 12 0 0x11200020d4301502028030260d00c05148002810802c0806420 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m5 : chk [] tight 0 12 0 0x2000000008004c00040c008100020200000448800828010000800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t0m6 : chk [] tight 0 12 0 0x1c400050040000001000240000000009000202100200028400102 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 0 p.1 p.2 = false := by
  refine ⟨[(0, 1), (0x28a1b08400802402840510201401036a00104048145006211040, 0), (0x2410480070302800800300a488820e5000490304244001001a8201, 0), (0x1802044a0902101a2c1810004509008000a2081012012c0104009c, 0), (0x11200020d4301502028030260d00c05148002810802c0806420, 0), (0x2000000008004c00040c008100020200000448800828010000800, 0), (0x1c400050040000001000240000000009000202100200028400102, 0)], by decide +kernel, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact budgetRoot12k12t0m0
  · exact budgetRoot12k12t0m1
  · exact budgetRoot12k12t0m2
  · exact budgetRoot12k12t0m3
  · exact budgetRoot12k12t0m4
  · exact budgetRoot12k12t0m5
  · exact budgetRoot12k12t0m6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t1m0 : chk [] tight 0 12 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t1m1 : chk [] tight 0 12 1 0x300000572884aa07430088004153220202202081805261026943c0 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t1m2 : chk [] tight 0 12 1 0xf83808041300c0381b17c0aa0cc031804040024400100106b009 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t1m3 : chk [] tight 0 12 1 0xb0047200168513004a4001e108011080510957c008088ec900800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t1m4 : chk [] tight 0 12 1 0x4078080d20004088040602104200cc4788f0a003b2d0610000436 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 1 p.1 p.2 = false := by
  refine ⟨[(0, 1), (0x300000572884aa07430088004153220202202081805261026943c0, 0), (0xf83808041300c0381b17c0aa0cc031804040024400100106b009, 0), (0xb0047200168513004a4001e108011080510957c008088ec900800, 0), (0x4078080d20004088040602104200cc4788f0a003b2d0610000436, 0)], by decide +kernel, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact budgetRoot12k12t1m0
  · exact budgetRoot12k12t1m1
  · exact budgetRoot12k12t1m2
  · exact budgetRoot12k12t1m3
  · exact budgetRoot12k12t1m4
def budgetRoot12k12t2m0Batch0 : List BState := [storedState 1 11 2 0x8c6339ca3294e53 [103,117,104,106,107,108,109],
  storedState 1 11 2 0x8ca539ca318ce53 [103,104,106,118,107,108,109],
  storedState 1 11 2 0x8ce718ca339ca33 [103,104,106,119,107,108,109],
  storedState 1 11 2 0x8ce729c6339c651 [103,104,106,107,108,109,120],
  storedState 1 11 2 0x8c6719ca329ca53 [103,110,104,106,107,108,109],
  storedState 1 11 2 0x8ce319ca3394a53 [103,104,105,106,107,108,109],
  storedState 1 11 2 0x8ce338ca3394e33 [103,104,121,106,107,108,109],
  storedState 1 11 2 0x8c6738ca329ce33 [103,122,104,106,107,108,109],
  storedState 1 11 2 0x8ca729ca319c653 [103,104,106,107,112,108,109],
  storedState 1 11 2 0x8ca739c6319ce51 [103,104,106,107,108,109,113],
  storedState 1 11 2 0x8ce529ca338c653 [103,104,106,107,108,109,111],
  storedState 1 11 2 0x8ce539c6338ce51 [103,104,106,107,108,109,114],
  storedState 1 11 2 0x8c6739c2329ce52 [103,116,104,106,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t2m0Batch0OK : budgetRoot12k12t2m0Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRoot12k12t2m0Batch1 : List BState := [storedState 1 11 2 0x8ce339c23394e52 [103,104,115,106,107,108,109],
  storedState 1 11 2 0x8ce719c2339ca52 [103,104,106,123,107,108,109],
  storedState 1 11 2 0x8ca7394a319ce13 [103,104,106,107,108,124,109],
  storedState 1 11 2 0x8ce5394a338ce13 [103,104,106,107,108,109,125],
  storedState 1 11 2 0x8ce7294a339c613 [103,104,106,107,108,109,126],
  storedState 1 11 2 0x8ce738c2339ce32 [103,104,106,107,127,108,109],
  storedState 1 11 2 0x8ce73946339ce11 [103,104,106,107,108,109,128],
  storedState 0 10 1 0x8c6339ca3284e53 [103,129,104,106,107,108,109],
  storedState 0 10 1 0x8c6719ca329c253 [103,130,104,106,107,108,109],
  storedState 0 10 1 0x8ca139ca318ce53 [103,104,106,131,107,108,109],
  storedState 0 10 1 0x8ca709ca319c653 [103,104,132,106,107,108,109],
  storedState 0 10 1 0x8ca7384a319ce13 [103,104,133,106,107,108,109],
  storedState 0 10 1 0x8ce319ca3394253 [103,104,134,106,107,108,109],
  storedState 0 10 1 0x8ce339c23394e50 [103,104,135,106,107,108,109],
  storedState 0 9 0 0x8c6719ca309c253 [103,104,136,106,107,108,109],
  storedState 0 9 0 0x8c6739c2309ce50 [103,104,137,106,107,108,109],
  storedState 0 10 1 0x8c2539ca318ce53 [103,104,106,107,108,109,138],
  storedState 0 10 1 0x8c2729ca319c653 [103,106,107,108,109,139,140],
  storedState 0 10 1 0x8c2729ca319c653 [103,104,106,107,108,109,140],
  storedState 0 10 1 0x8c27394a319ce13 [103,104,106,107,108,109,141],
  storedState 0 10 1 0x8c2739c6319ce51 [103,106,107,108,109,139,142],
  storedState 0 10 1 0x8c2739c6319ce51 [103,104,106,107,108,109,142],
  storedState 0 10 1 0x8c6339ca3094e53 [103,143,106,107,108,109,139],
  storedState 0 10 1 0x8c6339ca3094e53 [103,104,143,106,107,108,109],
  storedState 0 10 1 0x8c6339ca3284e53 [103,129,104,144,107,108,109],
  storedState 0 10 1 0x8c6719ca309ca53 [103,106,145,107,108,109,139],
  storedState 0 10 1 0x8c6719ca309ca53 [103,104,106,145,107,108,109],
  storedState 0 10 1 0x8c6719ca329c253 [103,130,104,146,106,108,109],
  storedState 0 10 1 0x8c6738ca309ce33 [103,106,107,147,108,109,139],
  storedState 0 10 1 0x8c6738ca309ce33 [103,104,106,107,147,108,109],
  storedState 0 10 1 0x8c6739c2309ce52 [103,106,107,108,148,109,139],
  storedState 0 10 1 0x8c6739c2309ce52 [103,104,106,107,108,148,109],
  storedState 0 10 1 0x8c6739c2329ce50 [103,149,104,106,107,108,109],
  storedState 0 10 1 0x8ca139ca318ce53 [103,104,144,131,107,108,109],
  storedState 0 10 1 0x8ca709ca319c653 [103,104,146,132,106,108,109],
  storedState 0 10 1 0x8ca7384a319ce13 [103,104,150,133,106,107,109],
  storedState 0 10 1 0x8ce129ca338c653 [103,104,144,107,151,108,109],
  storedState 0 10 1 0x8ce129ca338c653 [103,104,106,107,151,108,109],
  storedState 0 10 1 0x8ce1394a338ce13 [103,104,106,107,108,152,109],
  storedState 0 10 1 0x8ce139c6338ce51 [103,104,144,107,108,109,153],
  storedState 0 10 1 0x8ce139c6338ce51 [103,104,106,107,108,109,153],
  storedState 0 10 1 0x8ce319ca3384a53 [103,104,106,154,107,108,109],
  storedState 0 10 1 0x8ce319ca3394253 [103,104,134,146,106,108,109],
  storedState 0 10 1 0x8ce338ca3384e33 [103,104,155,144,107,108,109],
  storedState 0 10 1 0x8ce338ca3384e33 [103,104,106,155,107,108,109],
  storedState 0 10 1 0x8ce339c23384e52 [103,104,106,156,107,108,109],
  storedState 0 10 1 0x8ce339c23394e50 [103,104,135,157,106,107,108],
  storedState 0 10 1 0x8ce509ca338c653 [103,104,106,158,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t2m0Batch1OK : budgetRoot12k12t2m0Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRoot12k12t2m0Batch2 : List BState := [storedState 0 10 1 0x8ce509ca338c653 [103,104,146,106,158,108,109],
  storedState 0 10 1 0x8ce5384a338ce13 [103,104,106,159,107,108,109],
  storedState 0 10 1 0x8ce7094a339c613 [103,104,106,107,108,160,109],
  storedState 0 10 1 0x8ce709c6339c651 [103,104,106,107,108,109,161],
  storedState 0 10 1 0x8ce709c6339c651 [103,104,146,106,108,109,161],
  storedState 0 10 1 0x8ce718ca339c233 [103,104,162,106,107,108,109],
  storedState 0 10 1 0x8ce718ca339c233 [103,104,162,146,106,108,109],
  storedState 0 10 1 0x8ce719c2339c252 [103,104,163,106,107,108,109],
  storedState 0 10 1 0x8ce719c2339c252 [103,104,163,146,106,108,109],
  storedState 0 10 1 0x8ce719c2339ca50 [103,104,164,106,107,108,109],
  storedState 0 10 1 0x8ce719c2339ca50 [103,104,164,157,106,107,108],
  storedState 0 10 1 0x8ce7284a339c613 [103,104,106,107,165,108,109],
  storedState 0 10 1 0x8ce7284a339c613 [103,104,150,106,107,165,109],
  storedState 0 10 1 0x8ce73846339ce11 [103,104,106,107,108,109,166],
  storedState 0 10 1 0x8ce73846339ce11 [103,104,150,106,107,109,166],
  storedState 0 10 1 0x8ce738c2339ce30 [103,104,167,106,107,108,109],
  storedState 0 9 0 0x8c2139ca318ce53 [103,104,106,107,108,109,168],
  storedState 0 9 0 0x8c2709ca319c653 [103,104,106,107,108,109,169],
  storedState 0 9 0 0x8c27384a319ce13 [103,104,106,107,108,109,170],
  storedState 0 9 0 0x8c6339ca3084e53 [103,104,106,171,107,108,109],
  storedState 0 9 0 0x8ce109ca338c653 [103,104,106,107,172,108,109],
  storedState 0 9 0 0x8ce1384a338ce13 [103,104,106,173,107,108,109],
  storedState 0 9 0 0x8ce319ca3384253 [103,174,104,106,107,108,109],
  storedState 0 9 0 0x8ce339c23384e50 [103,175,104,106,107,108,109],
  storedState 0 9 0 0x8ce7084a339c613 [103,104,176,106,107,108,109],
  storedState 0 9 0 0x8ce719c2339c250 [177,103,104,106,107,108,109],
  storedState 0 10 1 0x8c2539ca318ce53 [103,106,107,108,109,139,138],
  storedState 0 10 1 0x8c27394a319ce13 [103,106,107,108,109,139,141],
  storedState 0 10 1 0x8c6739c2329ce50 [103,149,104,157,106,107,108],
  storedState 0 10 1 0x8ce1394a338ce13 [103,104,144,107,108,152,109],
  storedState 0 10 1 0x8ce319ca3384a53 [103,104,154,144,107,108,109],
  storedState 0 10 1 0x8ce339c23384e52 [103,104,156,144,107,108,109],
  storedState 0 10 1 0x8ce5384a338ce13 [103,104,150,106,159,107,109],
  storedState 0 10 1 0x8ce7094a339c613 [103,104,146,106,108,160,109],
  storedState 0 10 1 0x8ce738c2339ce30 [103,104,167,157,106,107,108]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t2m0Batch2OK : budgetRoot12k12t2m0Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 c)) = true := by decide +kernel
def budgetRoot12k12t2m0Cache : List BState := budgetRoot12k12t2m0Batch0 ++ (budgetRoot12k12t2m0Batch1 ++ (budgetRoot12k12t2m0Batch2))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t2m0Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 12 budgetRoot12k12t2m0Cache) [] tight 0 12 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t2m0 : chk [] tight 0 12 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by
  apply budgetMemo_join [] tight 0 12 2 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 budgetRoot12k12t2m0Cache _ budgetRoot12k12t2m0Lookup
  intro c hc
  simp only [budgetRoot12k12t2m0Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot12k12t2m0Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot12k12t2m0Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot12k12t2m0Batch2OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t2 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 2 p.1 p.2 = false := by
  exact one budgetRoot12k12t2m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t3m0 : chk [] tight 0 12 3 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t3 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 3 p.1 p.2 = false := by
  exact one budgetRoot12k12t3m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t4m0 : chk [] tight 0 12 4 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 4 p.1 p.2 = false := by
  exact one budgetRoot12k12t4m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t5m0 : chk [] tight 0 12 5 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 5 p.1 p.2 = false := by
  exact one budgetRoot12k12t5m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t6m0 : chk [] tight 0 12 6 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 6 p.1 p.2 = false := by
  exact one budgetRoot12k12t6m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t7m0 : chk [] tight 0 12 7 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 7 p.1 p.2 = false := by
  exact one budgetRoot12k12t7m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t8m0 : chk [] tight 0 12 8 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 8 p.1 p.2 = false := by
  exact one budgetRoot12k12t8m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t9m0 : chk [] tight 0 12 9 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 9 p.1 p.2 = false := by
  exact one budgetRoot12k12t9m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t10m0 : chk [] tight 0 12 10 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 10 p.1 p.2 = false := by
  exact one budgetRoot12k12t10m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t11m0 : chk [] tight 0 12 11 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 11 p.1 p.2 = false := by
  exact one budgetRoot12k12t11m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot12k12t12m0 : chk [] tight 0 12 12 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin12t12 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 12 12 p.1 p.2 = false := by
  exact one budgetRoot12k12t12m0
def budgetRoot13k13t4m0Batch0 : List BState := [storedState 0 11 3 0x94674a4e5295274 [103,106,107,108,109,139,138],
  storedState 0 11 3 0x94e34a4e5295274 [103,104,144,131,107,108,109],
  storedState 0 11 3 0x94a54a4e519d274 [103,143,106,107,108,109,139],
  storedState 0 11 3 0x94a54a4e538d274 [103,129,104,144,107,108,109],
  storedState 0 11 3 0x94674a4e5295274 [103,104,106,107,108,109,138],
  storedState 0 11 3 0x94a54a4e519d274 [103,104,143,106,107,108,109],
  storedState 0 11 3 0x94a54a4e538d274 [103,129,104,106,107,108,109],
  storedState 0 11 3 0x94e34a4e5295274 [103,104,106,131,107,108,109],
  storedState 0 11 3 0x94a92a4e51a4e74 [103,106,145,107,108,109,139],
  storedState 0 11 3 0x8c694a4e12a5274 [103,106,107,108,109,139,178],
  storedState 0 11 3 0x8d234a4e1495274 [103,104,144,179,107,108,109],
  storedState 0 11 3 0x94693a4e52a4a74 [103,106,107,108,109,139,140],
  storedState 0 11 3 0x946949ce52a5234 [103,106,107,108,109,139,141],
  storedState 0 11 3 0x94a92a4e51a4e74 [103,104,106,145,107,108,109],
  storedState 0 11 3 0x94a92a4e53a4674 [103,130,104,106,107,108,109],
  storedState 0 11 3 0x94a92a4e53a4674 [103,130,104,146,106,108,109],
  storedState 0 11 3 0x94a94a4651a5273 [103,106,107,108,148,109,139],
  storedState 0 11 3 0x94a94a4653a5271 [103,149,104,157,106,107,108],
  storedState 0 11 3 0x94e91a4e52a4a74 [103,104,132,106,107,108,109],
  storedState 0 11 3 0x94e91a4e52a4a74 [103,104,146,132,106,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch0OK : budgetRoot13k13t4m0Batch0.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch1 : List BState := [storedState 0 11 3 0x94e948ce52a5234 [103,104,150,133,106,107,109],
  storedState 0 11 3 0x95252a4e548ce74 [103,104,154,144,107,108,109],
  storedState 0 11 3 0x95252a4e548ce74 [103,104,106,154,107,108,109],
  storedState 0 11 3 0x95252a4e549c674 [103,104,134,146,106,108,109],
  storedState 0 11 3 0x9525494e548d254 [103,104,155,144,107,108,109],
  storedState 0 11 3 0x95254a46549d271 [103,104,135,157,106,107,108],
  storedState 0 11 3 0x952919ce54a4a34 [103,104,146,106,108,160,109],
  storedState 0 11 3 0x95291a4a54a4a72 [103,104,146,106,108,109,161],
  storedState 0 11 3 0x9529294e54a4654 [103,104,162,146,106,108,109],
  storedState 0 11 3 0x84a94a4e31a5274 [180,103,106,107,108,109,139],
  storedState 0 11 3 0x85254a4e348d274 [181,103,104,144,107,108,109],
  storedState 0 11 3 0x85292a4e34a4674 [182,103,104,146,106,108,109],
  storedState 0 11 3 0x85294a4634a5271 [183,103,104,157,106,107,108],
  storedState 0 11 3 0x8d291a4e14a4a74 [103,104,146,184,106,108,109],
  storedState 0 11 3 0x8d2948ce14a5234 [103,104,150,185,106,107,109],
  storedState 0 11 3 0x94693a4e52a4a74 [103,104,106,107,108,109,140],
  storedState 0 11 3 0x94694a4a52a5272 [103,106,107,108,109,139,142],
  storedState 0 11 3 0x94694a4a52a5272 [103,104,106,107,108,109,142],
  storedState 0 11 3 0x94a9494e51a5254 [103,106,107,147,108,109,139],
  storedState 0 11 3 0x94a9494e51a5254 [103,104,106,107,147,108,109],
  storedState 0 11 3 0x94a9494e53a5214 [103,186,104,150,106,107,109],
  storedState 0 11 3 0x94a94a4651a5273 [103,104,106,107,108,148,109],
  storedState 0 11 3 0x94a94a4653a5271 [103,149,104,106,107,108,109],
  storedState 0 11 3 0x94e948ce52a5234 [103,104,133,106,107,108,109],
  storedState 0 11 3 0x95233a4e5494a74 [103,104,144,107,151,108,109],
  storedState 0 11 3 0x95233a4e5494a74 [103,104,106,107,151,108,109],
  storedState 0 11 3 0x952349ce5495234 [103,104,144,107,108,152,109],
  storedState 0 11 3 0x952349ce5495234 [103,104,106,107,108,152,109],
  storedState 0 11 3 0x95234a4a5495272 [103,104,144,107,108,109,153],
  storedState 0 11 3 0x95234a4a5495272 [103,104,106,107,108,109,153],
  storedState 0 11 3 0x95252a4e549c674 [103,104,134,106,107,108,109],
  storedState 0 11 3 0x9525494e548d254 [103,104,106,155,107,108,109],
  storedState 0 11 3 0x95254a46548d273 [103,104,156,144,107,108,109],
  storedState 0 11 3 0x95254a46548d273 [103,104,106,156,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch1OK : budgetRoot13k13t4m0Batch1.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch2 : List BState := [storedState 0 11 3 0x95254a46549d271 [103,104,135,106,107,108,109],
  storedState 0 11 3 0x95271a4e5494a74 [103,104,106,158,107,108,109],
  storedState 0 11 3 0x95271a4e5494a74 [103,104,146,106,158,108,109],
  storedState 0 11 3 0x952748ce5495234 [103,104,150,106,159,107,109],
  storedState 0 11 3 0x95291a4a54a4a72 [103,104,106,107,108,109,161],
  storedState 0 11 3 0x95292a4654a4673 [103,104,163,146,106,108,109],
  storedState 0 11 3 0x95292a4654a4e71 [103,104,164,157,106,107,108],
  storedState 0 11 3 0x952938ce54a4a34 [103,104,106,107,165,108,109],
  storedState 0 11 3 0x952938ce54a4a34 [103,104,150,106,107,165,109],
  storedState 0 11 3 0x952948ca54a5232 [103,104,106,107,108,109,166],
  storedState 0 11 3 0x952948ca54a5232 [103,104,150,106,107,109,166],
  storedState 0 11 3 0x9529494654a5213 [103,104,187,106,107,108,109],
  storedState 0 11 3 0x9529494654a5213 [103,104,187,150,106,107,109],
  storedState 0 11 3 0x9529494654a5251 [103,104,167,106,107,108,109],
  storedState 0 11 3 0x9529494654a5251 [103,104,167,157,106,107,108],
  storedState 0 11 3 0x952949c254a5232 [103,104,106,107,108,188,109],
  storedState 0 11 3 0x952949c254a5232 [103,104,157,106,107,108,188],
  storedState 0 10 2 0x94634a4e5295274 [103,144,107,108,109,139,168],
  storedState 0 10 2 0x94a54a4e518d274 [103,171,144,107,108,109,139],
  storedState 0 11 3 0x84a94a4e31a5274 [180,103,104,106,107,108,109],
  storedState 0 11 3 0x85292a4e34a4674 [182,103,104,106,107,108,109],
  storedState 0 11 3 0x8529494e34a5214 [189,103,104,150,106,107,109],
  storedState 0 11 3 0x8c694a4e12a5274 [103,104,106,107,108,109,178],
  storedState 0 11 3 0x8d234a4e1495274 [103,104,106,179,107,108,109],
  storedState 0 11 3 0x8d294a4214a5272 [103,104,157,190,106,107,108],
  storedState 0 11 3 0x946949ce52a5234 [103,104,106,107,108,109,141],
  storedState 0 11 3 0x94a9494e53a5214 [103,186,104,106,107,108,109],
  storedState 0 11 3 0x94e94a4252a5272 [103,104,191,106,107,108,109],
  storedState 0 11 3 0x94e94a4252a5272 [103,104,157,191,106,107,108],
  storedState 0 11 3 0x9525494e549d214 [103,104,192,150,106,107,109],
  storedState 0 11 3 0x952748ce5495234 [103,104,106,159,107,108,109],
  storedState 0 11 3 0x95274a425495272 [103,104,106,193,107,108,109],
  storedState 0 11 3 0x95274a425495272 [103,104,157,106,193,107,108],
  storedState 0 11 3 0x952919ce54a4a34 [103,104,106,107,108,160,109],
  storedState 0 11 3 0x9529294e54a4654 [103,104,162,106,107,108,109],
  storedState 0 11 3 0x9529294e54a4e14 [103,104,194,106,107,108,109],
  storedState 0 11 3 0x9529294e54a4e14 [103,104,194,150,106,107,109],
  storedState 0 11 3 0x95292a4654a4673 [103,104,163,106,107,108,109],
  storedState 0 11 3 0x95292a4654a4e71 [103,104,164,106,107,108,109],
  storedState 0 11 3 0x95293a4254a4a72 [103,104,106,107,195,108,109],
  storedState 0 11 3 0x95293a4254a4a72 [103,104,157,106,107,195,108],
  storedState 0 10 2 0x94634a4e5295274 [103,106,107,108,109,139,168],
  storedState 0 10 2 0x94634a4e5295274 [103,104,144,107,108,109,168]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch2OK : budgetRoot13k13t4m0Batch2.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch3 : List BState := [storedState 0 10 2 0x94634a4e5295274 [103,104,106,107,108,109,168],
  storedState 0 10 2 0x94691a4e52a4a74 [103,146,106,108,109,139,169],
  storedState 0 10 2 0x94691a4e52a4a74 [103,104,106,107,108,109,169],
  storedState 0 10 2 0x94691a4e52a4a74 [103,104,146,106,108,109,169],
  storedState 0 10 2 0x946948ce52a5234 [103,106,107,108,109,139,170],
  storedState 0 10 2 0x946948ce52a5234 [103,150,106,107,109,139,170],
  storedState 0 10 2 0x946948ce52a5234 [103,104,106,107,108,109,170],
  storedState 0 10 2 0x946948ce52a5234 [103,104,150,106,107,109,170],
  storedState 0 10 2 0x94694a4252a5272 [103,157,106,107,108,139,196],
  storedState 0 10 2 0x94694a4252a5272 [103,104,106,107,108,109,196],
  storedState 0 10 2 0x94694a4252a5272 [103,104,157,106,107,108,196],
  storedState 0 10 2 0x94a54a4e518d274 [103,106,171,107,108,109,139],
  storedState 0 10 2 0x94a54a4e518d274 [103,104,171,144,107,108,109],
  storedState 0 10 2 0x94a54a4e518d274 [103,104,106,171,107,108,109],
  storedState 0 10 2 0x94a92a4e51a4674 [103,136,146,106,108,109,139],
  storedState 0 10 2 0x94a92a4e51a4674 [103,104,136,106,107,108,109],
  storedState 0 10 2 0x94a92a4e51a4674 [103,104,136,146,106,108,109],
  storedState 0 10 2 0x94a9494e51a5214 [103,197,150,106,107,109,139],
  storedState 0 10 2 0x94a9494e51a5214 [103,104,197,106,107,108,109],
  storedState 0 10 2 0x94a9494e51a5214 [103,104,197,150,106,107,109],
  storedState 0 10 2 0x94a94a4651a5271 [103,104,137,157,106,107,108],
  storedState 0 10 2 0x95231a4e5494a74 [103,104,146,144,172,108,109],
  storedState 0 10 2 0x95231a4e5494a74 [103,104,146,106,172,108,109],
  storedState 0 10 2 0x952348ce5495234 [103,104,144,173,107,108,109],
  storedState 0 10 2 0x952348ce5495234 [103,104,106,173,107,108,109],
  storedState 0 10 2 0x952348ce5495234 [103,104,150,144,173,107,109],
  storedState 0 10 2 0x952348ce5495234 [103,104,150,106,173,107,109],
  storedState 0 10 2 0x95234a425495272 [103,104,144,198,107,108,109],
  storedState 0 10 2 0x95234a425495272 [103,104,157,106,198,107,108],
  storedState 0 10 2 0x95252a4e548c674 [103,174,104,146,144,108,109],
  storedState 0 10 2 0x95252a4e548c674 [103,174,104,146,106,108,109],
  storedState 0 10 2 0x9525494e548d214 [103,199,104,144,107,108,109],
  storedState 0 10 2 0x9525494e548d214 [103,199,104,150,144,107,109],
  storedState 0 10 2 0x9525494e548d214 [103,199,104,150,106,107,109],
  storedState 0 10 2 0x95254a46548d271 [103,175,104,106,107,108,109],
  storedState 0 10 2 0x95254a46548d271 [103,175,104,157,144,107,108],
  storedState 0 10 2 0x95254a46548d271 [103,175,104,157,106,107,108],
  storedState 0 10 2 0x952918ce54a4a34 [103,104,176,106,107,108,109],
  storedState 0 10 2 0x952918ce54a4a34 [103,104,146,176,106,108,109],
  storedState 0 10 2 0x952918ce54a4a34 [103,104,150,146,176,106,109],
  storedState 0 10 2 0x95291a4254a4a72 [103,104,200,106,107,108,109],
  storedState 0 10 2 0x95291a4254a4a72 [103,104,146,200,106,108,109],
  storedState 0 10 2 0x95291a4254a4a72 [103,104,157,200,106,107,108],
  storedState 0 10 2 0x95291a4254a4a72 [103,104,157,146,200,106,108],
  storedState 0 10 2 0x9529294e54a4614 [103,201,104,106,107,108,109],
  storedState 0 10 2 0x9529294e54a4614 [103,201,104,146,106,108,109],
  storedState 0 10 2 0x9529294e54a4614 [103,201,104,150,106,107,109],
  storedState 0 10 2 0x9529294e54a4614 [103,201,104,150,146,106,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch3OK : budgetRoot13k13t4m0Batch3.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch4 : List BState := [storedState 0 10 2 0x95292a4654a4671 [177,103,104,106,107,108,109],
  storedState 0 10 2 0x95292a4654a4671 [177,103,104,146,106,108,109],
  storedState 0 10 2 0x95292a4654a4671 [177,103,104,157,146,106,108],
  storedState 0 11 3 0x85254a4e348d274 [181,103,104,106,107,108,109],
  storedState 0 11 3 0x8529494e34a5214 [189,103,104,106,107,108,109],
  storedState 0 11 3 0x85294a4634a5271 [183,103,104,106,107,108,109],
  storedState 0 11 3 0x8d291a4e14a4a74 [103,104,184,106,107,108,109],
  storedState 0 11 3 0x8d2948ce14a5234 [103,104,185,106,107,108,109],
  storedState 0 11 3 0x9525494e549d214 [103,104,192,106,107,108,109],
  storedState 0 10 2 0x94690a4e52a4674 [103,104,146,106,107,108,109,169],
  storedState 0 10 2 0x94691a4e52a4a74 [103,106,107,108,109,139,169],
  storedState 0 10 2 0x94694a4252a5272 [103,106,107,108,109,139,196],
  storedState 0 10 2 0x94a92a4e51a4674 [103,136,106,107,108,109,139],
  storedState 0 10 2 0x94a9494e51a5214 [103,197,106,107,108,109,139],
  storedState 0 10 2 0x94a94a4651a5271 [103,137,106,107,108,109,139],
  storedState 0 10 2 0x94a94a4651a5271 [103,137,157,106,107,108,139],
  storedState 0 10 2 0x94a94a4651a5271 [103,104,137,106,107,108,109],
  storedState 0 10 2 0x95231a4e5494a74 [103,104,144,107,172,108,109],
  storedState 0 10 2 0x95231a4e5494a74 [103,104,106,107,172,108,109],
  storedState 0 10 2 0x95234a425495272 [103,104,106,198,107,108,109],
  storedState 0 10 2 0x95234a425495272 [103,104,157,144,198,107,108],
  storedState 0 10 2 0x95251a4e548c274 [103,174,104,146,144,107,108,109],
  storedState 0 10 2 0x95252a4e548c674 [103,174,104,144,107,108,109],
  storedState 0 10 2 0x95252a4e548c674 [103,174,104,106,107,108,109],
  storedState 0 10 2 0x9525494e548d214 [103,199,104,106,107,108,109],
  storedState 0 10 2 0x95254a46548d271 [103,175,104,144,107,108,109],
  storedState 0 10 2 0x952918ce54a4a34 [103,104,150,176,106,107,109],
  storedState 0 10 2 0x95292a4254a4670 [177,103,104,157,106,107,108,109],
  storedState 0 10 2 0x95292a4654a4671 [177,103,104,157,106,107,108],
  storedState 0 10 2 0x952948c254a5232 [103,104,202,106,107,108,109],
  storedState 0 10 2 0x952948c254a5232 [103,104,150,202,106,107,109],
  storedState 0 10 2 0x952948c254a5232 [103,104,157,202,106,107,108],
  storedState 0 10 2 0x952948c254a5232 [103,104,157,150,202,106,107],
  storedState 0 10 2 0x9529494654a5211 [203,103,104,106,107,108,109],
  storedState 0 10 2 0x9529494654a5211 [203,103,104,150,106,107,109],
  storedState 0 10 2 0x9529494654a5211 [203,103,104,157,106,107,108],
  storedState 0 10 2 0x9529494654a5211 [203,103,104,157,150,106,107],
  storedState 0 11 3 0x8d294a4214a5272 [103,104,190,106,107,108,109],
  storedState 0 10 2 0x94214a4e518d274 [103,104,106,144,107,108,109,139,168],
  storedState 0 10 2 0x94234a4e5195274 [103,104,144,107,108,109,139,168],
  storedState 0 10 2 0x94234a4e5195274 [103,104,106,107,108,109,139,168],
  storedState 0 10 2 0x94290a4e51a4674 [103,104,146,106,107,108,109,139,169],
  storedState 0 10 2 0x94291a4e51a4a74 [103,104,106,107,108,109,139,169],
  storedState 0 10 2 0x94291a4e51a4a74 [103,104,146,106,108,109,139,169],
  storedState 0 10 2 0x9429484e51a5214 [103,104,150,106,107,108,109,139,170],
  storedState 0 10 2 0x942948ce51a5234 [103,104,106,107,108,109,139,170],
  storedState 0 10 2 0x942948ce51a5234 [103,104,150,106,107,109,139,170],
  storedState 0 10 2 0x94294a4251a5272 [103,104,106,107,108,109,139,196]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch4OK : budgetRoot13k13t4m0Batch4.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch5 : List BState := [storedState 0 10 2 0x94294a4251a5272 [103,104,157,106,107,108,139,196],
  storedState 0 10 2 0x94614a4e528d274 [103,106,144,107,108,109,139,168],
  storedState 0 10 2 0x94614a4e528d274 [103,104,106,144,107,108,109,168],
  storedState 0 10 2 0x94634a4e5085274 [103,104,106,171,144,107,108,109,139],
  storedState 0 10 2 0x94654a4e508d274 [103,104,171,144,107,108,109,139],
  storedState 0 10 2 0x94654a4e508d274 [103,104,106,171,107,108,109,139],
  storedState 0 10 2 0x94690a4e52a4674 [103,146,106,107,108,109,139,169],
  storedState 0 10 2 0x94691a4e50a4274 [103,104,136,146,106,107,108,109,139],
  storedState 0 10 2 0x94692a4e50a4674 [103,104,136,106,107,108,109,139],
  storedState 0 10 2 0x94692a4e50a4674 [103,104,136,146,106,108,109,139],
  storedState 0 10 2 0x9469484e52a5214 [103,150,106,107,108,109,139,170],
  storedState 0 10 2 0x9469484e52a5214 [103,104,150,106,107,108,109,170],
  storedState 0 10 2 0x9469494e50a5214 [103,104,197,106,107,108,109,139],
  storedState 0 10 2 0x9469494e50a5214 [103,104,197,150,106,107,109,139],
  storedState 0 10 2 0x94694a4250a5270 [103,104,137,157,106,107,108,109,139],
  storedState 0 10 2 0x94694a4650a5271 [103,104,137,106,107,108,109,139],
  storedState 0 10 2 0x94694a4650a5271 [103,104,137,157,106,107,108,139],
  storedState 0 10 2 0x94a34a4e5185274 [103,106,171,144,107,108,109,139],
  storedState 0 10 2 0x94a34a4e5185274 [103,104,106,171,144,107,108,109],
  storedState 0 10 2 0x94a91a4e51a4274 [103,136,146,106,107,108,109,139],
  storedState 0 10 2 0x94a91a4e51a4274 [103,104,136,146,106,107,108,109],
  storedState 0 10 2 0x94a94a4251a5270 [103,137,157,106,107,108,109,139],
  storedState 0 10 2 0x94a94a4251a5270 [103,104,137,157,106,107,108,109],
  storedState 0 10 2 0x95210a4e548c674 [103,104,146,106,144,107,172,108,109],
  storedState 0 10 2 0x95211a4e548ca74 [103,104,106,144,107,172,108,109],
  storedState 0 10 2 0x95211a4e548ca74 [103,104,146,106,144,172,108,109],
  storedState 0 10 2 0x9521484e548d214 [103,104,150,106,144,173,107,108,109],
  storedState 0 10 2 0x952148ce548d234 [103,104,106,144,173,107,108,109],
  storedState 0 10 2 0x952148ce548d234 [103,104,150,106,144,173,107,109],
  storedState 0 10 2 0x95214a42548d272 [103,104,106,144,198,107,108,109],
  storedState 0 10 2 0x95214a42548d272 [103,104,157,106,144,198,107,108],
  storedState 0 10 2 0x95230a4e5494674 [103,104,146,144,107,172,108,109],
  storedState 0 10 2 0x95230a4e5494674 [103,104,146,106,107,172,108,109],
  storedState 0 10 2 0x95231a4e5484274 [103,174,104,146,106,144,107,108,109],
  storedState 0 10 2 0x95232a4e5484674 [103,174,104,106,144,107,108,109],
  storedState 0 10 2 0x95232a4e5484674 [103,174,104,146,106,144,108,109],
  storedState 0 10 2 0x9523484e5495214 [103,104,150,144,173,107,108,109],
  storedState 0 10 2 0x9523484e5495214 [103,104,150,106,173,107,108,109],
  storedState 0 10 2 0x9523494e5485214 [103,199,104,106,144,107,108,109],
  storedState 0 10 2 0x9523494e5485214 [103,199,104,150,106,144,107,109],
  storedState 0 10 2 0x95234a425485270 [103,175,104,157,106,144,107,108,109],
  storedState 0 10 2 0x95234a465485271 [103,175,104,106,144,107,108,109],
  storedState 0 10 2 0x95234a465485271 [103,175,104,157,106,144,107,108],
  storedState 0 10 2 0x95251a4e548c274 [103,174,104,146,106,107,108,109],
  storedState 0 10 2 0x95254a42548d270 [103,175,104,157,144,107,108,109],
  storedState 0 10 2 0x95254a42548d270 [103,175,104,157,106,107,108,109],
  storedState 0 10 2 0x9529084e54a4614 [103,104,150,146,176,106,107,108,109],
  storedState 0 10 2 0x952908ce54a4634 [103,104,146,176,106,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch5OK : budgetRoot13k13t4m0Batch5.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch6 : List BState := [storedState 0 10 2 0x952908ce54a4634 [103,104,150,146,176,106,107,109],
  storedState 0 10 2 0x95290a4254a4672 [103,104,146,200,106,107,108,109],
  storedState 0 10 2 0x95290a4254a4672 [103,104,157,146,200,106,107,108],
  storedState 0 10 2 0x9529184e54a4a14 [103,104,150,176,106,107,108,109],
  storedState 0 10 2 0x9529184e54a4a14 [103,104,150,146,176,106,108,109],
  storedState 0 10 2 0x9529194e54a4214 [103,201,104,146,106,107,108,109],
  storedState 0 10 2 0x9529194e54a4214 [103,201,104,150,146,106,107,109],
  storedState 0 10 2 0x95291a4254a4270 [177,103,104,157,146,106,107,108,109],
  storedState 0 10 2 0x95291a4654a4271 [177,103,104,146,106,107,108,109],
  storedState 0 10 2 0x95291a4654a4271 [177,103,104,157,146,106,107,108],
  storedState 0 10 2 0x95292a4254a4670 [177,103,104,157,146,106,108,109],
  storedState 0 10 2 0x9529484254a5212 [103,104,150,202,106,107,108,109],
  storedState 0 10 2 0x9529484254a5212 [103,104,157,150,202,106,107,108],
  storedState 0 10 2 0x9529494254a5210 [203,103,104,157,106,107,108,109],
  storedState 0 10 2 0x9529494254a5210 [203,103,104,157,150,106,107,109],
  storedState 0 11 3 0x84694a4e30a5274 [180,103,104,106,107,108,109,139],
  storedState 0 11 3 0x85234a4e3485274 [181,103,104,106,144,107,108,109],
  storedState 0 11 3 0x85291a4e34a4274 [182,103,104,146,106,107,108,109],
  storedState 0 11 3 0x85294a4234a5270 [183,103,104,157,106,107,108,109],
  storedState 0 11 3 0x8c294a4e11a5274 [103,104,106,107,108,109,139,178],
  storedState 0 11 3 0x8d214a4e148d274 [103,104,106,144,179,107,108,109],
  storedState 0 11 3 0x8d290a4e14a4674 [103,104,146,184,106,107,108,109],
  storedState 0 11 3 0x8d29484e14a5214 [103,104,150,185,106,107,108,109],
  storedState 0 11 3 0x94274a4e5195274 [103,104,106,107,108,109,139,138],
  storedState 0 11 3 0x94293a4e51a4a74 [103,104,106,107,108,109,139,140],
  storedState 0 11 3 0x942949ce51a5234 [103,104,106,107,108,109,139,141],
  storedState 0 11 3 0x94294a4a51a5272 [103,104,106,107,108,109,139,142],
  storedState 0 11 3 0x94654a4e509d274 [103,104,143,106,107,108,109,139],
  storedState 0 11 3 0x94692a4e50a4e74 [103,104,106,145,107,108,109,139],
  storedState 0 11 3 0x9469494e50a5254 [103,104,106,107,147,108,109,139],
  storedState 0 11 3 0x94694a4650a5273 [103,104,106,107,108,148,109,139],
  storedState 0 11 3 0x94a34a4e5385274 [103,129,104,106,144,107,108,109],
  storedState 0 11 3 0x94a91a4e53a4274 [103,130,104,146,106,107,108,109],
  storedState 0 11 3 0x94a94a4253a5270 [103,149,104,157,106,107,108,109],
  storedState 0 11 3 0x94e14a4e528d274 [103,104,106,144,131,107,108,109],
  storedState 0 11 3 0x94e90a4e52a4674 [103,104,146,132,106,107,108,109],
  storedState 0 11 3 0x94e9484e52a5214 [103,104,150,133,106,107,108,109],
  storedState 0 11 3 0x95213a4e548ca74 [103,104,106,144,107,151,108,109],
  storedState 0 11 3 0x952149ce548d234 [103,104,106,144,107,108,152,109],
  storedState 0 11 3 0x95214a4a548d272 [103,104,106,144,107,108,109,153],
  storedState 0 11 3 0x95232a4e5484e74 [103,104,106,154,144,107,108,109],
  storedState 0 11 3 0x9523494e5485254 [103,104,106,155,144,107,108,109],
  storedState 0 11 3 0x95234a465485273 [103,104,106,156,144,107,108,109],
  storedState 0 11 3 0x95251a4e549c274 [103,104,134,146,106,107,108,109],
  storedState 0 11 3 0x95254a42549d270 [103,104,135,157,106,107,108,109],
  storedState 0 11 3 0x95270a4e5494674 [103,104,146,106,158,107,108,109],
  storedState 0 11 3 0x9527484e5495214 [103,104,150,106,159,107,108,109],
  storedState 0 11 3 0x952909ce54a4634 [103,104,146,106,107,108,160,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch6OK : budgetRoot13k13t4m0Batch6.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Batch7 : List BState := [storedState 0 11 3 0x95290a4a54a4672 [103,104,146,106,107,108,109,161],
  storedState 0 11 3 0x9529194e54a4254 [103,104,162,146,106,107,108,109],
  storedState 0 11 3 0x95291a4654a4273 [103,104,163,146,106,107,108,109],
  storedState 0 11 3 0x95292a4254a4e70 [103,104,164,157,106,107,108,109],
  storedState 0 11 3 0x9529384e54a4a14 [103,104,150,106,107,165,108,109],
  storedState 0 11 3 0x9529484a54a5212 [103,104,150,106,107,108,109,166],
  storedState 0 11 3 0x9529494254a5250 [103,104,167,157,106,107,108,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Batch7OK : budgetRoot13k13t4m0Batch7.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 c)) = true := by decide +kernel
def budgetRoot13k13t4m0Cache : List BState := budgetRoot13k13t4m0Batch0 ++ (budgetRoot13k13t4m0Batch1 ++ (budgetRoot13k13t4m0Batch2 ++ (budgetRoot13k13t4m0Batch3 ++ (budgetRoot13k13t4m0Batch4 ++ (budgetRoot13k13t4m0Batch5 ++ (budgetRoot13k13t4m0Batch6 ++ (budgetRoot13k13t4m0Batch7)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0Lookup : budgetWith (budgetMemo (lz 0) (mz 0) (pL (tight.map fun _ => 16)) 13 budgetRoot13k13t4m0Cache) [] tight 0 13 4 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m0 : chk [] tight 0 13 4 0 1 = false := by
  apply budgetMemo_join [] tight 0 13 4 0 1 budgetRoot13k13t4m0Cache _ budgetRoot13k13t4m0Lookup
  intro c hc
  simp only [budgetRoot13k13t4m0Cache, List.mem_append] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch0OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch1OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch2OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch3OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch4OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch5OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch6OK) c hc
  · simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp budgetRoot13k13t4m0Batch7OK) c hc
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m1 : chk [] tight 0 13 4 0x1808115ca8000008805000081142210040010101000144a0150400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m2 : chk [] tight 0 13 4 0x1082801022002022002a022a00440082002802c010380020a142 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m3 : chk [] tight 0 13 4 0x10204004048204310000124000000b51c8400c41600000e000a80 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m4 : chk [] tight 0 13 4 0x680080004004184052f00800015800800000038212000114a4005 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m5 : chk [] tight 0 13 4 0x2025400201008210400054018488020020129200084a8140801000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t4m6 : chk [] tight 0 13 4 0x40202102951c0008808050402018420168440000840200000038 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 4 p.1 p.2 = false := by
  refine ⟨[(0, 1), (0x1808115ca8000008805000081142210040010101000144a0150400, 0), (0x1082801022002022002a022a00440082002802c010380020a142, 0), (0x10204004048204310000124000000b51c8400c41600000e000a80, 0), (0x680080004004184052f00800015800800000038212000114a4005, 0), (0x2025400201008210400054018488020020129200084a8140801000, 0), (0x40202102951c0008808050402018420168440000840200000038, 0)], by decide +kernel, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact budgetRoot13k13t4m0
  · exact budgetRoot13k13t4m1
  · exact budgetRoot13k13t4m2
  · exact budgetRoot13k13t4m3
  · exact budgetRoot13k13t4m4
  · exact budgetRoot13k13t4m5
  · exact budgetRoot13k13t4m6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t5m0 : chk [] tight 0 13 5 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 5 p.1 p.2 = false := by
  exact one budgetRoot13k13t5m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t6m0 : chk [] tight 0 13 6 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 6 p.1 p.2 = false := by
  exact one budgetRoot13k13t6m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t7m0 : chk [] tight 0 13 7 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 7 p.1 p.2 = false := by
  exact one budgetRoot13k13t7m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t8m0 : chk [] tight 0 13 8 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 8 p.1 p.2 = false := by
  exact one budgetRoot13k13t8m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t9m0 : chk [] tight 0 13 9 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 9 p.1 p.2 = false := by
  exact one budgetRoot13k13t9m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t10m0 : chk [] tight 0 13 10 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 10 p.1 p.2 = false := by
  exact one budgetRoot13k13t10m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t11m0 : chk [] tight 0 13 11 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 11 p.1 p.2 = false := by
  exact one budgetRoot13k13t11m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t12m0 : chk [] tight 0 13 12 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t12 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 12 p.1 p.2 = false := by
  exact one budgetRoot13k13t12m0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem budgetRoot13k13t13m0 : chk [] tight 0 13 13 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma budgetRootJoin13t13 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 13 p.1 p.2 = false := by
  exact one budgetRoot13k13t13m0
lemma iroot : Imp [] 0 13 := imp_ts (Or.inl rfl) tightP (by norm_num) iTight (fun t ht => by
  interval_cases t
  · exact budgetRootJoin12t0
  · exact budgetRootJoin12t1
  · exact budgetRootJoin12t2
  · exact budgetRootJoin12t3
  · exact budgetRootJoin12t4
  · exact budgetRootJoin12t5
  · exact budgetRootJoin12t6
  · exact budgetRootJoin12t7
  · exact budgetRootJoin12t8
  · exact budgetRootJoin12t9
  · exact budgetRootJoin12t10
  · exact budgetRootJoin12t11
  · exact budgetRootJoin12t12)
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 13 t S) : False := by
  have hmin : ∀ q < 13, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 13 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 14 := by have := hm0.size.2; omega
  by_cases hlow : t ≤ 3
  · apply firstExcluded iroot _ hS hl
    apply allExcluded iroot
    simp only [smallT, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] tight 0 13 t p.1 p.2 = false := by
      have ht4 : 4 ≤ t := by omega
      interval_cases t
      · exact budgetRootJoin13t4
      · exact budgetRootJoin13t5
      · exact budgetRootJoin13t6
      · exact budgetRootJoin13t7
      · exact budgetRootJoin13t8
      · exact budgetRootJoin13t9
      · exact budgetRootJoin13t10
      · exact budgetRootJoin13t11
      · exact budgetRootJoin13t12
      · exact budgetRootJoin13t13
    exact imp_of_live (L := 14) (Or.inl rfl) tightP (by norm_num) iTight (by omega) hS hl hmin (Or.inr hM)
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
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1 && x 2) || (x 0 && x 1 && x 3) || (x 0 && x 2 && x 3) || (x 1 && x 2 && x 3) || (x 0 && x 1 && x 4) || (x 0 && x 2 && x 4) || (x 1 && x 2 && x 4) || (x 1 && x 3 && x 4) || (x 0 && x 1 && x 5) || (x 0 && x 2 && x 5) || (x 0 && x 3 && x 4 && x 5) || (x 2 && x 3 && x 4 && x 5)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 2 0) ||| (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0) ||| (rawP.getD 2 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 6 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 6 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 6 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩

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

theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
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

section sixin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target : (Fin 6 → Bool) → Bool := fun x => Nat.testBit (4276676776 * 2 ^ 32 + 3974686848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem f_target : ∀ x : Fin 6 → Bool, f x = target x := by
  decide +kernel

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [0, 17]⟩, ⟨.and, [15, 18]⟩], 19⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem solve (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = target x := by
  obtain ⟨⟨gates, o⟩, fits, size, computes⟩ := h
  have hsz : Circuit.size ⟨gates, o⟩ = gates.length := rfl
  have hws : witness.size = 14 := rfl
  have hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (computes y).trans (f_target y).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 14 ≤ gates.length := by
      by_contra hlt
      by_cases hlt2 : gates.length < 13
      · exact iroot gates.length hlt2 (bridge ⟨gates, o⟩ fits hf)
      · have heq : gates.length = 13 := by omega
        rcases bridge_not gates o fits hnot hf with hsol | ⟨t, ht1, S0, hS0, hl0⟩
        · exact iroot (gates.length - 1) (by omega) hsol
        · rw [heq] at hl0; exact iroot_pos ht1 hS0 hl0
    exact ⟨witness, witness_mono, by omega, witness_eval⟩
  · refine ⟨⟨gates, o⟩, fun g hg => ?_, size, computes⟩
    obtain ⟨ho, hl⟩ := fits g hg
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at ho
    have hmono : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases ho with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hnot ⟨g, hg, h⟩).elim
    exact ⟨hmono, hl⟩

end sixin
end PEqualNP.Outside.L_meta_48482

theorem PEqualNP.Outside.L_meta_48482 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3974686848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3974686848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_48482.solve
