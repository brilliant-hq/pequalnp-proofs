import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47789
def bigNat_0 : Nat := 0x3ffdffefff7ffbffefff7ffdfff7ffabffdbffdbffeaedddbbff77ffdddfff7776dfffeaffff6ffff6ffff7fffbfffdfffeffff0000000000000000
def bigNat_1 : Nat := 0x8800222000888920001500009000090000800040002000100000000000000000000
def bigNat_2 : Nat := 0x40020010008004001000800200080054002400240015122244000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0x3ffc0000003ffe0003ffc40001ffe1fff100e0dc00004ac6012b1819212ae1094a1094f3095404ac0256c12b6095b00000000000000000e9c34e3a73d38b4e5a73e9c5a73d3a999c9d9c1dce225c5b9a700001c1fff7076dfffe200006ffff6000000003fffdfffeffffbfbfbfbfbfbfbfbf
def bigNat_4 : Nat := 0x7ff80000007ff8000fff80011ffe00001fff4060e1c000095406255298242556412a2312a4112a7095584aa0255a12ad0000000000000000126cd36d9b4cd9536b9b466db9b4cdaad6c28ecad7684c5cba9b07ffc1c0007706dfffe80000600006ffff7fff80001fffeffffdfdfdfdfdfdfdfdf
def bigNat_5 : Nat := 0xfff0000001fff0000000fffbffc00001ffec0000700ec000192680a49a02a864988124cd024c8224d9126a8935449a024d6000000000000000025756ba65d12eaeba65d1974f5d3ae8167516f5927a8e89d895d700001dfff0770c0000affff000006ffff7fffbfffc0000ffffefefefefefefefef
def bigNat_6 : Nat := 0x1ffe0000000001fff7ffbffe00000001ffec0000000076e000002a390a08e4033308e10447312473104720239311c988e4c4720000000000000000039b98dc86e63736dcb6e6db926e537027b9a739239c2edc9126e77ffdc0000077600000affff6ffff000007fffbfffdfffe0000f7f7f7f7f7f7f7f7
def bigNat_7 : Nat := 0x1ffefff7ffbffc000000000000000001ffedffedfff50000000033c1cccf0738000f01c5783e3783e3783e3c1c1e0e0f070783800000000000000003dc1ee0f707b838e0c7071c1c70638037c1b7c1bbe0a8110037077ffdddfff700000000affff6ffff6ffff00000000000000000fafafafafafafafa
def bigNat_8 : Nat := 0x1ffefff7ffbffdfff7ffbffefffbffd4000000000000000000003bfe0eeff833bb6ffe007fc007fc007fc03fe01ff00ff807fc000000000000000003e01f00f807c03f00f807e01f807c02b80038003c0000000238077ffdddfff7776dfffe00000000000000000000000000000000fcfcfcfcfcfcfcfc
def bigNat_9 : Nat := 0x3ffdffefff7ffbffefff7ffdfff7ffabffdbffdbffeaedddbbff77ffdddfff7776dfffeaffff6ffff6ffff7fffbfffdfffeffffffffffffffffffff
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
def NN : Nat := 475
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
def segsX : List (ℕ × ℕ) := [(63, 80), (80, 97), (97, 114), (114, 131), (131, 148), (148, 151), (151, 168), (168, 171), (171, 188), (188, 190), (190, 192), (192, 209), (209, 212), (212, 215), (215, 219), (219, 223), (223, 227), (227, 241), (241, 245), (245, 249), (249, 263), (263, 267)]
def segsY : List (ℕ × ℕ) := [(267, 278), (278, 282), (282, 285), (285, 289), (289, 293), (293, 296), (296, 300), (300, 302), (302, 304), (304, 318), (318, 321), (321, 334), (334, 337), (337, 350), (350, 352), (352, 354), (354, 367), (367, 381), (381, 395), (395, 408), (408, 422), (422, 435), (435, 448), (448, 461), (461, 474)]
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
lemma state_covers {t k k' z : ℕ} {v : List W} {S : Finset ℕ}
    (hs : StOk P T l k z v S) (hl : Live R m T k' t S) :
    Nat.beq (cov (pos' t) l v) l = true := by
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

lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    simp only [tst, state_covers X hs hm.1, Bool.cond_true]
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
  simp only [cv, bR, state_covers X hs hl, cond_true] at h
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
  have : Std.Symm (fun a c : L_meta_47789.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
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
    {go : (L_meta_47789.X → L_meta_47789.X → Bool) → List L_meta_47789.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_47789.X.s e
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_47789.X → L_meta_47789.X → Bool) → List L_meta_47789.X → Bool,
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_47789.X.s e))
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
def pairDrops : List Nat := [1560207361738189851390686456566254230566726341952965527083954280107534533540772087961865482790629669117105270110683158248919001075967533752223, 3108504698529635111065116242208254188477625594697205425575646066855904927303238378939291808855873786163547451594629315015292186291677051203503, 6549744358881756856960417996189652683066172746175874885277974081134087947900960063990753725032137288229324646721616539276261749411318121084855, 9527239328241966409413320145868780014616988399764248191330613142646298148799503604164216730524678135681734501205771589743149374783037166500538, 10670597361562799668351825390425790469124192849785532981183774822868593957178341231518613663785132587706501627825928347812476096932373342239932, 298493952407868895774889883236770492099435302420152653689684860184003988489386067072652890599414624325767320831694438855970467791864368975823, 12314918998980733682286791535119927971347296520516200954164823373858707491430580900391283374753631827118651053332175969003067329034195064838103, 12387123519325336592900079297300388215582871451308883129914918600836991553192296939703876637519412339018388088312163124736431990485653726616282, 13721041204994238729164688661236035051599024516177545864964932021962251300373397052072918498772516024701836952336216572073795181511554518277340, 25296796123805720510489863009829235683647747475437511829926188299092038568181107636819882334999167320532898594213298586509989944605122782291943, 28395878266645790272388454408726311756488403867246774843534160015130731923195225848781716938945259246362756493545420874153626033336028630805226, 27443196199739254610856777425344565864636871894291833197717284983007985066206351472844235598130266322621988445072422273703988591034647607831788, 48770018203708932931037012505199138870935204443478913290766373277573052536729103640661037008654223219748259630386073322528720687784439890244338, 48769878633636508651320432459271482554785586360193384883182292758830690737232123058253504663316004298739370308581941331562514010220445641798900, 48771366108930487093783565877489122248235777803292124264016312163073205953307113724133529139346066790213239078059254044608346625714996546959608, 97554641481983021428077146709775135630843400597539191219876505220211186991482855809832633903442101954848674870894469637140303683854592703987711, 97550177953885784437795538868060930079834826722318849589357498524187569232593260786904990786060222533673747004299737729631998023188638267867135, 48979766034799617417406780545588844782241397787599686283383118899975656337749724137672234967844541044195102138996359960533301126037711869706239, 48878555924554522305599567631555667876487772110158156933636666321763333737901509788491923041881822216642065129713531689008147039174766670905343, 49831354285656938505020541179724815810340847016151842356310721578294157831944133924154609415106072027963003796396490011476593745632720878305279, 97548735184918274439691551257280311452414309025361729351346091523577639448446356671107818132915841837634020041299167505996283573322329991675903, 51837811557207756627786552973608917164965045288952873766230047643215782419655983017266242448018476160549406004471880176694058245980691015663615, 48830916006499400959282364458403905783808816603573304609565219368221917813230518409304887211962355600316485179468673026463736851895930635419647, 49974274039822302557858925513854523234479845190804205677893908597781072207202640610011178739950265845460615850862539143152044083263001122045951, 50307754170241646414463025303915768019469810966136189335416007499690376986855272468249304478500755903277114594112969684851705650035365897043967, 50331573425235712690594879551985191142309092533746589077664176232610682544045312681966845025158024921842935846571060882298204097331576656887807, 49188215391912800267247811676141132391810514938116540378971734672652396214952407407266286688464509288863828202845927453533314505327061283897343, 50319663445721932352218354326182031887822802368266104810277316533176198370787821119050366497291628045599736609353074008972646987071213524746239, 48985745740178534525726767202790713535545148646581687964885281514985360986173399822464877021479134694593558664020522547041971389895990231171071, 48961925781150973850253703147102428964487314972625684334066814124656347037407859099545606449629731213736703035482237859651779830444691304742911]
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
    have : Std.Symm (fun a b : L_meta_47789.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_47789.X.s e)) hpb
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
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q,hsol⟩
  have hqL := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k,hk,t,S,hS,hl⟩ := (Nat.find_spec hex).live
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hmin : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ E Z)) := fun j hj => Nat.find_min hex (by omega)
  have ht : t ≤ k := by
    have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun j hj hs => hmin j hj (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
    exact hm.size.2
  exact imp_of_live hE hp hL hI (by omega) hS hl hmin (hb.imp id fun u => u t (by omega))
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht

def rt3 : List (ℕ × ℕ) := [(28, 2), (35, 2), (38, 2), (41, 2), (49, 2), (50, 2), (52, 2), (56, 2), (1216, 2), (1344, 2), (1664, 2), (2368, 2), (2432, 2), (2624, 2), (2688, 2), (2816, 2), (3136, 2), (3200, 2), (3328, 2), (3584, 2)]
def rt2 : List (ℕ × ℕ) := [(3, 2), (5, 3), (6, 2), (9, 2), (10, 3), (12, 2), (17, 2), (18, 2), (20, 3), (24, 3), (33, 5), (34, 5), (36, 3), (40, 3), (48, 7), (66, 5), (68, 4), (72, 5), (80, 5), (96, 5), (129, 5), (132, 5), (136, 4), (144, 5), (160, 5), (192, 2), (257, 4), (258, 5), (264, 5), (272, 4), (288, 5), (320, 3), (384, 2), (513, 5), (514, 4), (516, 5), (528, 4), (544, 5), (576, 2), (640, 3), (768, 2), (1025, 5), (1026, 5), (1028, 5), (1032, 5), (1056, 4), (1088, 5), (1152, 5), (1280, 3), (1536, 3), (2049, 6), (2050, 6), (2052, 5), (2056, 5), (2064, 5), (2112, 5), (2176, 5), (2304, 6), (2560, 6), (3072, 6)]
def rt1 : List (ℕ × ℕ) := [(1, 8), (2, 8), (4, 7), (8, 7), (16, 8), (32, 9), (64, 8), (128, 8), (256, 8), (512, 8), (1024, 9), (2048, 9)]
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
lemma pairOk1 : okE [] (subsetRows rt 4097) (4097, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk2 : okE [] (subsetRows rt 4098) (4098, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk3 : okE [] (subsetRows rt 4099) (4099, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk4 : okE [] (subsetRows rt 4100) (4100, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk5 : okE [] (subsetRows rt 4105) (4105, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk6 : okE [] (subsetRows rt 4107) (4107, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk7 : okE [] (subsetRows rt 4110) (4110, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk8 : okE [] (subsetRows rt 4111) (4111, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk9 : okE [] (subsetRows rt 4112) (4112, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk10 : okE [] (subsetRows rt 4113) (4113, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk11 : okE [] (subsetRows rt 4114) (4114, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk12 : okE [] (subsetRows rt 4115) (4115, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk13 : okE [] (subsetRows rt 4120) (4120, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk14 : okE [] (subsetRows rt 4121) (4121, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk15 : okE [] (subsetRows rt 4122) (4122, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk16 : okE [] (subsetRows rt 4125) (4125, 11) = true := by decide +kernel
def pairBounds : List (ℕ × ℕ) := [(4096, 11), (4097, 11), (4098, 11), (4099, 10), (4100, 11), (4105, 10), (4107, 11), (4110, 10), (4111, 11), (4112, 11), (4113, 11), (4114, 11), (4115, 11), (4120, 11), (4121, 11), (4122, 11), (4125, 11)]
lemma pairValid : ∀ p ∈ pairBounds, Imp [] p.1 p.2 := by
  intro p hp
  simp only [pairBounds, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact imp_okE (Or.inl rfl) pairOk10 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk11 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk12 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk13 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk14 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk15 (fun q hq => ir q (subsetRows_mem hq))
  · exact imp_okE (Or.inl rfl) pairOk16 (fun q hq => ir q (subsetRows_mem hq))
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
def ea0 : ℕ × ℕ := (0, 1)
def q2Keys : List ℕ := [33, 34, 48, 66, 72, 80, 96, 129, 132, 144, 160, 258, 264, 288, 513, 516, 544, 1025, 1026, 1028, 1032, 1088, 1152, 2049, 2050, 2052, 2056, 2064, 2112, 2176, 2304, 2560, 3072]
def q2_0 : List (ℕ × ℕ) := q2Keys.zip [5,5,6,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,4,4,4,5,5,6,6,6]
def q1Keys : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
def q1_0 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,7,9,8,8,7,7,9,9]
def extra_0 : List (ℕ × ℕ) := [(4111, 11)]
def edgeQ0 := q1_0 ++ q2_0 ++ extra_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep0 : six.contains ea0 && allB.all (fun p => okEdge ea0 p.1) &&
  q2_0.all (pass ea0 (lowRt ea0)) &&
  q1_0.all (pass ea0 (q2_0 ++ lowRt ea0)) &&
  extra_0.all (fun p => (lowAll ea0).any (fun b => qual b p)) &&
  pOk 0 edgeQ0 && okEdge ea0 0 = true := by decide +kernel
def ea1 : ℕ × ℕ := (0, 2)
def q2_1 : List (ℕ × ℕ) := q2Keys.zip [5,4,6,5,5,5,5,5,5,4,4,5,5,5,5,5,4,5,4,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_1 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,7,8,8,8,7,8,7,8,9]
def extra_1 : List (ℕ × ℕ) := [(4112, 11)]
def edgeQ1 := q1_1 ++ q2_1 ++ extra_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep1 : six.contains ea1 && allB.all (fun p => okEdge ea1 p.1) &&
  q2_1.all (pass ea1 (lowRt ea1)) &&
  q1_1.all (pass ea1 (q2_1 ++ lowRt ea1)) &&
  extra_1.all (fun p => (lowAll ea1).any (fun b => qual b p)) &&
  pOk 0 edgeQ1 && okEdge ea1 0 = true := by decide +kernel
def ea2 : ℕ × ℕ := (0, 3)
def q2_2 : List (ℕ × ℕ) := q2Keys.zip [5,5,6,5,5,5,5,5,5,4,4,5,5,5,5,5,5,5,5,4,5,5,4,6,6,5,5,5,5,5,6,6,6]
def q1_2 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,7,7,8,8,9]
def extra_2 : List (ℕ × ℕ) := [(4113, 11)]
def edgeQ2 := q1_2 ++ q2_2 ++ extra_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep2 : six.contains ea2 && allB.all (fun p => okEdge ea2 p.1) &&
  q2_2.all (pass ea2 (lowRt ea2)) &&
  q1_2.all (pass ea2 (q2_2 ++ lowRt ea2)) &&
  extra_2.all (fun p => (lowAll ea2).any (fun b => qual b p)) &&
  pOk 0 edgeQ2 && okEdge ea2 0 = true := by decide +kernel
def ea3 : ℕ × ℕ := (0, 4)
def q2_3 : List (ℕ × ℕ) := q2Keys.zip [5,4,7,5,5,5,5,5,5,5,4,4,4,4,5,5,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_3 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,7,8,8,8,7,7,7,9,9]
def extra_3 : List (ℕ × ℕ) := [(4114, 11)]
def edgeQ3 := q1_3 ++ q2_3 ++ extra_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep3 : six.contains ea3 && allB.all (fun p => okEdge ea3 p.1) &&
  q2_3.all (pass ea3 (lowRt ea3)) &&
  q1_3.all (pass ea3 (q2_3 ++ lowRt ea3)) &&
  extra_3.all (fun p => (lowAll ea3).any (fun b => qual b p)) &&
  pOk 0 edgeQ3 && okEdge ea3 0 = true := by decide +kernel
def ea4 : ℕ × ℕ := (0, 5)
def q2_4 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,4,6,6,5,5,5,5,5,6,6,6]
def q1_4 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,8,8,8,9,9]
def extra_4 : List (ℕ × ℕ) := [(4115, 11)]
def edgeQ4 := q1_4 ++ q2_4 ++ extra_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep4 : six.contains ea4 && allB.all (fun p => okEdge ea4 p.1) &&
  q2_4.all (pass ea4 (lowRt ea4)) &&
  q1_4.all (pass ea4 (q2_4 ++ lowRt ea4)) &&
  extra_4.all (fun p => (lowAll ea4).any (fun b => qual b p)) &&
  pOk 0 edgeQ4 && okEdge ea4 0 = true := by decide +kernel
def ea9 : ℕ × ℕ := (2, 3)
def q2_9 : List (ℕ × ℕ) := q2Keys.zip [5,5,6,5,5,4,4,5,5,4,4,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,4,4,6,6,6]
def q1_9 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,7,9,7,7,8,8,9,9]
def extra_9 : List (ℕ × ℕ) := [(4120, 11)]
def edgeQ9 := q1_9 ++ q2_9 ++ extra_9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep9 : six.contains ea9 && allB.all (fun p => okEdge ea9 p.1) &&
  q2_9.all (pass ea9 (lowRt ea9)) &&
  q1_9.all (pass ea9 (q2_9 ++ lowRt ea9)) &&
  extra_9.all (fun p => (lowAll ea9).any (fun b => qual b p)) &&
  pOk 0 edgeQ9 && okEdge ea9 0 = true := by decide +kernel
def ea10 : ℕ × ℕ := (2, 4)
def q2_10 : List (ℕ × ℕ) := q2Keys.zip [5,4,7,4,5,5,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,4,4,6,6,6]
def q1_10 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,7,8,9,8,8,8,7,9,9]
def extra_10 : List (ℕ × ℕ) := [(4121, 11)]
def edgeQ10 := q1_10 ++ q2_10 ++ extra_10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep10 : six.contains ea10 && allB.all (fun p => okEdge ea10 p.1) &&
  q2_10.all (pass ea10 (lowRt ea10)) &&
  q1_10.all (pass ea10 (q2_10 ++ lowRt ea10)) &&
  extra_10.all (fun p => (lowAll ea10).any (fun b => qual b p)) &&
  pOk 0 edgeQ10 && okEdge ea10 0 = true := by decide +kernel
def ea11 : ℕ × ℕ := (2, 5)
def q2_11 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,4,4,5,5,5,4,5,5,5,5,5,5,5,5,5,5,5,4,5,6,6,5,5,5,5,5,6,6,6]
def q1_11 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,7,9,8,7,8,8,9,9]
def extra_11 : List (ℕ × ℕ) := [(4122, 11)]
def edgeQ11 := q1_11 ++ q2_11 ++ extra_11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep11 : six.contains ea11 && allB.all (fun p => okEdge ea11 p.1) &&
  q2_11.all (pass ea11 (lowRt ea11)) &&
  q1_11.all (pass ea11 (q2_11 ++ lowRt ea11)) &&
  extra_11.all (fun p => (lowAll ea11).any (fun b => qual b p)) &&
  pOk 0 edgeQ11 && okEdge ea11 0 = true := by decide +kernel
def ea14 : ℕ × ℕ := (4, 5)
def q2_14 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_14 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,8,8,8,9,9]
def extra_14 : List (ℕ × ℕ) := [(4125, 11)]
def edgeQ14 := q1_14 ++ q2_14 ++ extra_14
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep14 : six.contains ea14 && allB.all (fun p => okEdge ea14 p.1) &&
  q2_14.all (pass ea14 (lowRt ea14)) &&
  q1_14.all (pass ea14 (q2_14 ++ lowRt ea14)) &&
  extra_14.all (fun p => (lowAll ea14).any (fun b => qual b p)) &&
  pOk 0 edgeQ14 && okEdge ea14 0 = true := by decide +kernel
def ea15 : ℕ × ℕ := (6, 1)
def q2_15 : List (ℕ × ℕ) := q2Keys.zip [5,5,6,5,5,5,5,5,5,5,5,5,4,5,5,4,5,5,5,5,5,5,5,6,6,4,4,4,5,5,6,6,6]
def q1_15 : List (ℕ × ℕ) := q1Keys.zip [8,8,6,6,7,9,8,8,8,8,9,9]
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
def q2_16 : List (ℕ × ℕ) := q2Keys.zip [5,4,6,5,5,5,5,5,5,5,5,5,5,5,5,5,4,5,4,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_16 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,7,7,8,8,8,8,7,9,9]
def extra_16 : List (ℕ × ℕ) := [(4097, 11)]
def edgeQ16 := q1_16 ++ q2_16 ++ extra_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep16 : six.contains ea16 && allB.all (fun p => okEdge ea16 p.1) &&
  q2_16.all (pass ea16 (lowRt ea16)) &&
  q1_16.all (pass ea16 (q2_16 ++ lowRt ea16)) &&
  extra_16.all (fun p => (lowAll ea16).any (fun b => qual b p)) &&
  pOk 0 edgeQ16 && okEdge ea16 0 = true := by decide +kernel
def ea17 : ℕ × ℕ := (6, 3)
def q2_17 : List (ℕ × ℕ) := q2Keys.zip [5,5,6,5,5,5,5,5,4,5,4,4,5,5,5,5,5,5,4,4,5,5,4,6,6,5,5,5,5,5,6,6,6]
def q1_17 : List (ℕ × ℕ) := q1Keys.zip [8,7,6,7,7,8,8,8,8,8,8,9]
def extra_17 : List (ℕ × ℕ) := [(4098, 11)]
def edgeQ17 := q1_17 ++ q2_17 ++ extra_17
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep17 : six.contains ea17 && allB.all (fun p => okEdge ea17 p.1) &&
  q2_17.all (pass ea17 (lowRt ea17)) &&
  q1_17.all (pass ea17 (q2_17 ++ lowRt ea17)) &&
  extra_17.all (fun p => (lowAll ea17).any (fun b => qual b p)) &&
  pOk 0 edgeQ17 && okEdge ea17 0 = true := by decide +kernel
def ea18 : ℕ × ℕ := (6, 4)
def q2_18 : List (ℕ × ℕ) := q2Keys.zip [5,4,7,5,5,5,5,5,5,5,5,4,4,5,5,4,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_18 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,7,8,9,8,8,7,8,9,9]
def extra_18 : List (ℕ × ℕ) := [(4099, 10)]
def edgeQ18 := q1_18 ++ q2_18 ++ extra_18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep18 : six.contains ea18 && allB.all (fun p => okEdge ea18 p.1) &&
  q2_18.all (pass ea18 (lowRt ea18)) &&
  q1_18.all (pass ea18 (q2_18 ++ lowRt ea18)) &&
  extra_18.all (fun p => (lowAll ea18).any (fun b => qual b p)) &&
  pOk 0 edgeQ18 && okEdge ea18 0 = true := by decide +kernel
def ea19 : ℕ × ℕ := (6, 5)
def q2_19 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,4,5,5,4,4,5,5,5,5,5,4,5,4,5,4,6,6,5,5,5,5,5,6,6,6]
def q1_19 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,6,8,9,8,8,7,8,8,9]
def extra_19 : List (ℕ × ℕ) := [(4100, 11)]
def edgeQ19 := q1_19 ++ q2_19 ++ extra_19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep19 : six.contains ea19 && allB.all (fun p => okEdge ea19 p.1) &&
  q2_19.all (pass ea19 (lowRt ea19)) &&
  q1_19.all (pass ea19 (q2_19 ++ lowRt ea19)) &&
  extra_19.all (fun p => (lowAll ea19).any (fun b => qual b p)) &&
  pOk 0 edgeQ19 && okEdge ea19 0 = true := by decide +kernel
def ea24 : ℕ × ℕ := (8, 3)
def q2_24 : List (ℕ × ℕ) := q2Keys.zip [5,5,6,4,5,4,5,4,5,4,5,5,5,5,5,5,5,4,4,5,5,5,5,6,6,5,5,4,4,4,6,6,6]
def q1_24 : List (ℕ × ℕ) := q1Keys.zip [7,7,7,7,7,9,8,8,8,8,9,9]
def extra_24 : List (ℕ × ℕ) := [(4105, 10)]
def edgeQ24 := q1_24 ++ q2_24 ++ extra_24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep24 : six.contains ea24 && allB.all (fun p => okEdge ea24 p.1) &&
  q2_24.all (pass ea24 (lowRt ea24)) &&
  q1_24.all (pass ea24 (q2_24 ++ lowRt ea24)) &&
  extra_24.all (fun p => (lowAll ea24).any (fun b => qual b p)) &&
  pOk 0 edgeQ24 && okEdge ea24 0 = true := by decide +kernel
def ea25 : ℕ × ℕ := (8, 4)
def q2_25 : List (ℕ × ℕ) := q2Keys.zip [5,4,7,4,4,5,5,4,5,5,5,5,5,5,4,5,5,5,5,5,5,5,5,6,6,5,4,5,4,4,6,6,6]
def q1_25 : List (ℕ × ℕ) := q1Keys.zip [7,7,7,6,8,9,8,8,8,8,9,9]
def extra_25 : List (ℕ × ℕ) := []
def edgeQ25 := q1_25 ++ q2_25 ++ extra_25
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep25 : six.contains ea25 && allB.all (fun p => okEdge ea25 p.1) &&
  q2_25.all (pass ea25 (lowRt ea25)) &&
  q1_25.all (pass ea25 (q2_25 ++ lowRt ea25)) &&
  extra_25.all (fun p => (lowAll ea25).any (fun b => qual b p)) &&
  pOk 0 edgeQ25 && okEdge ea25 0 = true := by decide +kernel
def ea26 : ℕ × ℕ := (8, 5)
def q2_26 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,4,5,5,4,5,6,6,5,5,5,5,5,6,6,6]
def q1_26 : List (ℕ × ℕ) := q1Keys.zip [8,7,7,7,8,9,8,8,8,8,9,9]
def extra_26 : List (ℕ × ℕ) := [(4107, 11)]
def edgeQ26 := q1_26 ++ q2_26 ++ extra_26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep26 : six.contains ea26 && allB.all (fun p => okEdge ea26 p.1) &&
  q2_26.all (pass ea26 (lowRt ea26)) &&
  q1_26.all (pass ea26 (q2_26 ++ lowRt ea26)) &&
  extra_26.all (fun p => (lowAll ea26).any (fun b => qual b p)) &&
  pOk 0 edgeQ26 && okEdge ea26 0 = true := by decide +kernel
def ea29 : ℕ × ℕ := (10, 5)
def q2_29 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,4,4,5,5,4,4,5,5,4,4,5,4,4,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_29 : List (ℕ × ℕ) := q1Keys.zip [7,7,7,7,8,9,8,8,7,7,9,9]
def extra_29 : List (ℕ × ℕ) := [(4110, 10)]
def edgeQ29 := q1_29 ++ q2_29 ++ extra_29
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep29 : six.contains ea29 && allB.all (fun p => okEdge ea29 p.1) &&
  q2_29.all (pass ea29 (lowRt ea29)) &&
  q1_29.all (pass ea29 (q2_29 ++ lowRt ea29)) &&
  extra_29.all (fun p => (lowAll ea29).any (fun b => qual b p)) &&
  pOk 0 edgeQ29 && okEdge ea29 0 = true := by decide +kernel
def ea30 : ℕ × ℕ := (12, 0)
def q2_30 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_30 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,8,8,8,9,9]
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
def q2_32 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_32 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,8,8,8,9,9]
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
def q2_34 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_34 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,8,8,8,9,9]
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
def q2_35 : List (ℕ × ℕ) := q2Keys.zip [5,5,7,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,5,5,5,5,5,6,6,6]
def q1_35 : List (ℕ × ℕ) := q1Keys.zip [8,8,7,7,8,9,8,8,8,8,9,9]
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
def Excluded (k : ℕ) (e : ℕ × ℕ) (t : ℕ) := ∀ (S : Finset ℕ), (S : Set ℕ) ⊆ C (mz 0) (WZ [e] 0) →
  ¬ Live Z0 (mz 0) (tz 0) k t S
lemma nextExcluded {k t : ℕ} (base : Imp [] 0 (k+1))
    (no : ∀ e ∈ six, Excluded k e (remT (unaryE e) t)) {n : Bool} {s : ℕ} {U : Finset ℕ}
    (tail : Live Z0 (mz 0) (tz 0) k (remT n t) (insert s U))
    (keep : (U : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) (hc : classifyB n s = true) : False := by
  rcases combOr hc with hs | he
  · apply base k (by omega)
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
lemma firstExcluded {k t : ℕ} (base : Imp [] 0 (k+1))
    (no : ∀ e ∈ six, Excluded k e (remT (unaryE e) t)) {S : Finset ℕ}
    (avail : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) (hl : Live Z0 (mz 0) (tz 0) (k+1) t S) : False := by
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
lemma pullExcluded {k : ℕ} (A : WireAction) {e e' : ℕ × ℕ} {t : ℕ}
    (hc : mapChecks A.fn e e' = true) (done : Excluded k e' t) : Excluded k e t := by
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
def lplain : List ℕ := [56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 56, 57, 58, 60, 59, 62, 61, 63, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 951, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 951, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 465, 951, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 951, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 951, 344, 344, 951, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 466, 951, 327, 327, 951, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 468, 951, 346, 951, 330, 951, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 469, 951, 404, 404, 951, 376, 376, 951, 418, 418, 418, 951, 417, 417, 417, 951, 444, 444, 444, 951, 472, 472, 472, 472, 472, 472, 472, 472, 472, 472, 472, 472, 472, 951, 471, 471, 471, 951, 458, 458, 458, 951, 470, 470, 470, 470, 470, 470, 470, 470, 470, 470, 470, 470, 470, 951, 473, 473, 473, 951, 463, 462, 465, 464, 467, 466, 468, 469, 472, 470, 951, 463, 462, 469, 951, 463, 465, 951, 463, 464, 467, 951, 462, 465, 466, 951, 462, 464, 951, 465, 464, 468, 951, 466, 951, 467, 951, 463, 462, 465, 464, 467, 344, 466, 327, 468, 469, 444, 472, 470, 951, 467, 468, 951, 463, 462, 465, 464, 467, 344, 466, 468, 346, 469, 472, 470, 951, 466, 468, 951, 463, 462, 465, 464, 467, 466, 327, 468, 330, 469, 472, 470, 951, 469, 951, 469, 951, 463, 462, 465, 464, 467, 466, 468, 469, 404, 418, 472, 470, 951, 463, 462, 465, 464, 467, 466, 468, 469, 404, 417, 472, 471, 470, 951, 463, 462, 465, 464, 467, 466, 468, 469, 376, 418, 472, 458, 470, 951, 463, 462, 465, 464, 467, 466, 468, 469, 376, 417, 472, 470, 951, 463, 462, 465, 464, 467, 466, 468, 469, 418, 417, 472, 470, 473, 951, 463, 462, 465, 464, 467, 466, 468, 469, 444, 472, 458, 470, 951, 463, 462, 465, 464, 467, 466, 468, 469, 444, 472, 471, 470, 951, 463, 462, 465, 464, 467, 466, 468, 469, 472, 471, 470, 473, 951, 463, 462, 465, 464, 467, 466, 468, 469, 472, 458, 470, 473, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 951, 752, 756, 770, 767, 792, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 752, 756, 763, 759, 792, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 752, 770, 763, 774, 792, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 752, 767, 759, 774, 792, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 752, 767, 776, 792, 811, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 792, 824, 951, 752, 763, 778, 792, 824, 795, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 792, 808, 951, 752, 774, 792, 811, 824, 795, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 824, 951, 808, 951, 752, 756, 792, 824, 808, 828, 826, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 882, 869, 951, 855, 841, 951, 882, 855, 896, 951, 869, 841, 896, 951, 792, 922, 909, 951, 752, 792, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 869, 909, 948, 951, 855, 922, 935, 951, 752, 792, 824, 808, 882, 869, 855, 841, 896, 922, 909, 948, 935, 951, 896, 948, 935, 951, 752, 752, 752, 752, 752, 752, 752, 752, 752, 752, 951, 756, 756, 756, 951, 770, 770, 951, 767, 767, 767, 951, 763, 763, 763, 951, 759, 759, 951, 774, 774, 774, 951, 778, 951, 776, 951, 792, 792, 792, 792, 792, 792, 792, 792, 792, 792, 792, 792, 792, 951, 811, 811, 951, 824, 824, 824, 824, 824, 824, 824, 824, 824, 824, 824, 824, 951, 795, 795, 951, 808, 808, 808, 808, 808, 808, 808, 808, 808, 808, 808, 808, 951, 828, 951, 826, 951, 882, 882, 882, 882, 882, 882, 882, 882, 882, 882, 882, 882, 951, 869, 869, 869, 869, 869, 869, 869, 869, 869, 869, 869, 869, 869, 951, 855, 855, 855, 855, 855, 855, 855, 855, 855, 855, 855, 855, 855, 951, 841, 841, 841, 841, 841, 841, 841, 841, 841, 841, 841, 841, 951, 896, 896, 896, 896, 896, 896, 896, 896, 896, 896, 896, 896, 896, 951, 922, 922, 922, 922, 922, 922, 922, 922, 922, 922, 922, 922, 951, 909, 909, 909, 909, 909, 909, 909, 909, 909, 909, 909, 909, 951, 948, 948, 948, 948, 948, 948, 948, 948, 948, 948, 948, 948, 951, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 935, 951]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mplain : rew lplain (mz 0) = mz 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tplain : twist false lplain (tz 0) = tz 0 := by decide +kernel
def actplain := twisted false lplain mplain tplain
def tblplain := factTable [(0, 1), (1, 0), (2, 3), (3, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 14), (10, 13), (11, 15), (12, 16), (13, 10), (14, 9), (15, 11), (16, 12), (17, 17), (18, 20), (19, 21), (20, 18), (21, 19), (22, 22), (23, 23), (24, 29), (25, 28), (26, 30), (27, 31), (28, 25), (29, 24), (30, 26), (31, 27), (32, 32), (33, 35), (34, 36), (35, 33), (36, 34), (37, 37), (38, 39), (39, 38), (40, 41), (41, 40), (42, 42), (43, 43)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma factsplain : acceptedFacts actplain.fn tblplain = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use5 : useFacts tblplain (1, 2) (0, 3) = true := by decide +kernel
lemma mirror5 (k t : ℕ) : Excluded k (0, 3) t → Excluded k (1, 2) t := pullExcluded actplain (liftFacts factsplain use5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use6 : useFacts tblplain (1, 3) (0, 2) = true := by decide +kernel
lemma mirror6 (k t : ℕ) : Excluded k (0, 2) t → Excluded k (1, 3) t := pullExcluded actplain (liftFacts factsplain use6)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use7 : useFacts tblplain (1, 4) (0, 4) = true := by decide +kernel
lemma mirror7 (k t : ℕ) : Excluded k (0, 4) t → Excluded k (1, 4) t := pullExcluded actplain (liftFacts factsplain use7)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use8 : useFacts tblplain (1, 5) (0, 5) = true := by decide +kernel
lemma mirror8 (k t : ℕ) : Excluded k (0, 5) t → Excluded k (1, 5) t := pullExcluded actplain (liftFacts factsplain use8)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use12 : useFacts tblplain (3, 4) (2, 4) = true := by decide +kernel
lemma mirror12 (k t : ℕ) : Excluded k (2, 4) t → Excluded k (3, 4) t := pullExcluded actplain (liftFacts factsplain use12)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use13 : useFacts tblplain (3, 5) (2, 5) = true := by decide +kernel
lemma mirror13 (k t : ℕ) : Excluded k (2, 5) t → Excluded k (3, 5) t := pullExcluded actplain (liftFacts factsplain use13)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use20 : useFacts tblplain (7, 2) (6, 3) = true := by decide +kernel
lemma mirror20 (k t : ℕ) : Excluded k (6, 3) t → Excluded k (7, 2) t := pullExcluded actplain (liftFacts factsplain use20)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use21 : useFacts tblplain (7, 3) (6, 2) = true := by decide +kernel
lemma mirror21 (k t : ℕ) : Excluded k (6, 2) t → Excluded k (7, 3) t := pullExcluded actplain (liftFacts factsplain use21)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use22 : useFacts tblplain (7, 4) (6, 4) = true := by decide +kernel
lemma mirror22 (k t : ℕ) : Excluded k (6, 4) t → Excluded k (7, 4) t := pullExcluded actplain (liftFacts factsplain use22)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use23 : useFacts tblplain (7, 5) (6, 5) = true := by decide +kernel
lemma mirror23 (k t : ℕ) : Excluded k (6, 5) t → Excluded k (7, 5) t := pullExcluded actplain (liftFacts factsplain use23)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use27 : useFacts tblplain (9, 4) (8, 4) = true := by decide +kernel
lemma mirror27 (k t : ℕ) : Excluded k (8, 4) t → Excluded k (9, 4) t := pullExcluded actplain (liftFacts factsplain use27)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use28 : useFacts tblplain (9, 5) (8, 5) = true := by decide +kernel
lemma mirror28 (k t : ℕ) : Excluded k (8, 5) t → Excluded k (9, 5) t := pullExcluded actplain (liftFacts factsplain use28)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use31 : useFacts tblplain (13, 0) (12, 0) = true := by decide +kernel
lemma mirror31 (k t : ℕ) : Excluded k (12, 0) t → Excluded k (13, 0) t := pullExcluded actplain (liftFacts factsplain use31)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use33 : useFacts tblplain (15, 0) (14, 0) = true := by decide +kernel
lemma mirror33 (k t : ℕ) : Excluded k (14, 0) t → Excluded k (15, 0) t := pullExcluded actplain (liftFacts factsplain use33)
lemma prepSound (e : ℕ × ℕ) (a b c : List (ℕ × ℕ))
    (hp : six.contains e && allB.all (fun p => okEdge e p.1) && b.all (pass e (lowRt e)) &&
      a.all (pass e (b ++ lowRt e)) && c.all (fun p => (lowAll e).any (fun b => qual b p)) &&
      pOk 0 (a ++ b ++ c) && okEdge e 0 = true)
    : okEdge e 0 = true ∧ pOk 0 (a ++ b ++ c) = true ∧ ∀ p ∈ a ++ b ++ c, Imp [e] p.1 p.2 := by
  simp only [Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨he,edges⟩,hb⟩,ha⟩,hc⟩,hP⟩,hE⟩ := hp
  have he' : e ∈ six := by simpa using he
  have lo := lowValid edges
  have prev := lowRtValid lo
  have goodB : ∀ p ∈ b, Imp [e] p.1 p.2 := fun p h => passValid he' lo prev (hb p h)
  have goodA : ∀ p ∈ a, Imp [e] p.1 p.2 := fun p h => passValid he' lo (apI goodB prev) (ha p h)
  have goodC : ∀ p ∈ c, Imp [e] p.1 p.2 := fun p h => qualified (hc p h) lo
  exact ⟨hE,hP,apI (apI goodA goodB) goodC⟩

def runCase (e : ℕ × ℕ) (Q : List (ℕ × ℕ)) (k t : ℕ) : Prop :=
  ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [e] Q 0 k (remT (unaryE e) t) p.1 p.2 = false
lemma afterEdge {k t : ℕ} (bound : k+1 ≤ 15) (base : Imp [] 0 (k+1)) {e : ℕ × ℕ} (he : e ∈ six)
    {Q : List (ℕ × ℕ)} (prep : okEdge e 0 = true ∧ pOk 0 Q = true ∧ ∀ p ∈ Q, Imp [e] p.1 p.2)
    (run : runCase e Q k t) : Excluded k e (remT (unaryE e) t) := by
  intro S hs hl
  obtain ⟨hE,hP,hQ⟩ := prep
  have hmin : ∀ q < k, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [e] 0)) :=
    fun q hq h => base (q+1) (by omega) (prefixOne hE h)
  exact imp_of_live (L:=k+1) (Or.inr ⟨e,he,rfl,base⟩) hP bound hQ (by omega) hs hl hmin (Or.inr run)
def ready0 := prepSound ea0 q1_0 q2_0 extra_0 edgePrep0
noncomputable def ec0 (k t h p : ℕ) := chk [ea0] edgeQ0 0 k (remT (unaryE ea0) t) h p
def ready1 := prepSound ea1 q1_1 q2_1 extra_1 edgePrep1
noncomputable def ec1 (k t h p : ℕ) := chk [ea1] edgeQ1 0 k (remT (unaryE ea1) t) h p
def ready2 := prepSound ea2 q1_2 q2_2 extra_2 edgePrep2
noncomputable def ec2 (k t h p : ℕ) := chk [ea2] edgeQ2 0 k (remT (unaryE ea2) t) h p
def ready3 := prepSound ea3 q1_3 q2_3 extra_3 edgePrep3
noncomputable def ec3 (k t h p : ℕ) := chk [ea3] edgeQ3 0 k (remT (unaryE ea3) t) h p
def ready4 := prepSound ea4 q1_4 q2_4 extra_4 edgePrep4
noncomputable def ec4 (k t h p : ℕ) := chk [ea4] edgeQ4 0 k (remT (unaryE ea4) t) h p
def ready9 := prepSound ea9 q1_9 q2_9 extra_9 edgePrep9
noncomputable def ec9 (k t h p : ℕ) := chk [ea9] edgeQ9 0 k (remT (unaryE ea9) t) h p
def ready10 := prepSound ea10 q1_10 q2_10 extra_10 edgePrep10
noncomputable def ec10 (k t h p : ℕ) := chk [ea10] edgeQ10 0 k (remT (unaryE ea10) t) h p
def ready11 := prepSound ea11 q1_11 q2_11 extra_11 edgePrep11
noncomputable def ec11 (k t h p : ℕ) := chk [ea11] edgeQ11 0 k (remT (unaryE ea11) t) h p
def ready14 := prepSound ea14 q1_14 q2_14 extra_14 edgePrep14
noncomputable def ec14 (k t h p : ℕ) := chk [ea14] edgeQ14 0 k (remT (unaryE ea14) t) h p
def ready15 := prepSound ea15 q1_15 q2_15 extra_15 edgePrep15
noncomputable def ec15 (k t h p : ℕ) := chk [ea15] edgeQ15 0 k (remT (unaryE ea15) t) h p
def ready16 := prepSound ea16 q1_16 q2_16 extra_16 edgePrep16
noncomputable def ec16 (k t h p : ℕ) := chk [ea16] edgeQ16 0 k (remT (unaryE ea16) t) h p
def ready17 := prepSound ea17 q1_17 q2_17 extra_17 edgePrep17
noncomputable def ec17 (k t h p : ℕ) := chk [ea17] edgeQ17 0 k (remT (unaryE ea17) t) h p
def ready18 := prepSound ea18 q1_18 q2_18 extra_18 edgePrep18
noncomputable def ec18 (k t h p : ℕ) := chk [ea18] edgeQ18 0 k (remT (unaryE ea18) t) h p
def ready19 := prepSound ea19 q1_19 q2_19 extra_19 edgePrep19
noncomputable def ec19 (k t h p : ℕ) := chk [ea19] edgeQ19 0 k (remT (unaryE ea19) t) h p
def ready24 := prepSound ea24 q1_24 q2_24 extra_24 edgePrep24
noncomputable def ec24 (k t h p : ℕ) := chk [ea24] edgeQ24 0 k (remT (unaryE ea24) t) h p
def ready25 := prepSound ea25 q1_25 q2_25 extra_25 edgePrep25
noncomputable def ec25 (k t h p : ℕ) := chk [ea25] edgeQ25 0 k (remT (unaryE ea25) t) h p
def ready26 := prepSound ea26 q1_26 q2_26 extra_26 edgePrep26
noncomputable def ec26 (k t h p : ℕ) := chk [ea26] edgeQ26 0 k (remT (unaryE ea26) t) h p
def ready29 := prepSound ea29 q1_29 q2_29 extra_29 edgePrep29
noncomputable def ec29 (k t h p : ℕ) := chk [ea29] edgeQ29 0 k (remT (unaryE ea29) t) h p
def ready30 := prepSound ea30 q1_30 q2_30 extra_30 edgePrep30
noncomputable def ec30 (k t h p : ℕ) := chk [ea30] edgeQ30 0 k (remT (unaryE ea30) t) h p
def ready32 := prepSound ea32 q1_32 q2_32 extra_32 edgePrep32
noncomputable def ec32 (k t h p : ℕ) := chk [ea32] edgeQ32 0 k (remT (unaryE ea32) t) h p
def ready34 := prepSound ea34 q1_34 q2_34 extra_34 edgePrep34
noncomputable def ec34 (k t h p : ℕ) := chk [ea34] edgeQ34 0 k (remT (unaryE ea34) t) h p
def ready35 := prepSound ea35 q1_35 q2_35 extra_35 edgePrep35
noncomputable def ec35 (k t h p : ℕ) := chk [ea35] edgeQ35 0 k (remT (unaryE ea35) t) h p
noncomputable section
abbrev BState := Nat × Nat × Nat × Nat × List (Nat × Nat × Nat × Nat × Nat)
def budgetPack (mode k t z : Nat) (v : List W) : BState :=
  (mode,k,t,z,v.map fun w => (w.s,w.a,w.b,w.c,w.r))
def budgetEval (l m g K : Nat) (c : BState) : Bool :=
  let (mode,k,t,z,ws) := c
  let v := ws.map fun (x,a,b,c,r) => (⟨x,a,b,c,r⟩ : W)
  if mode == 0 then look l m g K k t z v else look1 l m g K K k t z v
def budgetTop (cb : Nat → Nat → Nat → Nat → List W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
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
noncomputable def rowsPass (Q : List (ℕ × ℕ)) (k : ℕ) (xs : List BState) : Bool :=
  xs.all (fun c => !(budgetEval (lz 0) (mz 0) (pL (Q.map fun _ => 16)) k c))
lemma rowsAppend (Q : List (ℕ × ℕ)) (k : ℕ) (xs ys : List BState) :
    rowsPass Q k (xs ++ ys) = (rowsPass Q k xs && rowsPass Q k ys) := List.all_append
noncomputable def outerRun (E Q : List (ℕ × ℕ)) (k t h p : ℕ) (xs : List BState) :=
  budgetWith (budgetMemo (lz 0) (mz 0) (pL (Q.map fun _ => 16)) k xs) E Q 0 k t h p
lemma joinRows {E Q : List (ℕ × ℕ)} {k t h p : ℕ} {xs : List BState}
    (inner : rowsPass Q k xs = true) (outer : outerRun E Q k t h p xs = false) :
    chk E Q 0 k t h p = false :=
  budgetMemo_join _ _ _ _ _ _ _ _ (fun c hc => by
    simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp inner) c hc) outer
def univMask : ℕ := (AA ||| (2 ^ 64 - 1)) ||| (AA <<< NN)
def sig0 : ℕ := bigNat_8
def sig1 : ℕ := bigNat_7
def sig2 : ℕ := (bigNat_4 ||| (bigNat_6 ^^^ univMask))
def sig3 : ℕ := (bigNat_6 ^^^ univMask)
def sig4 : ℕ := bigNat_5
def sig5 : ℕ := bigNat_4
def sig6 : ℕ := bigNat_3
def sig7 : ℕ := ((bigNat_5 &&& bigNat_6) ^^^ univMask)
def sig8 : ℕ := (bigNat_5 ^^^ univMask)
def sig9 : ℕ := (bigNat_3 ||| (bigNat_5 ^^^ univMask))
def sig10 : ℕ := bigNat_6
def sig11 : ℕ := (bigNat_7 ||| (bigNat_6 ^^^ univMask))
def sig12 : ℕ := (bigNat_7 ||| (bigNat_5 ^^^ univMask))
def sig13 : ℕ := (bigNat_4 ^^^ univMask)
def sig14 : ℕ := (bigNat_6 &&& (bigNat_4 ^^^ univMask))
def sig15 : ℕ := (bigNat_3 ^^^ univMask)
def sig16 : ℕ := (bigNat_5 &&& (bigNat_3 ^^^ univMask))
def sig17 : ℕ := ((bigNat_3 &&& bigNat_6) ^^^ univMask)
def sig18 : ℕ := ((bigNat_4 &&& bigNat_5) ^^^ univMask)
def sig19 : ℕ := ((bigNat_3 ||| bigNat_6) ^^^ univMask)
def sig20 : ℕ := ((bigNat_3 &&& bigNat_4) ^^^ univMask)
def sig21 : ℕ := ((bigNat_5 ||| bigNat_6) ^^^ univMask)
def sig22 : ℕ := ((bigNat_4 ||| bigNat_5) ^^^ univMask)
def sig23 : ℕ := ((bigNat_3 ||| bigNat_4) ^^^ univMask)
def sig24 : ℕ := (bigNat_5 ||| (bigNat_6 ^^^ univMask))
def sig25 : ℕ := (bigNat_6 ||| (bigNat_5 ^^^ univMask))
def sig26 : ℕ := (bigNat_3 ||| (bigNat_6 ^^^ univMask))
def sig27 : ℕ := (bigNat_4 ||| (bigNat_5 ^^^ univMask))
def sig28 : ℕ := ((bigNat_4 ||| bigNat_6) ^^^ univMask)
def sig29 : ℕ := ((bigNat_4 &&& bigNat_6) ^^^ univMask)
def sig30 : ℕ := ((bigNat_3 &&& bigNat_5) ^^^ univMask)
def sig31 : ℕ := (bigNat_8 ||| (bigNat_6 ^^^ univMask))
def sig32 : ℕ := (bigNat_7 ^^^ univMask)
def sig33 : ℕ := (bigNat_6 &&& (bigNat_7 ^^^ univMask))
def sig34 : ℕ := (bigNat_7 &&& (bigNat_3 ^^^ univMask))
def sig35 : ℕ := (bigNat_5 &&& (bigNat_6 ^^^ univMask))
def sig36 : ℕ := (bigNat_4 &&& (bigNat_6 ^^^ univMask))
def sig37 : ℕ := (bigNat_3 &&& (bigNat_6 ^^^ univMask))
def sig38 : ℕ := (bigNat_6 ||| (bigNat_3 ^^^ univMask))
def sig39 : ℕ := (bigNat_6 &&& (bigNat_5 ^^^ univMask))
def sig40 : ℕ := (bigNat_6 &&& (bigNat_3 ^^^ univMask))
def sig41 : ℕ := (bigNat_4 &&& (bigNat_5 ^^^ univMask))
def sig42 : ℕ := (bigNat_5 ||| (bigNat_4 ^^^ univMask))
def sig43 : ℕ := (bigNat_5 &&& (bigNat_4 ^^^ univMask))
def sig44 : ℕ := ((bigNat_3 ||| bigNat_5) ^^^ univMask)
def sig45 : ℕ := (bigNat_8 ||| (bigNat_5 ^^^ univMask))
def sig46 : ℕ := (bigNat_8 ||| (bigNat_4 ^^^ univMask))
def sig47 : ℕ := (bigNat_8 ||| (bigNat_3 ^^^ univMask))
def sig48 : ℕ := (bigNat_8 &&& (bigNat_6 ^^^ univMask))
def sig49 : ℕ := (bigNat_8 &&& (bigNat_5 ^^^ univMask))
def sig50 : ℕ := (bigNat_8 &&& (bigNat_4 ^^^ univMask))
def sig51 : ℕ := (bigNat_5 &&& (bigNat_7 ^^^ univMask))
def sig52 : ℕ := (bigNat_5 ||| (bigNat_7 ^^^ univMask))
def sig53 : ℕ := (bigNat_7 ||| (bigNat_4 ^^^ univMask))
def sig54 : ℕ := (bigNat_7 ||| (bigNat_3 ^^^ univMask))
def sig55 : ℕ := (bigNat_7 &&& (bigNat_6 ^^^ univMask))
def sig56 : ℕ := (bigNat_7 &&& (bigNat_5 ^^^ univMask))
def sig57 : ℕ := (bigNat_7 &&& (bigNat_4 ^^^ univMask))
def sig58 : ℕ := (bigNat_6 ||| (bigNat_4 ^^^ univMask))
def sig59 : ℕ := (bigNat_3 &&& (bigNat_5 ^^^ univMask))
def sig60 : ℕ := (bigNat_5 ||| (bigNat_3 ^^^ univMask))
def sig61 : ℕ := (bigNat_3 &&& (bigNat_4 ^^^ univMask))
def sig62 : ℕ := (bigNat_3 ||| (bigNat_4 ^^^ univMask))
def sig63 : ℕ := (bigNat_4 &&& (bigNat_3 ^^^ univMask))
def sig64 : ℕ := (bigNat_8 ||| (bigNat_7 ^^^ univMask))
def sig65 : ℕ := (bigNat_8 &&& (bigNat_3 ^^^ univMask))
def sig66 : ℕ := (bigNat_6 ||| (bigNat_7 ^^^ univMask))
def sig67 : ℕ := (bigNat_4 ||| (bigNat_7 ^^^ univMask))
def sig68 : ℕ := (bigNat_3 ||| (bigNat_7 ^^^ univMask))
def sig69 : ℕ := (bigNat_4 ||| (bigNat_3 ^^^ univMask))
def sig70 : ℕ := (bigNat_8 ^^^ univMask)
def sig71 : ℕ := (bigNat_5 &&& (bigNat_8 ^^^ univMask))
def sig72 : ℕ := (bigNat_8 &&& (bigNat_7 ^^^ univMask))
def sig73 : ℕ := (bigNat_4 &&& (bigNat_7 ^^^ univMask))
def sig74 : ℕ := ((bigNat_4 ||| bigNat_7) ^^^ univMask)
def sig75 : ℕ := (bigNat_7 &&& (bigNat_8 ^^^ univMask))
def sig76 : ℕ := (bigNat_6 &&& (bigNat_8 ^^^ univMask))
def sig77 : ℕ := (bigNat_4 &&& (bigNat_8 ^^^ univMask))
def sig78 : ℕ := (bigNat_3 &&& (bigNat_8 ^^^ univMask))
def sig79 : ℕ := (bigNat_6 ||| (bigNat_8 ^^^ univMask))
def sig80 : ℕ := (bigNat_5 ||| (bigNat_8 ^^^ univMask))
def sig81 : ℕ := (bigNat_4 ||| (bigNat_8 ^^^ univMask))
def sig82 : ℕ := (bigNat_3 ||| (bigNat_8 ^^^ univMask))
def sig83 : ℕ := (bigNat_3 &&& (bigNat_7 ^^^ univMask))
def sig84 : ℕ := ((bigNat_6 ||| bigNat_8) ^^^ univMask)
def sig85 : ℕ := ((bigNat_5 ||| bigNat_8) ^^^ univMask)
def sig86 : ℕ := ((bigNat_3 ||| bigNat_8) ^^^ univMask)
def sig87 : ℕ := ((bigNat_5 &&& bigNat_8) ^^^ univMask)
def sig88 : ℕ := ((bigNat_4 &&& bigNat_8) ^^^ univMask)
def sig89 : ℕ := ((bigNat_3 &&& bigNat_8) ^^^ univMask)
def sig90 : ℕ := ((bigNat_6 ||| bigNat_7) ^^^ univMask)
def sig91 : ℕ := ((bigNat_3 ||| bigNat_7) ^^^ univMask)
def sig92 : ℕ := ((bigNat_6 &&& bigNat_7) ^^^ univMask)
def sig93 : ℕ := ((bigNat_5 &&& bigNat_7) ^^^ univMask)
def sig94 : ℕ := ((bigNat_4 &&& bigNat_7) ^^^ univMask)
def sig95 : ℕ := ((bigNat_3 &&& bigNat_7) ^^^ univMask)
def sig96 : ℕ := (bigNat_7 ||| (bigNat_8 ^^^ univMask))
def sig97 : ℕ := ((bigNat_7 ||| bigNat_8) ^^^ univMask)
def sig98 : ℕ := ((bigNat_4 ||| bigNat_8) ^^^ univMask)
def sig99 : ℕ := (bigNat_7 &&& (bigNat_5 ||| bigNat_6))
def sig100 : ℕ := (bigNat_5 &&& bigNat_6)
def sig101 : ℕ := (bigNat_5 ||| bigNat_6)
def sig102 : ℕ := (bigNat_4 ||| (bigNat_5 &&& bigNat_7))
def sig103 : ℕ := (bigNat_5 &&& bigNat_7)
def sig104 : ℕ := (bigNat_6 ||| (bigNat_5 &&& bigNat_7))
def sig105 : ℕ := (bigNat_5 &&& (bigNat_6 &&& bigNat_7))
def sig106 : ℕ := (bigNat_3 &&& bigNat_4)
def sig107 : ℕ := (bigNat_4 &&& bigNat_5)
def sig108 : ℕ := (bigNat_4 ||| bigNat_5)
def sig109 : ℕ := (bigNat_3 &&& bigNat_6)
def sig110 : ℕ := (bigNat_3 ||| bigNat_6)
def sig111 : ℕ := (bigNat_4 ||| (bigNat_5 &&& bigNat_6))
def sig112 : ℕ := (bigNat_3 ||| (bigNat_5 &&& bigNat_6))
def sig113 : ℕ := (bigNat_6 &&& (bigNat_3 ||| bigNat_5))
def sig114 : ℕ := (bigNat_3 ||| bigNat_4)
def sig115 : ℕ := (bigNat_3 ||| (bigNat_5 &&& bigNat_7))
def sig116 : ℕ := (bigNat_8 ||| (bigNat_5 &&& bigNat_6))
def sig117 : ℕ := (bigNat_8 &&& (bigNat_3 ||| bigNat_7))
def sig118 : ℕ := (bigNat_3 ||| bigNat_7)
def sig119 : ℕ := (bigNat_3 ||| bigNat_8)
def sig120 : ℕ := (bigNat_3 &&& bigNat_8)
def sig121 : ℕ := (bigNat_3 ||| bigNat_5)
def sig122 : ℕ := (bigNat_3 &&& bigNat_5)
def sig123 : ℕ := (sig5 &&& sig113)
def sig124 : ℕ := (sig1 &&& sig113)
def sig125 : ℕ := (sig5 &&& sig10)
def sig126 : ℕ := (sig6 &&& sig1)
def sig127 : ℕ := (sig5 &&& sig1)
def sig128 : ℕ := (sig5 ||| sig113)
def sig129 : ℕ := (sig10 &&& sig1)
def sig130 : ℕ := (sig5 ||| sig10)
def sig131 : ℕ := (sig6 ||| sig99)
def sig132 : ℕ := (sig5 ||| sig99)
def sig133 : ℕ := (sig1 &&& sig0)
def sig134 : ℕ := (sig5 ||| sig1)
def sig135 : ℕ := (sig4 ||| sig1)
def sig136 : ℕ := (sig1 ||| sig113)
def sig137 : ℕ := (sig0 ||| sig113)
def wireEntry (s a b r : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ := (s,a,b,a ||| b,r)
def wireDict : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
wireEntry sig0 33554432 0x80000000000000 3,
wireEntry sig1 1048576 0x4000000000000 3,
wireEntry sig2 0 34359771136 0,
wireEntry sig3 35184372088832 32768 0,
wireEntry sig4 1024 1099511627776 3,
wireEntry sig5 32 34359738368 3,
wireEntry sig6 1 1073741824 3,
wireEntry sig7 0 33792 0,
wireEntry sig8 1099511627776 1024 0,
wireEntry sig9 0 1073742848 0,
wireEntry sig10 32768 35184372088832 3,
wireEntry sig11 0 0x4000000008000 0,
wireEntry sig12 0 0x4000000000400 0,
wireEntry sig13 34359738368 32 0,
wireEntry sig14 34359771136 0 0,
wireEntry sig15 1073741824 1 0,
wireEntry sig16 1073742848 0 0,
wireEntry sig17 0 32769 0,
wireEntry sig18 0 1056 0,
wireEntry sig19 35185445830656 0 0,
wireEntry sig20 0 33 0,
wireEntry sig21 36283883716608 0 0,
wireEntry sig22 1133871366144 0 0,
wireEntry sig23 35433480192 0 0,
wireEntry sig24 0 1099511660544 0,
wireEntry sig25 0 35184372089856 0,
wireEntry sig26 0 1073774592 0,
wireEntry sig27 0 34359739392 0,
wireEntry sig28 35218731827200 0 0,
wireEntry sig29 0 32800 0,
wireEntry sig30 0 1025 0,
wireEntry sig31 0 0x80000000008000 0,
wireEntry sig32 0x4000000000000 1048576 0,
wireEntry sig33 0x4000000008000 0 0,
wireEntry sig34 1074790400 0 0,
wireEntry sig35 35184372089856 0 0,
wireEntry sig36 35184372088864 0 0,
wireEntry sig37 35184372088833 0 0,
wireEntry sig38 0 35184372088833 0,
wireEntry sig39 1099511660544 0 0,
wireEntry sig40 1073774592 0 0,
wireEntry sig41 1099511627808 0 0,
wireEntry sig42 0 1099511627808 0,
wireEntry sig43 34359739392 0 0,
wireEntry sig44 1100585369600 0 0,
wireEntry sig45 0 0x80000000000400 0,
wireEntry sig46 0 0x80000000000020 0,
wireEntry sig47 0 0x80000000000001 0,
wireEntry sig48 35184405643264 0 0,
wireEntry sig49 1099545182208 0 0,
wireEntry sig50 34393292800 0 0,
wireEntry sig51 0x4000000000400 0 0,
wireEntry sig52 0 1099512676352 0,
wireEntry sig53 0 0x4000000000020 0,
wireEntry sig54 0 0x4000000000001 0,
wireEntry sig55 35184373137408 0 0,
wireEntry sig56 1099512676352 0 0,
wireEntry sig57 34360786944 0 0,
wireEntry sig58 0 35184372088864 0,
wireEntry sig59 1099511627777 0 0,
wireEntry sig60 0 1099511627777 0,
wireEntry sig61 34359738369 0 0,
wireEntry sig62 0 1073741856 0,
wireEntry sig63 1073741856 0 0,
wireEntry sig64 0 0x80000000100000 0,
wireEntry sig65 1107296256 0 0,
wireEntry sig66 0 35184373137408 0,
wireEntry sig67 0 34360786944 0,
wireEntry sig68 0 1074790400 0,
wireEntry sig69 0 34359738369 0,
wireEntry sig70 0x80000000000000 33554432 0,
wireEntry sig71 0x80000000000400 0 0,
wireEntry sig72 0x4000002000000 0 0,
wireEntry sig73 0x4000000000020 0 0,
wireEntry sig74 0x4000800000000 0 0,
wireEntry sig75 0x80000000100000 0 0,
wireEntry sig76 0x80000000008000 0 0,
wireEntry sig77 0x80000000000020 0 0,
wireEntry sig78 0x80000000000001 0 0,
wireEntry sig79 0 35184405643264 0,
wireEntry sig80 0 1099545182208 0,
wireEntry sig81 0 34393292800 0,
wireEntry sig82 0 1107296256 0,
wireEntry sig83 0x4000000000001 0 0,
wireEntry sig84 0x80200000000000 0 0,
wireEntry sig85 0x80010000000000 0 0,
wireEntry sig86 0x80000040000000 0 0,
wireEntry sig87 0 33555456 0,
wireEntry sig88 0 33554464 0,
wireEntry sig89 0 33554433 0,
wireEntry sig90 0x4200000000000 0 0,
wireEntry sig91 0x4000040000000 0 0,
wireEntry sig92 0 1081344 0,
wireEntry sig93 0 1049600 0,
wireEntry sig94 0 1048608 0,
wireEntry sig95 0 1048577 0,
wireEntry sig96 0 0x4000002000000 0,
wireEntry sig97 0x84000000000000 0 0,
wireEntry sig98 0x80000800000000 0 0]
def cs (m k t z : ℕ) (ws : List ℕ) : BState := (m,k,t,z,ws.map fun i => wireDict.getD i (0,0,0,0,0))
noncomputable section
abbrev DeepState := ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ)
def deepPack (mode fuel k t z : ℕ) (v : List W) : DeepState :=
  (mode,fuel,k,t,z,v.map fun w => (w.s,w.a,w.b,w.c,w.r))
def deepEval (l m g K : ℕ) (s : DeepState) : Bool :=
  let (mode,fuel,k,t,z,ws) := s
  let v := ws.map fun (x,a,b,c,r) => (⟨x,a,b,c,r⟩ : W)
  if mode == 0 then look l m g fuel k t z v else look1 l m g K fuel k t z v
def deepStep (cb : ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool)
    (l m g K mode : ℕ) : ℕ → ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, _, _ => true
  | fuel+1, k, t, z, v =>
    Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      if mode == 0 then mv (cb 0 fuel) l m g k t z v y
      else Bool.rec (motive := fun _ => Bool) (mv (cb 0 K) l m g k t z v y) true
        (node (cb 1 fuel (Nat.sub k 1) t) (pos t) l m g
          (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)
def deepFn (l m g K mode fuel k t z : ℕ) (v : List W) : Bool :=
  if mode == 0 then look l m g fuel k t z v else look1 l m g K fuel k t z v
lemma deepFnPack (l m g K mode fuel k t z : ℕ) (v : List W) :
    deepEval l m g K (deepPack mode fuel k t z v) = deepFn l m g K mode fuel k t z v := by
  have hv : (v.map (fun w => (w.s,w.a,w.b,w.c,w.r))).map
      (fun (s,a,b,c,r) => (⟨s,a,b,c,r⟩ : W)) = v := by
    induction v with
    | nil => rfl
    | cons w v ih => cases w; simp only [List.map_cons, ih]
  simp only [deepEval,deepPack,deepFn,hv]
lemma deepFnStep (l m g K mode fuel k t z : ℕ) (v : List W) :
    deepStep (deepFn l m g K) l m g K mode fuel k t z v = deepFn l m g K mode fuel k t z v := by
  cases mode <;> cases fuel <;> rfl
def deepMemo (l m g K : ℕ) (cache : List DeepState) (mode fuel k t z : ℕ) (v : List W) : Bool :=
  if deepPack mode fuel k t z v ∈ cache then false else deepFn l m g K mode fuel k t z v
lemma deepMemo_eq (l m g K : ℕ) (cache : List DeepState)
    (ok : ∀ c ∈ cache, deepEval l m g K c = false) : deepMemo l m g K cache = deepFn l m g K := by
  funext mode fuel k t z v
  unfold deepMemo
  split
  next hc => exact ((deepFnPack _ _ _ _ _ _ _ _ _ _).symm.trans (ok _ hc)).symm
  next => rfl
def deepOuter (l m g K : ℕ) (cache : List DeepState) (s : DeepState) : Bool :=
  let (mode,fuel,k,t,z,ws) := s
  let v := ws.map fun (x,a,b,c,r) => (⟨x,a,b,c,r⟩ : W)
  deepStep (deepMemo l m g K cache) l m g K mode fuel k t z v
lemma deepJoin (l m g K : ℕ) (cache : List DeepState) (s : DeepState)
    (ok : ∀ c ∈ cache, deepEval l m g K c = false)
    (outer : deepOuter l m g K cache s = false) : deepEval l m g K s = false := by
  obtain ⟨md,fu,k,t,z,ws⟩ := s
  simpa only [deepOuter,deepMemo_eq _ _ _ _ _ ok,deepFnStep,deepFn,deepEval] using outer
end
def ds (md fu k t z : ℕ) (ws : List ℕ) : DeepState :=
  (md,fu,k,t,z,ws.map fun i => wireDict.getD i (0,0,0,0,0))
def deepen (K : ℕ) (s : BState) : DeepState := (s.1,K,s.2)
lemma atDepth (l m g K : ℕ) (s : BState) : deepEval l m g K (deepen K s) = budgetEval l m g K s := by
  obtain ⟨md,k,t,z,ws⟩ := s
  rfl
noncomputable def deepPass (Q : List (ℕ × ℕ)) (K : ℕ) (children : List DeepState) :=
  children.all (fun c => !(deepEval (lz 0) (mz 0) (pL (Q.map fun _ => 16)) K c))
noncomputable def deepCheck (Q : List (ℕ × ℕ)) (K : ℕ) (children : List DeepState) (s : BState) :=
  deepOuter (lz 0) (mz 0) (pL (Q.map fun _ => 16)) K children (deepen K s)
lemma joinDepth {Q : List (ℕ × ℕ)} {K : ℕ} {children : List DeepState} {parent : BState}
    (h1 : deepPass Q K children = true) (h2 : deepCheck Q K children parent = false) :
    rowsPass Q K [parent] = true := by
  have h := deepJoin (lz 0) (mz 0) (pL (Q.map fun _ => 16)) K children (deepen K parent)
    (fun c hc => by simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp h1) c hc) h2
  rw [atDepth] at h
  change ((!budgetEval (lz 0) (mz 0) (pL (Q.map fun _ => 16)) K parent) && true) = true
  rw [h]
  rfl
lemma deepAppend (Q : List (ℕ × ℕ)) (k : ℕ) (xs ys : List DeepState) :
    deepPass Q k (xs ++ ys) = (deepPass Q k xs && deepPass Q k ys) := List.all_append
theorem leaf0 : ec0 11 0 FF 1 = false := by decide +kernel
def allMasks (f : ℕ → ℕ → Bool) (ms : List (ℕ × ℕ)) : Prop := ∀ p ∈ ms, f p.1 p.2 = false
lemma endMasks {f : ℕ → ℕ → Bool} : allMasks f [] := by intro p hp; simp at hp
lemma addMask {f : ℕ → ℕ → Bool} {h p : ℕ} {ms : List (ℕ × ℕ)}
    (accepted : f h p = false) (tail : allMasks f ms) : allMasks f ((h,p)::ms) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact accepted
  · exact tail v hv
lemma u0k11t0 : runCase ea0 edgeQ0 11 0 := by
  exact one leaf0
theorem leaf1 : ec0 11 1 FF 1 = false := by decide +kernel
lemma u0k11t1 : runCase ea0 edgeQ0 11 1 := by
  exact one leaf1
theorem leaf2 : ec0 11 2 FF 1 = false := by decide +kernel
lemma u0k11t2 : runCase ea0 edgeQ0 11 2 := by
  exact one leaf2
theorem leaf3 : ec0 11 3 FF 1 = false := by decide +kernel
lemma u0k11t3 : runCase ea0 edgeQ0 11 3 := by
  exact one leaf3
lemma lower0 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea0 edgeQ0 11 t := by
  interval_cases t
  · exact u0k11t0
  · exact u0k11t1
  · exact u0k11t2
  · exact u0k11t3
theorem leaf4 : ec1 11 0 FF 1 = false := by decide +kernel
lemma u1k11t0 : runCase ea1 edgeQ1 11 0 := by
  exact one leaf4
theorem leaf5 : ec1 11 1 FF 1 = false := by decide +kernel
lemma u1k11t1 : runCase ea1 edgeQ1 11 1 := by
  exact one leaf5
theorem leaf6 : ec1 11 2 FF 1 = false := by decide +kernel
lemma u1k11t2 : runCase ea1 edgeQ1 11 2 := by
  exact one leaf6
theorem leaf7 : ec1 11 3 FF 1 = false := by decide +kernel
lemma u1k11t3 : runCase ea1 edgeQ1 11 3 := by
  exact one leaf7
lemma lower1 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea1 edgeQ1 11 t := by
  interval_cases t
  · exact u1k11t0
  · exact u1k11t1
  · exact u1k11t2
  · exact u1k11t3
theorem leaf8 : ec2 11 0 FF 1 = false := by decide +kernel
lemma u2k11t0 : runCase ea2 edgeQ2 11 0 := by
  exact one leaf8
theorem leaf9 : ec2 11 1 FF 1 = false := by decide +kernel
lemma u2k11t1 : runCase ea2 edgeQ2 11 1 := by
  exact one leaf9
theorem leaf10 : ec2 11 2 FF 1 = false := by decide +kernel
lemma u2k11t2 : runCase ea2 edgeQ2 11 2 := by
  exact one leaf10
theorem leaf11 : ec2 11 3 FF 1 = false := by decide +kernel
lemma u2k11t3 : runCase ea2 edgeQ2 11 3 := by
  exact one leaf11
lemma lower2 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea2 edgeQ2 11 t := by
  interval_cases t
  · exact u2k11t0
  · exact u2k11t1
  · exact u2k11t2
  · exact u2k11t3
theorem leaf12 : ec3 11 0 FF 1 = false := by decide +kernel
lemma u3k11t0 : runCase ea3 edgeQ3 11 0 := by
  exact one leaf12
theorem leaf13 : ec3 11 1 FF 1 = false := by decide +kernel
lemma u3k11t1 : runCase ea3 edgeQ3 11 1 := by
  exact one leaf13
theorem leaf14 : ec3 11 2 FF 1 = false := by decide +kernel
lemma u3k11t2 : runCase ea3 edgeQ3 11 2 := by
  exact one leaf14
theorem leaf15 : ec3 11 3 FF 1 = false := by decide +kernel
lemma u3k11t3 : runCase ea3 edgeQ3 11 3 := by
  exact one leaf15
lemma lower3 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea3 edgeQ3 11 t := by
  interval_cases t
  · exact u3k11t0
  · exact u3k11t1
  · exact u3k11t2
  · exact u3k11t3
theorem leaf16 : ec4 11 0 FF 1 = false := by decide +kernel
lemma u4k11t0 : runCase ea4 edgeQ4 11 0 := by
  exact one leaf16
theorem leaf17 : ec4 11 1 FF 1 = false := by decide +kernel
lemma u4k11t1 : runCase ea4 edgeQ4 11 1 := by
  exact one leaf17
theorem leaf18 : ec4 11 2 FF 1 = false := by decide +kernel
lemma u4k11t2 : runCase ea4 edgeQ4 11 2 := by
  exact one leaf18
theorem leaf19 : ec4 11 3 FF 1 = false := by decide +kernel
lemma u4k11t3 : runCase ea4 edgeQ4 11 3 := by
  exact one leaf19
lemma lower4 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea4 edgeQ4 11 t := by
  interval_cases t
  · exact u4k11t0
  · exact u4k11t1
  · exact u4k11t2
  · exact u4k11t3
theorem leaf20 : ec9 11 0 FF 1 = false := by decide +kernel
lemma u9k11t0 : runCase ea9 edgeQ9 11 0 := by
  exact one leaf20
theorem leaf21 : ec9 11 1 FF 1 = false := by decide +kernel
lemma u9k11t1 : runCase ea9 edgeQ9 11 1 := by
  exact one leaf21
theorem leaf22 : ec9 11 2 FF 1 = false := by decide +kernel
lemma u9k11t2 : runCase ea9 edgeQ9 11 2 := by
  exact one leaf22
theorem leaf23 : ec9 11 3 FF 1 = false := by decide +kernel
lemma u9k11t3 : runCase ea9 edgeQ9 11 3 := by
  exact one leaf23
lemma lower9 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea9 edgeQ9 11 t := by
  interval_cases t
  · exact u9k11t0
  · exact u9k11t1
  · exact u9k11t2
  · exact u9k11t3
theorem leaf24 : ec10 11 0 FF 1 = false := by decide +kernel
lemma u10k11t0 : runCase ea10 edgeQ10 11 0 := by
  exact one leaf24
theorem leaf25 : ec10 11 1 FF 1 = false := by decide +kernel
lemma u10k11t1 : runCase ea10 edgeQ10 11 1 := by
  exact one leaf25
theorem leaf26 : ec10 11 2 FF 1 = false := by decide +kernel
lemma u10k11t2 : runCase ea10 edgeQ10 11 2 := by
  exact one leaf26
theorem leaf27 : ec10 11 3 FF 1 = false := by decide +kernel
lemma u10k11t3 : runCase ea10 edgeQ10 11 3 := by
  exact one leaf27
lemma lower10 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea10 edgeQ10 11 t := by
  interval_cases t
  · exact u10k11t0
  · exact u10k11t1
  · exact u10k11t2
  · exact u10k11t3
theorem leaf28 : ec11 11 0 FF 1 = false := by decide +kernel
lemma u11k11t0 : runCase ea11 edgeQ11 11 0 := by
  exact one leaf28
theorem leaf29 : ec11 11 1 FF 1 = false := by decide +kernel
lemma u11k11t1 : runCase ea11 edgeQ11 11 1 := by
  exact one leaf29
theorem leaf30 : ec11 11 2 FF 1 = false := by decide +kernel
lemma u11k11t2 : runCase ea11 edgeQ11 11 2 := by
  exact one leaf30
theorem leaf31 : ec11 11 3 FF 1 = false := by decide +kernel
lemma u11k11t3 : runCase ea11 edgeQ11 11 3 := by
  exact one leaf31
lemma lower11 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea11 edgeQ11 11 t := by
  interval_cases t
  · exact u11k11t0
  · exact u11k11t1
  · exact u11k11t2
  · exact u11k11t3
theorem leaf32 : ec14 11 0 FF 1 = false := by decide +kernel
lemma u14k11t0 : runCase ea14 edgeQ14 11 0 := by
  exact one leaf32
theorem leaf33 : ec14 11 1 FF 1 = false := by decide +kernel
lemma u14k11t1 : runCase ea14 edgeQ14 11 1 := by
  exact one leaf33
theorem leaf34 : ec14 11 2 FF 1 = false := by decide +kernel
lemma u14k11t2 : runCase ea14 edgeQ14 11 2 := by
  exact one leaf34
theorem leaf35 : ec14 11 3 FF 1 = false := by decide +kernel
lemma u14k11t3 : runCase ea14 edgeQ14 11 3 := by
  exact one leaf35
lemma lower14 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea14 edgeQ14 11 t := by
  interval_cases t
  · exact u14k11t0
  · exact u14k11t1
  · exact u14k11t2
  · exact u14k11t3
theorem leaf36 : ec15 11 0 FF 1 = false := by decide +kernel
lemma u15k11t0 : runCase ea15 edgeQ15 11 0 := by
  exact one leaf36
theorem leaf37 : ec15 11 1 FF 1 = false := by decide +kernel
lemma u15k11t1 : runCase ea15 edgeQ15 11 1 := by
  exact one leaf37
theorem leaf38 : ec15 11 2 FF 1 = false := by decide +kernel
lemma u15k11t2 : runCase ea15 edgeQ15 11 2 := by
  exact one leaf38
theorem leaf39 : ec15 11 3 FF 1 = false := by decide +kernel
lemma u15k11t3 : runCase ea15 edgeQ15 11 3 := by
  exact one leaf39
lemma lower15 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea15 edgeQ15 11 t := by
  interval_cases t
  · exact u15k11t0
  · exact u15k11t1
  · exact u15k11t2
  · exact u15k11t3
theorem leaf40 : ec16 11 0 FF 1 = false := by decide +kernel
lemma u16k11t0 : runCase ea16 edgeQ16 11 0 := by
  exact one leaf40
theorem leaf41 : ec16 11 1 FF 1 = false := by decide +kernel
lemma u16k11t1 : runCase ea16 edgeQ16 11 1 := by
  exact one leaf41
theorem leaf42 : ec16 11 2 FF 1 = false := by decide +kernel
lemma u16k11t2 : runCase ea16 edgeQ16 11 2 := by
  exact one leaf42
theorem leaf43 : ec16 11 3 FF 1 = false := by decide +kernel
lemma u16k11t3 : runCase ea16 edgeQ16 11 3 := by
  exact one leaf43
lemma lower16 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea16 edgeQ16 11 t := by
  interval_cases t
  · exact u16k11t0
  · exact u16k11t1
  · exact u16k11t2
  · exact u16k11t3
theorem leaf44 : ec17 11 0 FF 1 = false := by decide +kernel
lemma u17k11t0 : runCase ea17 edgeQ17 11 0 := by
  exact one leaf44
theorem leaf45 : ec17 11 1 FF 1 = false := by decide +kernel
lemma u17k11t1 : runCase ea17 edgeQ17 11 1 := by
  exact one leaf45
theorem leaf46 : ec17 11 2 FF 1 = false := by decide +kernel
lemma u17k11t2 : runCase ea17 edgeQ17 11 2 := by
  exact one leaf46
theorem leaf47 : ec17 11 3 FF 1 = false := by decide +kernel
lemma u17k11t3 : runCase ea17 edgeQ17 11 3 := by
  exact one leaf47
lemma lower17 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea17 edgeQ17 11 t := by
  interval_cases t
  · exact u17k11t0
  · exact u17k11t1
  · exact u17k11t2
  · exact u17k11t3
theorem leaf48 : ec18 11 0 FF 1 = false := by decide +kernel
lemma u18k11t0 : runCase ea18 edgeQ18 11 0 := by
  exact one leaf48
theorem leaf49 : ec18 11 1 FF 1 = false := by decide +kernel
lemma u18k11t1 : runCase ea18 edgeQ18 11 1 := by
  exact one leaf49
theorem leaf50 : ec18 11 2 FF 1 = false := by decide +kernel
lemma u18k11t2 : runCase ea18 edgeQ18 11 2 := by
  exact one leaf50
theorem leaf51 : ec18 11 3 FF 1 = false := by decide +kernel
lemma u18k11t3 : runCase ea18 edgeQ18 11 3 := by
  exact one leaf51
lemma lower18 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea18 edgeQ18 11 t := by
  interval_cases t
  · exact u18k11t0
  · exact u18k11t1
  · exact u18k11t2
  · exact u18k11t3
theorem leaf52 : ec19 11 0 FF 1 = false := by decide +kernel
lemma u19k11t0 : runCase ea19 edgeQ19 11 0 := by
  exact one leaf52
theorem leaf53 : ec19 11 1 FF 1 = false := by decide +kernel
lemma u19k11t1 : runCase ea19 edgeQ19 11 1 := by
  exact one leaf53
theorem leaf54 : ec19 11 2 FF 1 = false := by decide +kernel
lemma u19k11t2 : runCase ea19 edgeQ19 11 2 := by
  exact one leaf54
theorem leaf55 : ec19 11 3 FF 1 = false := by decide +kernel
lemma u19k11t3 : runCase ea19 edgeQ19 11 3 := by
  exact one leaf55
lemma lower19 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea19 edgeQ19 11 t := by
  interval_cases t
  · exact u19k11t0
  · exact u19k11t1
  · exact u19k11t2
  · exact u19k11t3
theorem leaf56 : ec24 11 0 FF 1 = false := by decide +kernel
lemma u24k11t0 : runCase ea24 edgeQ24 11 0 := by
  exact one leaf56
theorem leaf57 : ec24 11 1 FF 1 = false := by decide +kernel
lemma u24k11t1 : runCase ea24 edgeQ24 11 1 := by
  exact one leaf57
theorem leaf58 : ec24 11 2 FF 1 = false := by decide +kernel
lemma u24k11t2 : runCase ea24 edgeQ24 11 2 := by
  exact one leaf58
theorem leaf59 : ec24 11 3 FF 1 = false := by decide +kernel
lemma u24k11t3 : runCase ea24 edgeQ24 11 3 := by
  exact one leaf59
lemma lower24 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea24 edgeQ24 11 t := by
  interval_cases t
  · exact u24k11t0
  · exact u24k11t1
  · exact u24k11t2
  · exact u24k11t3
theorem leaf60 : ec25 11 0 FF 1 = false := by decide +kernel
lemma u25k11t0 : runCase ea25 edgeQ25 11 0 := by
  exact one leaf60
theorem leaf61 : ec25 11 1 FF 1 = false := by decide +kernel
lemma u25k11t1 : runCase ea25 edgeQ25 11 1 := by
  exact one leaf61
theorem leaf62 : ec25 11 2 FF 1 = false := by decide +kernel
lemma u25k11t2 : runCase ea25 edgeQ25 11 2 := by
  exact one leaf62
theorem leaf63 : ec25 11 3 FF 1 = false := by decide +kernel
lemma u25k11t3 : runCase ea25 edgeQ25 11 3 := by
  exact one leaf63
lemma lower25 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea25 edgeQ25 11 t := by
  interval_cases t
  · exact u25k11t0
  · exact u25k11t1
  · exact u25k11t2
  · exact u25k11t3
theorem leaf64 : ec26 11 0 FF 1 = false := by decide +kernel
lemma u26k11t0 : runCase ea26 edgeQ26 11 0 := by
  exact one leaf64
theorem leaf65 : ec26 11 1 FF 1 = false := by decide +kernel
lemma u26k11t1 : runCase ea26 edgeQ26 11 1 := by
  exact one leaf65
theorem leaf66 : ec26 11 2 FF 1 = false := by decide +kernel
lemma u26k11t2 : runCase ea26 edgeQ26 11 2 := by
  exact one leaf66
theorem leaf67 : ec26 11 3 FF 1 = false := by decide +kernel
lemma u26k11t3 : runCase ea26 edgeQ26 11 3 := by
  exact one leaf67
lemma lower26 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea26 edgeQ26 11 t := by
  interval_cases t
  · exact u26k11t0
  · exact u26k11t1
  · exact u26k11t2
  · exact u26k11t3
theorem leaf68 : ec29 11 0 FF 1 = false := by decide +kernel
lemma u29k11t0 : runCase ea29 edgeQ29 11 0 := by
  exact one leaf68
theorem leaf69 : ec29 11 1 FF 1 = false := by decide +kernel
lemma u29k11t1 : runCase ea29 edgeQ29 11 1 := by
  exact one leaf69
theorem leaf70 : ec29 11 2 FF 1 = false := by decide +kernel
lemma u29k11t2 : runCase ea29 edgeQ29 11 2 := by
  exact one leaf70
theorem leaf71 : ec29 11 3 FF 1 = false := by decide +kernel
lemma u29k11t3 : runCase ea29 edgeQ29 11 3 := by
  exact one leaf71
lemma lower29 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea29 edgeQ29 11 t := by
  interval_cases t
  · exact u29k11t0
  · exact u29k11t1
  · exact u29k11t2
  · exact u29k11t3
theorem leaf72 : ec30 11 0 FF 1 = false := by decide +kernel
lemma u30k11t0 : runCase ea30 edgeQ30 11 0 := by
  exact one leaf72
theorem leaf73 : ec30 11 1 FF 1 = false := by decide +kernel
lemma u30k11t1 : runCase ea30 edgeQ30 11 1 := by
  exact one leaf73
theorem leaf74 : ec30 11 2 FF 1 = false := by decide +kernel
lemma u30k11t2 : runCase ea30 edgeQ30 11 2 := by
  exact one leaf74
theorem leaf75 : ec30 11 3 FF 1 = false := by decide +kernel
lemma u30k11t3 : runCase ea30 edgeQ30 11 3 := by
  exact one leaf75
lemma lower30 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea30 edgeQ30 11 t := by
  interval_cases t
  · exact u30k11t0
  · exact u30k11t1
  · exact u30k11t2
  · exact u30k11t3
theorem leaf76 : ec32 11 0 FF 1 = false := by decide +kernel
lemma u32k11t0 : runCase ea32 edgeQ32 11 0 := by
  exact one leaf76
theorem leaf77 : ec32 11 1 FF 1 = false := by decide +kernel
lemma u32k11t1 : runCase ea32 edgeQ32 11 1 := by
  exact one leaf77
theorem leaf78 : ec32 11 2 FF 1 = false := by decide +kernel
lemma u32k11t2 : runCase ea32 edgeQ32 11 2 := by
  exact one leaf78
theorem leaf79 : ec32 11 3 FF 1 = false := by decide +kernel
lemma u32k11t3 : runCase ea32 edgeQ32 11 3 := by
  exact one leaf79
lemma lower32 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea32 edgeQ32 11 t := by
  interval_cases t
  · exact u32k11t0
  · exact u32k11t1
  · exact u32k11t2
  · exact u32k11t3
theorem leaf80 : ec34 11 0 FF 1 = false := by decide +kernel
lemma u34k11t0 : runCase ea34 edgeQ34 11 0 := by
  exact one leaf80
theorem leaf81 : ec34 11 1 FF 1 = false := by decide +kernel
lemma u34k11t1 : runCase ea34 edgeQ34 11 1 := by
  exact one leaf81
theorem leaf82 : ec34 11 2 FF 1 = false := by decide +kernel
lemma u34k11t2 : runCase ea34 edgeQ34 11 2 := by
  exact one leaf82
theorem leaf83 : ec34 11 3 FF 1 = false := by decide +kernel
lemma u34k11t3 : runCase ea34 edgeQ34 11 3 := by
  exact one leaf83
lemma lower34 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea34 edgeQ34 11 t := by
  interval_cases t
  · exact u34k11t0
  · exact u34k11t1
  · exact u34k11t2
  · exact u34k11t3
theorem leaf84 : ec35 11 0 FF 1 = false := by decide +kernel
lemma u35k11t0 : runCase ea35 edgeQ35 11 0 := by
  exact one leaf84
theorem leaf85 : ec35 11 1 FF 1 = false := by decide +kernel
lemma u35k11t1 : runCase ea35 edgeQ35 11 1 := by
  exact one leaf85
theorem leaf86 : ec35 11 2 FF 1 = false := by decide +kernel
lemma u35k11t2 : runCase ea35 edgeQ35 11 2 := by
  exact one leaf86
theorem leaf87 : ec35 11 3 FF 1 = false := by decide +kernel
lemma u35k11t3 : runCase ea35 edgeQ35 11 3 := by
  exact one leaf87
lemma lower35 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea35 edgeQ35 11 t := by
  interval_cases t
  · exact u35k11t0
  · exact u35k11t1
  · exact u35k11t2
  · exact u35k11t3
lemma lowerCases (base : Imp [] 0 12) {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : ∀ e ∈ six, Excluded 11 e (remT (unaryE e) t) := by
  intro e he
  simp only [six,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact afterEdge (by decide) base (e:=ea0) (by decide +kernel) ready0 (lower0 ha hb)
  · exact afterEdge (by decide) base (e:=ea1) (by decide +kernel) ready1 (lower1 ha hb)
  · exact afterEdge (by decide) base (e:=ea2) (by decide +kernel) ready2 (lower2 ha hb)
  · exact afterEdge (by decide) base (e:=ea3) (by decide +kernel) ready3 (lower3 ha hb)
  · exact afterEdge (by decide) base (e:=ea4) (by decide +kernel) ready4 (lower4 ha hb)
  · exact mirror5 _ _ (afterEdge (by decide) base (e:=ea2) (by decide +kernel) ready2 (lower2 ha hb))
  · exact mirror6 _ _ (afterEdge (by decide) base (e:=ea1) (by decide +kernel) ready1 (lower1 ha hb))
  · exact mirror7 _ _ (afterEdge (by decide) base (e:=ea3) (by decide +kernel) ready3 (lower3 ha hb))
  · exact mirror8 _ _ (afterEdge (by decide) base (e:=ea4) (by decide +kernel) ready4 (lower4 ha hb))
  · exact afterEdge (by decide) base (e:=ea9) (by decide +kernel) ready9 (lower9 ha hb)
  · exact afterEdge (by decide) base (e:=ea10) (by decide +kernel) ready10 (lower10 ha hb)
  · exact afterEdge (by decide) base (e:=ea11) (by decide +kernel) ready11 (lower11 ha hb)
  · exact mirror12 _ _ (afterEdge (by decide) base (e:=ea10) (by decide +kernel) ready10 (lower10 ha hb))
  · exact mirror13 _ _ (afterEdge (by decide) base (e:=ea11) (by decide +kernel) ready11 (lower11 ha hb))
  · exact afterEdge (by decide) base (e:=ea14) (by decide +kernel) ready14 (lower14 ha hb)
  · exact afterEdge (by decide) base (e:=ea15) (by decide +kernel) ready15 (lower15 ha hb)
  · exact afterEdge (by decide) base (e:=ea16) (by decide +kernel) ready16 (lower16 ha hb)
  · exact afterEdge (by decide) base (e:=ea17) (by decide +kernel) ready17 (lower17 ha hb)
  · exact afterEdge (by decide) base (e:=ea18) (by decide +kernel) ready18 (lower18 ha hb)
  · exact afterEdge (by decide) base (e:=ea19) (by decide +kernel) ready19 (lower19 ha hb)
  · exact mirror20 _ _ (afterEdge (by decide) base (e:=ea17) (by decide +kernel) ready17 (lower17 ha hb))
  · exact mirror21 _ _ (afterEdge (by decide) base (e:=ea16) (by decide +kernel) ready16 (lower16 ha hb))
  · exact mirror22 _ _ (afterEdge (by decide) base (e:=ea18) (by decide +kernel) ready18 (lower18 ha hb))
  · exact mirror23 _ _ (afterEdge (by decide) base (e:=ea19) (by decide +kernel) ready19 (lower19 ha hb))
  · exact afterEdge (by decide) base (e:=ea24) (by decide +kernel) ready24 (lower24 ha hb)
  · exact afterEdge (by decide) base (e:=ea25) (by decide +kernel) ready25 (lower25 ha hb)
  · exact afterEdge (by decide) base (e:=ea26) (by decide +kernel) ready26 (lower26 ha hb)
  · exact mirror27 _ _ (afterEdge (by decide) base (e:=ea25) (by decide +kernel) ready25 (lower25 ha hb))
  · exact mirror28 _ _ (afterEdge (by decide) base (e:=ea26) (by decide +kernel) ready26 (lower26 ha hb))
  · exact afterEdge (by decide) base (e:=ea29) (by decide +kernel) ready29 (lower29 ha hb)
  · exact afterEdge (by decide) base (e:=ea30) (by decide +kernel) ready30 (lower30 ha hb)
  · exact mirror31 _ _ (afterEdge (by decide) base (e:=ea30) (by decide +kernel) ready30 (lower30 ha hb))
  · exact afterEdge (by decide) base (e:=ea32) (by decide +kernel) ready32 (lower32 ha hb)
  · exact mirror33 _ _ (afterEdge (by decide) base (e:=ea32) (by decide +kernel) ready32 (lower32 ha hb))
  · exact afterEdge (by decide) base (e:=ea34) (by decide +kernel) ready34 (lower34 ha hb)
  · exact afterEdge (by decide) base (e:=ea35) (by decide +kernel) ready35 (lower35 ha hb)
variable {R : ℕ → ℕ}
def mayStep (R : ℕ → ℕ) (M : List (ℕ × ℕ)) (m T k t : ℕ) (S : Finset ℕ) : Prop :=
  ∀ k₀ d a b S₁, k = k₀ + 1 → R a ≠ 0 → R b ≠ 0 → Bi Z0 d a b S S₁ → Live Z0 m T k₀ t S₁ →
    ∃ p ∈ M, hb p.1 (a+b) = true
section
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma oneRegions (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∀ k₀ d S₁, k' = k₀+1 → Bi Z0 d a.s c.s S S₁ → Live Z0 m T k₀ t S₁ → ∃ go : (L_meta_47789.X → L_meta_47789.X → Bool) → List L_meta_47789.X → Bool,
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
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb') k0 d S1 rfl hb hl1
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
lemma topRegions (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hphase : ∃ p ∈ M, Nat.beq p.2 1 = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) (cover : mayStep R M m T k' t S) : False := by
  obtain ⟨p0,hp0,hp1⟩ := hphase
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
  refine oneRegions X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr k₀ d S₁ hk₀ hbi htail
    obtain ⟨p,hpM,hpb⟩ := cover k₀ d a.s c.s S₁ hk₀ (by rwa [←hcod a ha]) (by rwa [←hcod c hc]) hbi htail
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : L_meta_47789.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_47789.X.s e)) hpb
end
noncomputable def markedChk (R : ℕ → ℕ) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc ((avl P m (rawL E)).map (fun w => {w with r := R w.s})) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
theorem markedRegions (R : ℕ → ℕ) (rr : RR R) (rr2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (rsub : ∀ x, R x ≠ 0 → x ∈ WZ E Z)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), ((∃ p ∈ M, Nat.beq p.2 1 = true) ∧ mayStep R M (mz Z) (tz Z) k t S) ∧ ∀ p ∈ M, markedChk R E Q Z (L - 1) t p.1 p.2 = false) : False := by
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
  let mark := fun w : W => {w with r := R w.s}
  set v := ((avl (PZ Q) (mz Z) (rawL E)).map mark).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist ((avl (PZ Q) (mz Z) (rawL E)).map mark) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    have sort : Srt ((avl (PZ Q) (mz Z) (rawL E)).map mark) := List.pairwise_map.mpr a1
    exact (sort.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨mark w', by rw [hv, List.mem_filter]; exact ⟨List.mem_map_of_mem hw', by simpa [mark,e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp (hsub.subset hw)
    obtain ⟨x, _, rfl⟩ := a2 w' hw'
    obtain ⟨pa,pb,ec,ca,cb⟩ := mkW_ok (PZ Q) (x &&& mz Z)
    exact ⟨pa,pb,ec,ca,cb⟩
  have hcod : ∀ w ∈ v, w.r = R w.s := by
    intro w hw
    obtain ⟨w', _, rfl⟩ := List.mem_map.mp (hsub.subset hw)
    rfl
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp (hsub.subset hw)
    obtain ⟨x, hx, rfl⟩ := a2 w' hw'; exact wire_good (rawL_sub hE6 hx) Z
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
    simp only [markedChk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topRegions X rr rr2 hMf.1 all hst hcod (by omega) hl ?_ hMf.2
  intro q hq hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl (rsub _ hx)
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
lemma swapBinary {e' : ℕ × ℕ} {t u v a b : ℕ} {firstOp laterOp : Bool} {S S₁ : Finset ℕ}
    (base : Imp [] 0 13) (he : okEdge e' 0 = true) (first : Excluded 12 e' t)
    (hu : u ∈ C (mz 0) (WZ [] 0)) (hv : v ∈ C (mz 0) (WZ [] 0)) (huv : u ≠ v)
    (hgate : op laterOp a b = exv e' 0)
    (hs : (S : Set ℕ) ⊆ insert (op firstOp u v) (C (mz 0) (WZ [] 0)))
    (bi : Bi Z0 laterOp a b S S₁)
    (tail : Live Z0 (mz 0) (tz 0) 11 t S₁) : False := by
  obtain ⟨_, U, rfl, rfl, _⟩ := bi
  have hsub : ((insert (op laterOp a b) U : Finset ℕ) : Set ℕ) ⊆
      insert (op firstOp u v) (C (mz 0) (WZ [e'] 0)) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · right; left; exact ⟨xw e', by simp [rawL], hgate⟩
    · rcases hs (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)) with h | h
      · exact Or.inl h
      · exact Or.inr (stock_extend e' h)
  let A := insert (op laterOp a b) U
  by_cases hp : op firstOp u v ∈ A
  · apply first (insert u (insert v (A.erase (op firstOp u v))))
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact stock_extend e' hu
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact stock_extend e' hv
      · exact (hsub (Finset.mem_erase.mp hz).2).resolve_left (Finset.mem_erase.mp hz).1
    · apply Live.bi (d := firstOp) huv (al0 _ _ _)
      rwa [Finset.insert_erase hp]
  · apply base 12 (by decide)
    apply prefixOne he
    exact tail.sol.mono le_rfl (fun z hz => (hsub hz).resolve_left (fun eq => hp (eq ▸ hz)))

lemma swapUnary {x e' t d a b} {S S₁ : Finset ℕ}
    (base : Imp [] 0 13) (he : okEdge e' 0 = true)
    (first : Excluded 12 e' (t+1))
    (hv : op d a b = exv e' 0)
    (hs : (S : Set ℕ) ⊆ insert (ip x 0 ^^^ mz 0) (C (mz 0) (WZ [] 0)))
    (bi : Bi Z0 d a b S S₁)
    (tail : Live Z0 (mz 0) (tz 0) 11 t S₁) : False := by
  obtain ⟨_, U, rfl, rfl, _⟩ := bi
  have hsub : ((insert (op d a b) U : Finset ℕ) : Set ℕ) ⊆
      insert (ip x 0 ^^^ mz 0) (C (mz 0) (WZ [e'] 0)) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · right; left; exact ⟨xw e', by simp [rawL], hv⟩
    · rcases hs (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)) with h | h
      · exact Or.inl h
      · exact Or.inr (stock_extend e' h)
  let A := insert (op d a b) U
  by_cases hp : ip x 0 ^^^ mz 0 ∈ A
  · apply first (insert (ip x 0) (A.erase (ip x 0 ^^^ mz 0)))
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | h
      · exact stock_extend e' (ip_mem _ _)
      · exact (hsub (Finset.mem_erase.mp h).2).resolve_left (Finset.mem_erase.mp h).1
    · apply Live.un
      rwa [Finset.insert_erase hp]
  · apply base 12 (by decide)
    apply prefixOne he
    exact tail.sol.mono le_rfl (fun z hz => (hsub hz).resolve_left (fun eq => hp (eq ▸ hz)))
def cliqueMark (inputs : List ℕ) (w : ℕ) : ℕ := if inputs.contains w then 3 else 0

def priorGate (prior : List (ℕ × ℕ)) (v : ℕ) : Bool :=
  prior.any fun p => okEdge p 0 && exv p 0 == v

def storedInput (e : ℕ × ℕ) (keep : Bool) :=
  if keep then (rawL [e]).map (fun x => x &&& mz 0) else rawP.map (fun x => x &&& mz 0)
def frontCover (inputs : List ℕ) (prior : List (ℕ × ℕ)) (M : List (ℕ × ℕ)) :=
  inputs.all fun a => inputs.all fun b => a == b || M.any (fun p => hb p.1 (a+b)) ||
    (priorGate prior (op true a b) && priorGate prior (op false a b))

def moveEarlier (e : ℕ × ℕ) (t : ℕ) (prior : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ prior, okEdge p 0 = true → ∀ {d a b} {S S₁ : Finset ℕ}, op d a b = exv p 0 →
    (S : Set ℕ) ⊆ C (mz 0) (WZ [e] 0) → Bi Z0 d a b S S₁ →
    Live Z0 (mz 0) (tz 0) 11 t S₁ → False
lemma binaryEarlier {e : ℕ × ℕ} {t x y : ℕ} {prior : List (ℕ × ℕ)} {op₁ : Bool}
    (base : Imp [] 0 13) (first : exv e 0 = op op₁ (ip x 0) (ip y 0))
    (ne : ip x 0 ≠ ip y 0) (previous : ∀ p ∈ prior, Excluded 12 p t) : moveEarlier e t prior := by
  intro p hp he d a b S S₁ eq hs bi tail
  apply swapBinary (firstOp:=op₁) base he (previous p hp) (ip_mem x 0) (ip_mem y 0) ne eq _ bi tail
  simpa only [←first] using hs.trans (extra_sub e 0)
lemma unaryEarlier {e : ℕ × ℕ} {t x : ℕ} {prior : List (ℕ × ℕ)}
    (base : Imp [] 0 13) (first : exv e 0 = ip x 0 ^^^ mz 0)
    (previous : ∀ p ∈ prior, Excluded 12 p (t+1)) : moveEarlier e t prior := by
  intro p hp he d a b S S₁ eq hs bi tail
  apply swapUnary (x:=x) base he (previous p hp) eq _ bi tail
  simpa only [←first] using hs.trans (extra_sub e 0)
lemma inputSubset (e : ℕ × ℕ) (flag : Bool) {w : ℕ} (hw : w ∈ storedInput e flag) :
    w ∈ WZ [e] 0 := by
  cases flag <;> simp only [storedInput,Bool.false_eq_true,if_false,if_true] at hw
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact ⟨a,by simp [rawL,ha],rfl⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact ⟨a,ha,rfl⟩
lemma useFront {e : ℕ × ℕ} {Q prior M : List (ℕ × ℕ)} {t : ℕ} {useExtra : Bool}
    (base : Imp [] 0 13) (he : e ∈ six)
    (prep : okEdge e 0 = true ∧ pOk 0 Q = true ∧ ∀ p ∈ Q, Imp [e] p.1 p.2)
    (move : moveEarlier e t prior)
    (phase : ∃ p ∈ M, Nat.beq p.2 1 = true)
    (covered : frontCover (storedInput e useExtra) prior M = true)
    (num : ∀ p ∈ M, markedChk (cliqueMark (storedInput e useExtra)) [e] Q 0 12 t p.1 p.2 = false) :
    Excluded 12 e t := by
  intro S hs hl
  let inputs := storedInput e useExtra
  have mem {w : ℕ} (h : cliqueMark inputs w ≠ 0) : w ∈ inputs := by simpa [cliqueMark] using h
  have rr : RR (cliqueMark inputs) := by
    intro d a b ha hb
    have h := mem ha
    have h' := mem hb
    cases d <;> simp [Al,cliqueMark,h,h']
  have rr2 : ∀ d a b, (cliqueMark inputs a = 0 ∨ cliqueMark inputs b = 0) → Al (cliqueMark inputs) d a b := by
    rintro d a b (h | h) <;> simp [Al,h]
  apply markedRegions (cliqueMark inputs) rr rr2 (E:=[e]) (Q:=Q) (L:=13)
    (Or.inr ⟨e,he,rfl,base⟩) prep.2.1 (by decide) prep.2.2 (by decide) hs hl
  · intro k hk sol
    exact base (k+1) (by omega) (prefixOne prep.1 sol)
  · intro w hw
    exact inputSubset e useExtra (mem hw)
  · refine Or.inr ⟨M,⟨phase,?_⟩,num⟩
    intro k₀ d a b S₁ hk ha hb bi tail
    obtain rfl : k₀ = 11 := by omega
    have h := List.all_eq_true.mp (List.all_eq_true.mp covered a (mem ha)) b (mem hb)
    simp only [beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (same | enough) | previous
    · exact False.elim (bi.1 same)
    · exact List.any_eq_true.mp enough
    · have gate : priorGate prior (op d a b) = true := by cases d <;> tauto
      obtain ⟨p,hp,hit⟩ := List.any_eq_true.mp gate
      simp only [Bool.and_eq_true,beq_iff_eq] at hit
      exact False.elim (move p hp hit.1 hit.2.symm hs bi tail)
noncomputable def markedBudgetWith (R : ℕ → ℕ) (cb : Nat → Nat → Nat → Nat → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc ((avl P m (rawL E)).map (fun w => {w with r := R w.s})) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => budgetStart cb l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma markedDeepRootJoin (R : ℕ → ℕ) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (cache : List DeepState)
    (ok : ∀ c ∈ cache, deepEval (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K c = false)
    (checked : markedBudgetWith R (fun mode => deepMemo (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K cache mode K)
      E Q Z K t H ph = false) : markedChk R E Q Z K t H ph = false := by
  rw [deepMemo_eq _ _ _ _ _ ok] at checked
  unfold markedBudgetWith at checked
  unfold markedChk
  simp only [frc_eq,st_eq,deepFn] at checked ⊢
  exact checked

noncomputable def stepInside (Q : List (ℕ × ℕ)) (xs : List DeepState) (w : DeepState) :=
  deepOuter (lz 0) (mz 0) (pL (Q.map fun _ => 16)) 12 xs w
noncomputable def atFront (R : ℕ → ℕ) (e : ℕ × ℕ) (Q : List (ℕ × ℕ))
    (t h ph : ℕ) (xs : List DeepState) :=
  markedBudgetWith R (fun mode => deepMemo (lz 0) (mz 0) (pL (Q.map fun _ => 16)) 12 xs mode 12)
    [e] Q 0 12 t h ph
lemma proveFront {R : ℕ → ℕ} {e : ℕ × ℕ} {Q : List (ℕ × ℕ)} {t h ph : ℕ} {xs : List DeepState}
    (hi : deepPass Q 12 xs = true) (ho : atFront R e Q t h ph xs = false) :
    markedChk R [e] Q 0 12 t h ph = false :=
  markedDeepRootJoin _ _ _ _ _ _ _ _ _ (fun c hc => by
    simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp hi) c hc) ho
lemma proveInside {Q : List (ℕ × ℕ)} {xs : List DeepState} {w : DeepState}
    (hi : deepPass Q 12 xs = true) (ho : stepInside Q xs w = false) : deepPass Q 12 [w] = true := by
  have h := deepJoin (lz 0) (mz 0) (pL (Q.map fun _ => 16)) 12 xs w
    (fun c hc => by simpa only [Bool.not_eq_true'] using (List.all_eq_true.mp hi) c hc) ho
  change ((!deepEval (lz 0) (mz 0) (pL (Q.map fun _ => 16)) 12 w) && true) = true
  rw [h]
  rfl
def wireSignal0 : ℕ := (sig71 ||| sig116)
def wireSignal1 : ℕ := (sig37 ||| sig59)
def wireSignal2 : ℕ := (sig93 &&& sig115)
def wireSignal3 : ℕ := (sig113 &&& sig122)
def wireSignal4 : ℕ := (sig109 ||| sig122)
def wireSignal5 : ℕ := (sig122 &&& sig126)
def wireSignal6 : ℕ := (sig107 &&& sig122)
def wireSignal7 : ℕ := (sig118 &&& sig119)
def wireSignal8 : ℕ := (sig109 &&& sig125)
def wireSignal9 : ℕ := (sig126 &&& sig129)
def wireSignal10 : ℕ := (sig126 &&& sig127)
def wireSignal11 : ℕ := (sig126 &&& sig133)
def wireSignal12 : ℕ := (sig36 ||| sig41)
def wireSignal13 : ℕ := (sig93 &&& sig102)
def wireSignal14 : ℕ := (sig63 ||| sig73)
def wireSignal15 : ℕ := (sig107 &&& sig125)
def wireSignal16 : ℕ := (sig107 ||| sig125)
def wireSignal17 : ℕ := (sig107 &&& sig127)
def wireSignal18 : ℕ := (sig114 &&& sig130)
def wireSignal19 : ℕ := (sig106 ||| sig125)
def wireSignal20 : ℕ := (sig106 ||| sig127)
def wireSignal21 : ℕ := (bigNat_4 ||| sig120)
def wireSignal22 : ℕ := (sig106 ||| sig107)
def wireSignal23 : ℕ := (sig108 &&& sig114)
def wireSignal24 : ℕ := (sig114 &&& sig134)
def wireSignal25 : ℕ := (sig127 &&& sig133)
def wireSignal26 : ℕ := (bigNat_4 ||| sig133)
def wireSignal27 : ℕ := (sig43 &&& sig130)
def wireSignal28 : ℕ := (sig40 &&& sig121)
def wireSignal29 : ℕ := (sig16 ||| sig51)
def wireSignal30 : ℕ := (sig108 &&& sig121)
def wireSignal31 : ℕ := (sig101 &&& sig121)
def wireSignal32 : ℕ := (sig100 ||| sig122)
def wireSignal33 : ℕ := (sig107 ||| sig122)
def wireSignal34 : ℕ := (sig103 ||| sig122)
def wireSignal35 : ℕ := (bigNat_5 ||| sig120)
def wireSignal36 : ℕ := (sig121 &&& sig135)
def wireSignal37 : ℕ := (sig103 &&& sig133)
def wireSignal38 : ℕ := (bigNat_5 ||| sig133)
def wireSignal39 : ℕ := (sig93 &&& sig104)
def wireSignal40 : ℕ := (sig33 ||| sig40)
def wireSignal41 : ℕ := (sig110 &&& sig130)
def wireSignal42 : ℕ := (sig109 ||| sig125)
def wireSignal43 : ℕ := (sig79 &&& sig116)
def wireSignal44 : ℕ := (sig109 ||| sig129)
def wireSignal45 : ℕ := (bigNat_6 ||| sig120)
def wireSignal46 : ℕ := (sig101 &&& sig110)
def wireSignal47 : ℕ := (bigNat_6 ||| sig126)
def wireSignal48 : ℕ := (sig129 &&& sig133)
def wireSignal49 : ℕ := (bigNat_6 ||| sig133)
def wireSignal50 : ℕ := (sig55 ||| sig56)
def wireSignal51 : ℕ := (sig94 &&& sig133)
def wireSignal52 : ℕ := (sig95 &&& sig133)
def wireSignal53 : ℕ := (sig135 &&& sig136)
def wireSignal54 : ℕ := (sig118 &&& sig134)
def wireSignal55 : ℕ := (sig134 &&& sig135)
def wireSignal56 : ℕ := (sig118 &&& sig136)
def wireSignal57 : ℕ := (sig126 ||| sig129)
def wireSignal58 : ℕ := (sig126 ||| sig127)
def wireSignal59 : ℕ := (sig103 ||| sig126)
def wireSignal60 : ℕ := (sig75 ||| sig117)
def wireSignal61 : ℕ := (sig118 &&& sig135)
def wireSignal62 : ℕ := (sig48 ||| sig49)
def wireSignal63 : ℕ := (sig49 ||| sig72)
def wireSignal64 : ℕ := (sig45 &&& sig100)
def wireSignal65 : ℕ := (bigNat_8 &&& sig101)
def wireSignal66 : ℕ := (bigNat_8 ||| sig103)
def wireSignal67 : ℕ := (bigNat_8 ||| sig106)
def wireSignal68 : ℕ := (bigNat_8 ||| sig107)
def wireSignal69 : ℕ := (sig119 &&& sig137)
def wireSignal70 : ℕ := (bigNat_8 &&& sig110)
def wireSignal71 : ℕ := (bigNat_8 &&& sig114)
def wireSignal72 : ℕ := (bigNat_8 &&& sig121)
def wireSignal73 : ℕ := (bigNat_8 ||| sig122)
def wireSignal74 : ℕ := (bigNat_8 ||| sig126)
def wireSignal75 : ℕ := (sig3 ||| sig106)
def wireSignal76 : ℕ := (sig11 &&& sig24)
def wireSignal77 : ℕ := (sig37 ||| sig55)
def wireSignal78 : ℕ := (sig26 &&& sig31)
def wireSignal79 : ℕ := (sig35 ||| sig37)
def wireSignal80 : ℕ := (sig11 &&& sig31)
def wireSignal81 : ℕ := (sig9 &&& sig27)
def wireSignal82 : ℕ := (sig9 &&& sig25)
def wireSignal83 : ℕ := (sig39 ||| sig59)
def wireSignal84 : ℕ := (sig56 ||| sig59)
def wireSignal85 : ℕ := (sig9 &&& sig12)
def wireSignal86 : ℕ := (sig12 &&& sig45)
def wireSignal87 : ℕ := (sig42 &&& sig58)
def wireSignal88 : ℕ := (sig42 &&& sig53)
def wireSignal89 : ℕ := (sig58 &&& sig62)
def wireSignal90 : ℕ := (sig14 ||| sig61)
def wireSignal91 : ℕ := (sig46 &&& sig53)
def wireSignal92 : ℕ := (sig38 &&& sig60)
def wireSignal93 : ℕ := (sig54 &&& sig60)
def wireSignal94 : ℕ := (sig47 &&& sig54)
def wireSignal95 : ℕ := (sig52 &&& sig66)
def wireSignal96 : ℕ := (sig66 &&& sig68)
def wireSignal97 : ℕ := (sig33 ||| sig83)
def wireSignal98 : ℕ := (sig33 ||| sig76)
def wireSignal99 : ℕ := (sig51 ||| sig71)
def wireSignal100 : ℕ := (sig73 ||| sig77)
def wireSignal101 : ℕ := (sig78 ||| sig83)
def wireSignal102 : ℕ := (sig103 ||| sig106)
def wireSignal103 : ℕ := (sig103 ||| sig133)
def wireSignal104 : ℕ := (sig107 ||| sig109)
def wireSignal105 : ℕ := (sig120 ||| sig122)
def wireSignal106 : ℕ := (sig81 &&& wireSignal68)
def spacedBits (word : ℕ) : ℕ :=
  let stage32 := (word ||| (word <<< 128)) &&& 0xffffffff00000000000000000000000000000000ffffffff
  let stage16 := (stage32 ||| (stage32 <<< 64)) &&& 0xffff0000000000000000ffff0000000000000000ffff0000000000000000ffff
  let stage8 := (stage16 ||| (stage16 <<< 32)) &&& 0xff00000000ff00000000ff00000000ff00000000ff00000000ff00000000ff00000000ff
  let stage4 := (stage8 ||| (stage8 <<< 16)) &&& 0xf0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f0000f
  let stage2 := (stage4 ||| (stage4 <<< 8)) &&& 0xc0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c03
  let stage1 := (stage2 ||| (stage2 <<< 4)) &&& 0x8421084210842108421084210842108421084210842108421084210842108421084210842108421
  stage1
def flagsWire (w a b r : ℕ) := wireEntry w (spacedBits a) (spacedBits b) r
def frontierWires : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
flagsWire bigNat_8 306475040 0x1ff800000800 3,
flagsWire sig17 0 0x4925091009 0,
flagsWire bigNat_7 0x8000224010 0x1007e0000400 3,
flagsWire bigNat_6 0x4101010008 0x8001c000200 3,
flagsWire bigNat_5 0x2088100004 0x40003800100 3,
flagsWire bigNat_4 69801648130 0x20400780080 3,
flagsWire bigNat_3 0x824081001 0x10200078040 3,
flagsWire sig15 0x10200078040 0x824081001 3,
flagsWire sig3 0x8001c000200 0x4101010008 0,
flagsWire sig118 0 0x1107e0078440 0,
flagsWire bigNat_3 0x824081001 0x10200078040 0,
flagsWire sig24 0x8000000 0x44103810108 0,
flagsWire sig25 16777216 0x8209c100204 0,
flagsWire sig2 0 0x24501790088 0,
flagsWire sig26 67108864 0x14301078048 0,
flagsWire sig109 0x4925091009 0 0,
flagsWire sig27 8388608 0x22488780084 0,
flagsWire sig8 0x40003800100 0x2088100004 0,
flagsWire sig9 0 0x12288178044 0,
flagsWire sig30 0 0x28ac181005 0,
flagsWire sig122 0x28ac181005 0 0,
flagsWire sig23 0x306007f80c0 0 0,
flagsWire sig114 0 0x306007f80c0 0,
flagsWire sig45 33554432 0x1ff888100804 0,
flagsWire sig119 4096 0x1ffa00078840 0,
flagsWire sig11 0 0x1047e1010408 0,
flagsWire sig12 0 0x1027e8100404 0,
flagsWire sig68 536870912 0x1820027c050 0,
flagsWire sig32 0x1007e0000400 0x8000224010 0,
flagsWire sig95 8589934592 0x88242a5011 0,
flagsWire sig49 0x40013c47120 0x2000000000 0,
flagsWire sig120 0x8364c7021 0x10000000000 0,
flagsWire sig13 0x20400780080 69801648130 0,
flagsWire sig57 0x284007a4090 0x40000000 0,
flagsWire sig126 0x88242a5011 8589934592 0,
flagsWire sig35 0x8209c100204 16777216 0,
flagsWire sig36 0x8105c80a202 0 0,
flagsWire sig19 0x9021c078240 0 0,
flagsWire sig37 0x8083c081201 65536 0,
flagsWire sig110 0 0x9021c078240 0,
flagsWire sig39 0x44103810108 0x8000000 0,
flagsWire sig14 0x24501790088 0 0,
flagsWire sig41 0x4104380a102 1048576 0,
flagsWire sig44 0x50203878140 0 0,
flagsWire sig59 0x40827881101 0 0,
flagsWire sig42 1048576 0x4104380a102 0,
flagsWire sig121 0 0x50203878140 0,
flagsWire sig43 0x22488780084 8388608 0,
flagsWire sig61 0x20c24781081 32768 0,
flagsWire sig7 0 0x618911000c 0,
flagsWire sig8 0x40003800100 0x2088100004 3,
flagsWire bigNat_5 0x2088100004 0x40003800100 0,
flagsWire sig100 0x618911000c 0 0,
flagsWire sig107 0x30c890a006 0 0,
flagsWire sig103 0xa088324014 0 0,
flagsWire sig21 0xc001f800300 0 0,
flagsWire sig101 0 0xc001f800300 0,
flagsWire sig22 0x60403f80180 0 0,
flagsWire sig18 0 0x30c890a006 0,
flagsWire sig15 0x10200078040 0x824081001 0,
flagsWire sig16 0x12288178044 0 0,
flagsWire sig31 268435456 0x1ff901010808 0,
flagsWire wireSignal0 0 0x1ff803800900 0,
flagsWire sig46 4194304 0x1ff84080a802 0,
flagsWire sig47 262144 0x1ff824081801 0,
flagsWire sig135 0 0x1407e3800500 0,
flagsWire sig93 0 0xa088324014 0,
flagsWire sig67 0x40000000 0x284007a4090 0,
flagsWire sig53 2097152 0x1017e080a402 0,
flagsWire sig54 131072 0x100fe4081401 0,
flagsWire sig48 0x8001e447220 0x4000000000 0,
flagsWire sig55 0x8801c224210 4294967296 0,
flagsWire sig34 0x1820027c050 536870912 0,
flagsWire sig58 0 0x8105c80a202 0,
flagsWire sig40 0x14301078048 67108864 0,
flagsWire sig108 0 0x60403f80180 0,
flagsWire sig63 0x1124087a042 524288 0,
flagsWire sig110 0 0x29021c078240 0,
flagsWire wireSignal32 0x2088100004 0 0,
flagsWire wireSignal57 0x8000224010 8589934592 0,
flagsWire wireSignal19 69801648130 0 0,
flagsWire wireSignal70 306475040 0x90000000000 0,
flagsWire sig51 0x1027e8100404 0 0,
flagsWire sig56 0x48003a24110 0x80000000 0,
flagsWire sig109 0x204925091009 0 0,
flagsWire wireSignal104 0 0 0,
flagsWire sig129 0xc101234018 0 0,
flagsWire wireSignal56 0 0x1007e0000400 0,
flagsWire wireSignal69 4096 0x1ff800000800 0,
flagsWire wireSignal55 0 0x1007e0000400 0,
flagsWire wireSignal68 8192 0x1ff800000800 0,
flagsWire wireSignal17 0xb0c8b2e016 0 0,
flagsWire wireSignal18 0 0x20400780080 0,
flagsWire wireSignal31 0 0x40003800100 0,
flagsWire wireSignal82 16777216 0x2088100004 0,
flagsWire sig66 4294967296 0x8801c224210 0,
flagsWire sig52 0x80000000 0x48003a24110 0,
flagsWire wireSignal89 524288 69801648130 0,
flagsWire sig33 0x1047e1010408 0 0,
flagsWire sig113 0x4101010008 0 0,
flagsWire wireSignal22 69801648130 0 0,
flagsWire wireSignal59 0x8000224010 8589934592 0,
flagsWire wireSignal72 306475040 0x50000000000 0,
flagsWire sig121 0 0x250203878140 0,
flagsWire wireSignal79 0x8001c000200 16842752 0,
flagsWire wireSignal46 0 0x8001c000200 0,
flagsWire wireSignal23 0 0x20400780080 0,
flagsWire wireSignal61 0 0x1007e0000400 0,
flagsWire wireSignal73 4096 0x1ff800000800 0,
flagsWire sig9 0 0x2088100004 0,
flagsWire sig122 0x2028ac181005 0 0,
flagsWire sig106 0x186488b003 0 0,
flagsWire wireSignal102 0 0 0,
flagsWire wireSignal54 0 0x1007e0000400 0,
flagsWire wireSignal41 0 0x8001c000200 0,
flagsWire sig104 0 0x8001c000200 0,
flagsWire sig105 0xe18933401c 0 0,
flagsWire wireSignal8 0x596589b00b 0 0,
flagsWire sig130 0 0xa041c780280 0,
flagsWire wireSignal6 0x38ec98b007 0 0,
flagsWire sig115 0 0x10200078040 0,
flagsWire sig102 0 0x20400780080 0,
flagsWire wireSignal5 0xa8ac3a5015 0 0,
flagsWire wireSignal37 0xa09a767034 0 0,
flagsWire sig38 65536 0x8083c081201 0,
flagsWire wireSignal76 0x8000000 0x4101010008 0,
flagsWire sig60 0 0x40827881101 0,
flagsWire sig69 32768 0x20c24781081 0,
flagsWire wireSignal39 0x4101010008 0x8000000 0,
flagsWire sig51 0x2088100004 0 0,
flagsWire sig62 524288 0x1124087a042 0,
flagsWire wireSignal66 16384 0x1ff800000800 0,
flagsWire wireSignal2 0x824081001 131072 0,
flagsWire wireSignal13 69801648130 3145728 0,
flagsWire sig12 0 0x2088100004 0,
flagsWire wireSignal44 0x4101010008 0 0,
flagsWire wireSignal20 69801648130 0x400000000 0,
flagsWire wireSignal34 0x2088100004 0 0,
flagsWire sig117 306475040 0x110000000000 0,
flagsWire sig118 0 0x3107e0078440 0,
flagsWire wireSignal36 0 0x40203800100 0,
flagsWire wireSignal24 0 0x20600780080 0,
flagsWire wireSignal47 0 0x8021c000200 0,
flagsWire wireSignal9 0x20c9252b5019 0 0,
flagsWire sig126 0x2088242a5011 8589934592 0,
flagsWire wireSignal11 0x2088366e7031 0 0,
flagsWire wireSignal10 0x209864aaf013 0 0,
flagsWire wireSignal29 0x2288100004 0 0,
flagsWire wireSignal5 0x20a8ac3a5015 0 0,
flagsWire wireSignal85 0 0x2288100004 0,
flagsWire wireSignal74 20480 0x1ffa00000800 0,
flagsWire wireSignal40 0x4301010008 67108864 0,
flagsWire wireSignal14 78391582722 2621440 0,
flagsWire wireSignal43 0x4101010008 0x80000000000 0,
flagsWire wireSignal106 69801648130 0x20000000000 0,
flagsWire wireSignal103 0x8000224010 0x100000000000 0,
flagsWire wireSignal105 0x824081001 0x10000000000 0,
flagsWire wireSignal0 0 0x3ff803800900 0,
flagsWire wireSignal35 0 0x50003800100 0,
flagsWire wireSignal45 0 0x9001c000200 0,
flagsWire wireSignal21 8192 0x30400780080 0,
flagsWire wireSignal60 16384 0x1107e0000400 0,
flagsWire sig120 0x2008364c7021 0x10000000000 0,
flagsWire wireSignal78 335544320 0x14101010008 0,
flagsWire wireSignal33 0x2088100004 0 0,
flagsWire wireSignal42 0x4101010008 0 0,
flagsWire wireSignal58 0x8000224010 0x600000000 0,
flagsWire wireSignal71 306475040 0x30000000000 0,
flagsWire sig114 0 0x2306007f80c0 0,
flagsWire wireSignal30 0 0x40003800100 0,
flagsWire wireSignal67 12288 0x1ff800000800 0,
flagsWire sig106 0x20186488b003 0 0,
flagsWire wireSignal75 67108864 0x4101010008 0,
flagsWire wireSignal81 8388608 0x2088100004 0,
flagsWire sig99 0x8000224010 0 0,
flagsWire wireSignal16 69801648130 0 0,
flagsWire wireSignal4 0x824081001 0 0,
flagsWire wireSignal65 306475040 0xc0000000000 0,
flagsWire sig101 0 0x2c001f800300 0,
flagsWire sig100 0x20618911000c 0 0,
flagsWire sig111 0 0x20400780080 0,
flagsWire sig112 0 0x10200078040 0,
flagsWire sig116 0 0x1ff800000800 0,
flagsWire sig105 0x20e18933401c 0 0,
flagsWire wireSignal53 0 0x1007e0000400 0,
flagsWire wireSignal3 0x2069ad19100d 0 0,
flagsWire wireSignal15 0x2071c991a00e 0 0,
flagsWire wireSignal12 69801648130 1048576 0,
flagsWire wireSignal1 0x824081001 65536 0,
flagsWire wireSignal64 0x20619b55702c 0 0,
flagsWire wireSignal50 0x8000224010 6442450944 0,
flagsWire sig35 0x2088100004 16777216 0,
flagsWire sig39 0x4101010008 0x8000000 0,
flagsWire sig64 0 0x1ff800224810 0,
flagsWire wireSignal95 6442450944 0x8000224010 0,
flagsWire wireSignal62 306475040 0x6000000000 0,
flagsWire wireSignal38 0 0x140003800100 0,
flagsWire wireSignal49 0 0x18001c000200 0,
flagsWire wireSignal26 8192 0x120400780080 0,
flagsWire wireSignal7 4096 0x110200078040 0,
flagsWire wireSignal25 0x209052e6f032 0 0,
flagsWire wireSignal48 0x20c113677038 0 0,
flagsWire wireSignal37 0x20a09a767034 0 0,
flagsWire sig133 0x208012667030 0x100000000000 0,
flagsWire wireSignal80 268435456 0x104101010008 0,
flagsWire wireSignal86 33554432 0x102088100004 0,
flagsWire wireSignal90 0x20400780080 32768 0,
flagsWire wireSignal83 0x40003800100 0x8000000 0,
flagsWire wireSignal97 0x1007e0000400 131072 0,
flagsWire wireSignal96 4831838208 0x8000224010 0,
flagsWire sig26 67108864 0x4101010008 0,
flagsWire wireSignal84 0x40003800100 0x80000000 0,
flagsWire wireSignal77 0x8001c000200 4295032832 0,
flagsWire wireSignal88 3145728 69801648130 0,
flagsWire wireSignal93 131072 0x824081001 0,
flagsWire wireSignal63 306475040 0xa000000000 0,
flagsWire sig52 0x80000000 0x8000224010 0,
flagsWire sig56 0x8000224010 0x80000000 0,
flagsWire wireSignal92 65536 0x824081001 0,
flagsWire wireSignal87 1048576 69801648130 0,
flagsWire sig24 0x8000000 0x4101010008 0,
flagsWire sig25 16777216 0x2088100004 0,
flagsWire wireSignal27 0x22658979008c 0 0,
flagsWire wireSignal28 0x21638917804c 0 0,
flagsWire wireSignal91 6291456 0x10104080a002 0,
flagsWire wireSignal94 393216 0x100824081001 0,
flagsWire wireSignal100 0x10104080a002 6291456 0,
flagsWire wireSignal101 0x100824081001 393216 0,
flagsWire wireSignal98 0x104101010008 268435456 0,
flagsWire wireSignal99 0x102088100004 33554432 0,
flagsWire sig75 0x108000224010 0 0,
flagsWire wireSignal51 0x2284127e70b0 0 0,
flagsWire wireSignal52 0x21821267f070 0 0,
flagsWire sig64 0 0x108000224010 0,
flagsWire sig65 0x1021247f060 0x800000000 0,
flagsWire sig72 0x1007f2447420 0x8000000000 0,
flagsWire sig73 0x1017e080a402 2097152 0,
flagsWire sig83 0x100fe4081401 131072 0]
def spentColumns : List (ℕ × ℕ) := [
(0x634cbf8a186,0x0),
(0x2d229f978344,0x0),
(0x3987fc27c650,0x0),
(0x2b165cffa2c2,0x0),
(0x3ffa1e47fa60,0x0),
(0x108760224410,0x4208b900104),
(0x8411d010208,0x21440f8a082),
(0x2144068a082,0x4208b900104),
(0x1086e0224410,0x8411d010208),
(0x21440f8a082,0x8411d010208),
(0x10a240f9041,0x4208b900104),
(0x4208b000104,0x21440f8a082),
(0x4200b900104,0x1087e0224410),
(0x42082900104,0x8411d010208),
(0x84114010208,0x4208b900104),
(0x264d26611189,0x30c998a006),
(0xf7ff6f733cf,0x9088000),
(0x1ef336dbe79e,0x4c9200000),
(0xa555469a28a,0x4208b900104),
(0x36fb2ed3f59f,0x4c1280000),
(0x39cdfcb5d9af,0x63003482000),
(0x17bb2fd775d7,0x4c0288000),
(0x1293204ae492,0x424cbb00104),
(0x0,0x634cbf8a186),
(0x1683234a4590,0x34c8b0a006),
(0x19cc112c59a0,0x630cad0a006),
(0x225d65f9b08b,0x0),
(0x2469af99110d,0x0),
(0x30cfe52b5419,0x0),
(0x3ff9374d7829,0x0),
(0x204924091009,0x4208b900104),
(0x21000d8a082,0x1087e0224410),
(0x8401d010208,0x1087e0224410),
(0x204925011009,0x21440f8a082),
(0x1083a0024410,0x21440f8a082),
(0x108040d9041,0x1087e0224410),
(0x2d431f878348,0x0),
(0x271643ffa1c2,0x0),
(0x3587e3a7c550,0x0),
(0x3ffa13c7f960,0x0),
(0x10a24071041,0x21440f8a082),
(0x17b802447820,0x8411d010208),
(0x10a200e9041,0x8411d010208),
(0x250202868140,0x8411d010208),
(0x2869bd19120d,0x0),
(0x223cecf8b087,0x0),
(0x30afec3a5415,0x0),
(0x3ff8be5c7825,0x0),
(0x200824081001,0x4208b900104),
(0x1085c0204410,0x10a240f9041),
(0x3a6884540d4,0x1864bab003),
(0x1bd999dcf6db,0x664230000),
(0x1381805544d0,0x1e64aab003),
(0xb47197602c8,0x186489b003),
(0xbfff9ccf2df,0x4330000),
(0xf7ffb6eb3cf,0x4910000),
(0x52aaf071145,0x21440f8a082),
(0xa5559f0228a,0x10a240f9041),
(0x0,0x31e64ffb0c3),
(0x94b39061249,0x21444f9a082),
(0x7268b6701c4,0x186498b003),
(0x1aaac055055,0x21440faa082),
(0x31e64ffb0c3,0x0),
(0x1aaac3fd055,0x0),
(0x2b4c8fae096,0x0),
(0x8e19d33421c,0x0),
(0x1ff89a767834,0x0),
(0x84119000208,0x10a240f9041),
(0xa080324014,0x8411d010208),
(0x4208b900104,0x10a240f9041),
(0x21440f02082,0x10a240f9041),
(0x84115010208,0xa088324014),
(0x40003800100,0xa088324014),
(0x10a240d9041,0xa088324014),
(0x21440c8a082,0xa088324014),
(0x8000224010,0x4208b900104),
(0x1de812045820,0x21440f8a082),
(0x1ef012406820,0x10a240f9041),
(0x3947fd078648,0x0),
(0x3317e0ffa4c2,0x0),
(0x3527eb978544,0x0),
(0x3ffff247fc60,0x0),
(0x24aaafba5115,0x0),
(0x229e64faf093,0x0),
(0x28cb3d2b5219,0x0),
(0x3ffa366e7831,0x0),
(0x4208b900104,0x208a242a5011),
(0x208a242a5011,0x4208b900104),
(0x84119010208,0x208a242a5011),
(0x21440d0a082,0x208a242a5011),
(0x3ff91f810b08,0x0),
(0x3ffc43f8a982,0x0),
(0x3fffe3a24d10,0x0),
(0x3ffa278f9941,0x0),
(0x2528bfdc7125,0x0),
(0x29493f4d7229,0x0),
(0x231c76fcf0a3,0x0),
(0x318ff66e7431,0x0),
(0x2108224c7021,0x8411d010208),
(0x27268bff81c4,0x0),
(0x2b471d7f82c8,0x0),
(0x3387e07fc4d0,0x0),
(0x3ffe127ff8e0,0x0),
(0x28597d89b20b,0x0),
(0x2438ef98b107,0x0),
(0x309fe4aaf413,0x0),
(0x3ff876ccf823,0x0),
(0x20186088b003,0x8411d010208),
(0x20186408b003,0x4208b900104),
(0x3c87ffa24710,0x0),
(0x2e145ff8a382,0x0),
(0x2d0a3f8f9341,0x0),
(0x3ff81fc47b20,0x0),
(0x10e66033441c,0xc019f800300),
(0x2e145668a382,0x618991000c),
(0x2d0a328e9341,0x618d11000c),
(0x275c069a08e,0xc001f900300),
(0x16ba01e904d,0xc001f810300),
(0x18c674234618,0x4218b900104),
(0x339804c47b20,0xc619b11000c),
(0x1dee7bbed75d,0x184010000),
(0xc619f91030c,0x0),
(0x216bad1f904d,0x0),
(0x2275c9f9a08e,0x0),
(0x3ff99b55782c,0x0),
(0x30e7e933441c,0x0),
(0x21440e8a082,0x20618911000c),
(0x10a240e9041,0x20618911000c),
(0x108660224410,0x20618911000c),
(0x40002800100,0x20618911000c),
(0x80014000200,0x20618911000c),
(0xf7812443820,0x1087e0224410),
(0x20600911000c,0x1087e0224410),
(0x1f9812447820,0x20618911000c),
(0x1bd810447820,0x4208b900104),
(0x34a09bf67134,0x0),
(0x38c11f677238,0x0),
(0x329452fef0b2,0x0),
(0x318a366ff071,0x0),
(0x308002667030,0x8411d010208),
(0x308010667030,0x4208b900104),
(0x52aaf9f9145,0x0),
(0x94b3d0f9249,0x0),
(0x118fe42fd451,0x0),
(0x14a7ebb24514,0x0),
(0x29021c070240,0x21440f8a082),
(0x290214078240,0x4208b900104),
(0x29001c058240,0x1087e0224410),
(0x204805091009,0x1087e0224410),
(0x200820081001,0x8411d010208),
(0x310760078440,0x4208b900104),
(0x3106e0068440,0x8411d010208),
(0xa088024014,0x21440f8a082),
(0xa088304014,0x10a240f9041),
(0x1f5812443820,0xa088324014),
(0x2008100004,0x1087e0224410),
(0x100760000400,0xa088324014),
(0x20618910000c,0x10a240f9041),
(0x20618901000c,0x21440f8a082),
(0x202080100004,0x8411d010208),
(0x204100010008,0x4208b900104),
(0x308012065030,0x21440f8a082),
(0x308012606030,0x10a240f9041),
(0x21440988082,0x308012667030),
(0x10a24098041,0x308012667030),
(0x8410d010208,0x308012667030),
(0x42089900104,0x308012667030),
(0x7e0000400,0x308012667030),
(0x200012443020,0x1087e0224410),
(0x1ffa364ff861,0x0),
(0x1ff89bd47924,0x0),
(0x1297e0fae492,0x0),
(0x18c7fd234618,0x0),
(0x1ffff2667c30,0x0)]
def stateWord (Q : List (ℕ × ℕ)) (word : ℕ) : DeepState :=
  let ws := (List.range ((word >>> 20) &&& 15)).map fun j => frontierWires.getD
    ((word >>> (24 + 8*j)) &&& 255) (0,0,0,0,0)
  let d := spentColumns.getD ((word >>> 11) &&& 511) (0,0)
  let used := spacedBits d.1 + 2 * spacedBits d.2
  let sum := ws.foldl (fun v w => v+w.2.2.2.1) 0
  let z := pL (Q.map fun e => 16+(12-e.2)) - used - sum
  (word &&& 1,(word >>> 1) &&& 15,(word >>> 5) &&& 15,(word >>> 9) &&& 3,z,ws)
def stateBlock (Q : List (ℕ × ℕ)) (n words : ℕ) :=
  (List.range n).map fun i => stateWord Q ((words >>> (104*i)) &&& 0xffffffffffffffffffffffffff)
lemma shape0 : exv ea0 0 = op true (ip 0 0) (ip 1 0) := by decide +kernel
lemma unequal0 : ip 0 0 ≠ ip 1 0 := by decide +kernel
lemma member0 : ea0 ∈ six := by decide +kernel
lemma shape1 : exv ea1 0 = op true (ip 0 0) (ip 2 0) := by decide +kernel
lemma unequal1 : ip 0 0 ≠ ip 2 0 := by decide +kernel
lemma member1 : ea1 ∈ six := by decide +kernel
lemma shape2 : exv ea2 0 = op true (ip 0 0) (ip 3 0) := by decide +kernel
lemma unequal2 : ip 0 0 ≠ ip 3 0 := by decide +kernel
lemma member2 : ea2 ∈ six := by decide +kernel
lemma shape3 : exv ea3 0 = op true (ip 0 0) (ip 4 0) := by decide +kernel
lemma unequal3 : ip 0 0 ≠ ip 4 0 := by decide +kernel
lemma member3 : ea3 ∈ six := by decide +kernel
lemma shape4 : exv ea4 0 = op true (ip 0 0) (ip 5 0) := by decide +kernel
lemma unequal4 : ip 0 0 ≠ ip 5 0 := by decide +kernel
lemma member4 : ea4 ∈ six := by decide +kernel
lemma shape9 : exv ea9 0 = op true (ip 2 0) (ip 3 0) := by decide +kernel
lemma unequal9 : ip 2 0 ≠ ip 3 0 := by decide +kernel
lemma member9 : ea9 ∈ six := by decide +kernel
lemma shape10 : exv ea10 0 = op true (ip 2 0) (ip 4 0) := by decide +kernel
lemma unequal10 : ip 2 0 ≠ ip 4 0 := by decide +kernel
lemma member10 : ea10 ∈ six := by decide +kernel
lemma shape11 : exv ea11 0 = op true (ip 2 0) (ip 5 0) := by decide +kernel
lemma unequal11 : ip 2 0 ≠ ip 5 0 := by decide +kernel
lemma member11 : ea11 ∈ six := by decide +kernel
lemma shape14 : exv ea14 0 = op true (ip 4 0) (ip 5 0) := by decide +kernel
lemma unequal14 : ip 4 0 ≠ ip 5 0 := by decide +kernel
lemma member14 : ea14 ∈ six := by decide +kernel
lemma shape15 : exv ea15 0 = op false (ip 0 0) (ip 1 0) := by decide +kernel
lemma unequal15 : ip 0 0 ≠ ip 1 0 := by decide +kernel
lemma member15 : ea15 ∈ six := by decide +kernel
lemma shape16 : exv ea16 0 = op false (ip 0 0) (ip 2 0) := by decide +kernel
lemma unequal16 : ip 0 0 ≠ ip 2 0 := by decide +kernel
lemma member16 : ea16 ∈ six := by decide +kernel
lemma shape17 : exv ea17 0 = op false (ip 0 0) (ip 3 0) := by decide +kernel
lemma unequal17 : ip 0 0 ≠ ip 3 0 := by decide +kernel
lemma member17 : ea17 ∈ six := by decide +kernel
lemma shape18 : exv ea18 0 = op false (ip 0 0) (ip 4 0) := by decide +kernel
lemma unequal18 : ip 0 0 ≠ ip 4 0 := by decide +kernel
lemma member18 : ea18 ∈ six := by decide +kernel
lemma shape19 : exv ea19 0 = op false (ip 0 0) (ip 5 0) := by decide +kernel
lemma unequal19 : ip 0 0 ≠ ip 5 0 := by decide +kernel
lemma member19 : ea19 ∈ six := by decide +kernel
lemma shape24 : exv ea24 0 = op false (ip 2 0) (ip 3 0) := by decide +kernel
lemma unequal24 : ip 2 0 ≠ ip 3 0 := by decide +kernel
lemma member24 : ea24 ∈ six := by decide +kernel
lemma shape25 : exv ea25 0 = op false (ip 2 0) (ip 4 0) := by decide +kernel
lemma unequal25 : ip 2 0 ≠ ip 4 0 := by decide +kernel
lemma member25 : ea25 ∈ six := by decide +kernel
lemma shape26 : exv ea26 0 = op false (ip 2 0) (ip 5 0) := by decide +kernel
lemma unequal26 : ip 2 0 ≠ ip 5 0 := by decide +kernel
lemma member26 : ea26 ∈ six := by decide +kernel
lemma shape29 : exv ea29 0 = op false (ip 4 0) (ip 5 0) := by decide +kernel
lemma unequal29 : ip 4 0 ≠ ip 5 0 := by decide +kernel
lemma member29 : ea29 ∈ six := by decide +kernel
lemma shape30 : exv ea30 0 = ip 0 0 ^^^ mz 0 := by decide +kernel
lemma member30 : ea30 ∈ six := by decide +kernel
lemma shape32 : exv ea32 0 = ip 2 0 ^^^ mz 0 := by decide +kernel
lemma member32 : ea32 ∈ six := by decide +kernel
lemma shape34 : exv ea34 0 = ip 4 0 ^^^ mz 0 := by decide +kernel
lemma member34 : ea34 ∈ six := by decide +kernel
lemma shape35 : exv ea35 0 = ip 5 0 ^^^ mz 0 := by decide +kernel
lemma member35 : ea35 ∈ six := by decide +kernel
lemma finiteExtend {P : ℕ × ℕ → Prop} {a b : List (ℕ × ℕ)}
    (ha : ∀ p ∈ a, P p) (hb : ∀ p ∈ b, P p) : ∀ p ∈ a ++ b, P p :=
  fun p hp => (List.mem_append.mp hp).elim (ha p) (hb p)
def empty1 : List (ℕ × ℕ) := []
lemma empty1Valid (base : Imp [] 0 13) : ∀ p ∈ empty1, Excluded 12 p 1 := by simp [empty1]
def f2t1Masks : List (ℕ × ℕ) := [(0x40000000000000000000,0),(0x40000000000000000000000,0),(0x20000000000000000080000000000000000000000000,0),(0x200000000000000000000000000000000000000000080000000000,0),(0x8400000000000000,0),(0x2040000000000000000000004000000000000000000000000000,0),(0x800000000000000000040,0),(0x40000000000000000000000000000000080000000,0),(0x0,1)]
lemma f2t1Cover : frontCover (storedInput ea2 false) empty1 f2t1Masks = true := by decide +kernel
noncomputable def f2t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea2 false)) [ea2] edgeQ2 0 12 1 h p
def c2t1m0d0g0 := stateBlock edgeQ2 1 0x605044b034d0200800379
theorem c2t1m0d0g0ok : deepPass edgeQ2 12 c2t1m0d0g0 = true := by decide +kernel
def c2t1m0d0c := c2t1m0d0g0
theorem c2t1m0d0o : atFront (cliqueMark (storedInput ea2 false)) ea2 edgeQ2 1 0x40000000000000000000 0 c2t1m0d0c = false := by decide +kernel
theorem f2t1n0 : f2t1Run 0x40000000000000000000 0 = false := proveFront (xs:=c2t1m0d0c) c2t1m0d0g0ok c2t1m0d0o

theorem f2t1n1 : f2t1Run 0x40000000000000000000000 0 = false := by decide +kernel
theorem f2t1n2 : f2t1Run 0x20000000000000000080000000000000000000000000 0 = false := by decide +kernel
theorem f2t1n3 : f2t1Run 0x200000000000000000000000000000000000000000080000000000 0 = false := by decide +kernel
theorem f2t1n4 : f2t1Run 0x8400000000000000 0 = false := by decide +kernel
theorem f2t1n5 : f2t1Run 0x2040000000000000000000004000000000000000000000000000 0 = false := by decide +kernel
theorem f2t1n6 : f2t1Run 0x800000000000000000040 0 = false := by decide +kernel
theorem f2t1n7 : f2t1Run 0x40000000000000000000000000000000080000000 0 = false := by decide +kernel
def c2t1m8d0g0 := stateBlock edgeQ2 1 0x4e060504030200700b78
theorem c2t1m8d0g0ok : deepPass edgeQ2 12 c2t1m8d0g0 = true := by decide +kernel
def c2t1m8d0g1 := stateBlock edgeQ2 1 0x60504034f0200701378
theorem c2t1m8d0g1ok : deepPass edgeQ2 12 c2t1m8d0g1 = true := by decide +kernel
def c2t1m8d0g2 := stateBlock edgeQ2 2 0x6050403510260237800000050060504030200701b78
theorem c2t1m8d0g2ok : deepPass edgeQ2 12 c2t1m8d0g2 = true := by decide +kernel
def c2t1m8d0g3 := stateBlock edgeQ2 13 0x6050428034d020080715800000605040b034d02008069580000060504034d530200802958000052060504034d0200806158000006052f04034d02008059580000062a0504034d020080395800002c060504034d020080515800000605040d034d02008049580000060504034d0219008041580000060504034d100200803958000006050429034d02008031580000060504034d021a0080295800000006050403510200702378
theorem c2t1m8d0g3ok : deepPass edgeQ2 12 c2t1m8d0g3 = true := by decide +kernel
def c2t1m8d0c := c2t1m8d0g0 ++ c2t1m8d0g1 ++ c2t1m8d0g2 ++ c2t1m8d0g3
theorem c2t1m8d0o : atFront (cliqueMark (storedInput ea2 false)) ea2 edgeQ2 1 0x0 1 c2t1m8d0c = false := by decide +kernel
theorem f2t1n8 : f2t1Run 0x0 1 = false := proveFront (xs:=c2t1m8d0c) (by simp only [c2t1m8d0c,deepAppend,c2t1m8d0g0ok,c2t1m8d0g1ok,c2t1m8d0g2ok,c2t1m8d0g3ok,Bool.and_self]) c2t1m8d0o

lemma f2t1 (base : Imp [] 0 13) : Excluded 12 ea2 1 := by
  refine useFront base member2 ready2 (binaryEarlier base shape2 unequal2 (empty1Valid base)) ?_ f2t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f2t1Run) f2t1n0 (addMask f2t1n1 (addMask f2t1n2 (addMask f2t1n3 (addMask f2t1n4 (addMask f2t1n5 (addMask f2t1n6 (addMask f2t1n7 (addMask f2t1n8 (endMasks)))))))))
def f17t1Masks : List (ℕ × ℕ) := [(0x40000000000000000000,0),(0x200000000000000000000000000000000000000000000000000000,0),(0x400000000000000,0),(0x80000000000000000000000000,0),(0x800000000000000000000,0),(0x40000000000000000000000,0),(0x40000000000000000000000000000000000000000,0),(0x4000000000000000000000000000,0),(0x20000000000000000000000000000000000080000000,0),(0x8000000000000040,0),(0x2040000000000000000000000000000000000000080000000000,0),(0x0,1)]
lemma f17t1Cover : frontCover (storedInput ea17 false) empty1 f17t1Masks = true := by decide +kernel
noncomputable def f17t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea17 false)) [ea17] edgeQ17 0 12 1 h p
def c17t1m0d0g0 := stateBlock edgeQ17 11 0x35540605040302590090c3580035540605044b03020090bb570035540605360403020090b3570035540605040302090090ab570000003506050403025870a35800003506050403025700809b580035543406050403020090935700355406050456030200908b570035540605040327020090835700003555060504030200807b5800000055060504030200707b58
theorem c17t1m0d0g0ok : deepPass edgeQ17 12 c17t1m0d0g0 = true := by decide +kernel
def c17t1m0d0g1 := stateBlock edgeQ17 3 0x5b5406050403020080c3580000005406050403025a70cb580000355406050403025a80cb58
theorem c17t1m0d0g1ok : deepPass edgeQ17 12 c17t1m0d0g1 = true := by decide +kernel
def c17t1m0d0c := c17t1m0d0g0 ++ c17t1m0d0g1
def c17t1m0d0s := stateBlock edgeQ17 1 0x3554060504030200800379
theorem c17t1m0d0o : stepInside edgeQ17 c17t1m0d0c (stateWord edgeQ17 0x3554060504030200800379) = false := by decide +kernel
theorem c17t1m0d0sok : deepPass edgeQ17 12 c17t1m0d0s = true := proveInside (xs:=c17t1m0d0c) (by simp only [c17t1m0d0c,deepAppend,c17t1m0d0g0ok,c17t1m0d0g1ok,Bool.and_self]) c17t1m0d0o
def c17t1m0d1c := c17t1m0d0s
theorem c17t1m0d1o : atFront (cliqueMark (storedInput ea17 false)) ea17 edgeQ17 1 0x40000000000000000000 0 c17t1m0d1c = false := by decide +kernel
theorem f17t1n0 : f17t1Run 0x40000000000000000000 0 = false := proveFront (xs:=c17t1m0d1c) c17t1m0d0sok c17t1m0d1o

theorem f17t1n1 : f17t1Run 0x200000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem f17t1n2 : f17t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f17t1n3 : f17t1Run 0x80000000000000000000000000 0 = false := by decide +kernel
theorem f17t1n4 : f17t1Run 0x800000000000000000000 0 = false := by decide +kernel
theorem f17t1n5 : f17t1Run 0x40000000000000000000000 0 = false := by decide +kernel
theorem f17t1n6 : f17t1Run 0x40000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem f17t1n7 : f17t1Run 0x4000000000000000000000000000 0 = false := by decide +kernel
theorem f17t1n8 : f17t1Run 0x20000000000000000000000000000000000080000000 0 = false := by decide +kernel
theorem f17t1n9 : f17t1Run 0x8000000000000040 0 = false := by decide +kernel
theorem f17t1n10 : f17t1Run 0x2040000000000000000000000000000000000000080000000000 0 = false := by decide +kernel
def c17t1m11d0g0 := stateBlock edgeQ17 1 0x6055c0403020070d378
theorem c17t1m11d0g0ok : deepPass edgeQ17 12 c17t1m11d0g0 = true := by decide +kernel
def c17t1m11d0g1 := stateBlock edgeQ17 1 0x605045d03020070db78
theorem c17t1m11d0g1ok : deepPass edgeQ17 12 c17t1m11d0g1 = true := by decide +kernel
def c17t1m11d0g2 := stateBlock edgeQ17 2 0x6050403025860eb780000000605040302570070e378
theorem c17t1m11d0g2ok : deepPass edgeQ17 12 c17t1m11d0g2 = true := by decide +kernel
def c17t1m11d0g3 := stateBlock edgeQ17 15 0x54520605040302008061580000546206050403020081015800000006050403610200710958000054060504032d020080595800005406050403490200803158000054060504030c02008071580000540605046003020080615800005406050403021900804158000054060504035f02008101580000540605430403020080f9580000540605040310020080395800005406050403021a00802958000000060504035e020070f158000054060504031202008051580000000605040302005870eb78
theorem c17t1m11d0g3ok : deepPass edgeQ17 12 c17t1m11d0g3 = true := by decide +kernel
def c17t1m11d0g4 := stateBlock edgeQ17 3 0x5406050403530200802958000054061b050403020081195800005406050403024400811158
theorem c17t1m11d0g4ok : deepPass edgeQ17 12 c17t1m11d0g4 = true := by decide +kernel
def c17t1m11d0c := c17t1m11d0g0 ++ c17t1m11d0g1 ++ c17t1m11d0g2 ++ c17t1m11d0g3 ++ c17t1m11d0g4
theorem c17t1m11d0o : atFront (cliqueMark (storedInput ea17 false)) ea17 edgeQ17 1 0x0 1 c17t1m11d0c = false := by decide +kernel
theorem f17t1n11 : f17t1Run 0x0 1 = false := proveFront (xs:=c17t1m11d0c) (by simp only [c17t1m11d0c,deepAppend,c17t1m11d0g0ok,c17t1m11d0g1ok,c17t1m11d0g2ok,c17t1m11d0g3ok,c17t1m11d0g4ok,Bool.and_self]) c17t1m11d0o

lemma f17t1 (base : Imp [] 0 13) : Excluded 12 ea17 1 := by
  refine useFront base member17 ready17 (binaryEarlier base shape17 unequal17 (empty1Valid base)) ?_ f17t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f17t1Run) f17t1n0 (addMask f17t1n1 (addMask f17t1n2 (addMask f17t1n3 (addMask f17t1n4 (addMask f17t1n5 (addMask f17t1n6 (addMask f17t1n7 (addMask f17t1n8 (addMask f17t1n9 (addMask f17t1n10 (addMask f17t1n11 (endMasks))))))))))))
def bank0t1 := empty1 ++ [(0, 3), (1, 2), (6, 3), (7, 2)]
lemma bank0t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank0t1, Excluded 12 p 1 := by
  apply finiteExtend (empty1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f2t1 base
  · exact mirror5 _ _ (f2t1 base)
  · exact f17t1 base
  · exact mirror20 _ _ (f17t1 base)
def f1t1Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000,0),(0x2000000000000000000000000000000800000000000000000000,0),(0x80000000040,0),(0x20000000000000000080000000000000000000000000,0),(0x40000000000000000000000000000000000400000000000000,0),(0x200000000000000000000000004000000000000000000000000000,0),(0x8000000080000000,0),(0x0,1)]
lemma f1t1Cover : frontCover (storedInput ea1 false) bank0t1 f1t1Masks = true := by decide +kernel
noncomputable def f1t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea1 false)) [ea1] edgeQ1 0 12 1 h p
theorem f1t1n0 : f1t1Run 0x40000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem f1t1n1 : f1t1Run 0x2000000000000000000000000000000800000000000000000000 0 = false := by decide +kernel
theorem f1t1n2 : f1t1Run 0x80000000040 0 = false := by decide +kernel
theorem f1t1n3 : f1t1Run 0x20000000000000000080000000000000000000000000 0 = false := by decide +kernel
theorem f1t1n4 : f1t1Run 0x40000000000000000000000000000000000400000000000000 0 = false := by decide +kernel
theorem f1t1n5 : f1t1Run 0x200000000000000000000000004000000000000000000000000000 0 = false := by decide +kernel
theorem f1t1n6 : f1t1Run 0x8000000080000000 0 = false := by decide +kernel
def c1t1m7d0g0 := stateBlock edgeQ1 1 0x63060504030200712378
theorem c1t1m7d0g0ok : deepPass edgeQ1 12 c1t1m7d0g0 = true := by decide +kernel
def c1t1m7d0g1 := stateBlock edgeQ1 1 0x64060504030200712b78
theorem c1t1m7d0g1ok : deepPass edgeQ1 12 c1t1m7d0g1 = true := by decide +kernel
def c1t1m7d0g2 := stateBlock edgeQ1 2 0x6050466030200713b7800000006050465030200713378
theorem c1t1m7d0g2ok : deepPass edgeQ1 12 c1t1m7d0g2 = true := by decide +kernel
def c1t1m7d0g3 := stateBlock edgeQ1 14 0x605046803020071595800002606050467030200815158000006052304670302008069580000060504674603020081495800003006050467030200814158000006052f0467030200805958000006050467034902008031580000062405046703020080495800000605046703210200811158000006050467030244008111580000060504672903020080315800000605046703021a00802958000006050467030219008041580000060504670d030200804958
theorem c1t1m7d0g3ok : deepPass edgeQ1 12 c1t1m7d0g3 = true := by decide +kernel
def c1t1m7d0c := c1t1m7d0g0 ++ c1t1m7d0g1 ++ c1t1m7d0g2 ++ c1t1m7d0g3
theorem c1t1m7d0o : atFront (cliqueMark (storedInput ea1 false)) ea1 edgeQ1 1 0x0 1 c1t1m7d0c = false := by decide +kernel
theorem f1t1n7 : f1t1Run 0x0 1 = false := proveFront (xs:=c1t1m7d0c) (by simp only [c1t1m7d0c,deepAppend,c1t1m7d0g0ok,c1t1m7d0g1ok,c1t1m7d0g2ok,c1t1m7d0g3ok,Bool.and_self]) c1t1m7d0o

lemma f1t1 (base : Imp [] 0 13) : Excluded 12 ea1 1 := by
  refine useFront base member1 ready1 (binaryEarlier base shape1 unequal1 (bank0t1Valid base)) ?_ f1t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f1t1Run) f1t1n0 (addMask f1t1n1 (addMask f1t1n2 (addMask f1t1n3 (addMask f1t1n4 (addMask f1t1n5 (addMask f1t1n6 (addMask f1t1n7 (endMasks))))))))
def f16t1Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000,0),(0x2000000000000000000000000000000800000000000000000000,0),(0x40000000000000000000000000000000000000000000000040,0),(0x200000000000000000000000000000000000000400000000000000,0),(0x4000000000008000000000000000,0),(0x20000000000000000080000000000000000080000000,0),(0x80000000000,0),(0x0,1)]
lemma f16t1Cover : frontCover (storedInput ea16 false) bank0t1 f16t1Masks = true := by decide +kernel
noncomputable def f16t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea16 false)) [ea16] edgeQ16 0 12 1 h p
theorem f16t1n0 : f16t1Run 0x40000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem f16t1n1 : f16t1Run 0x2000000000000000000000000000000800000000000000000000 0 = false := by decide +kernel
theorem f16t1n2 : f16t1Run 0x40000000000000000000000000000000000000000000000040 0 = false := by decide +kernel
theorem f16t1n3 : f16t1Run 0x200000000000000000000000000000000000000400000000000000 0 = false := by decide +kernel
theorem f16t1n4 : f16t1Run 0x4000000000008000000000000000 0 = false := by decide +kernel
theorem f16t1n5 : f16t1Run 0x20000000000000000080000000000000000080000000 0 = false := by decide +kernel
theorem f16t1n6 : f16t1Run 0x80000000000 0 = false := by decide +kernel
def c16t1m7d0g0 := stateBlock edgeQ16 1 0x6050403690200716378
theorem c16t1m7d0g0ok : deepPass edgeQ16 12 c16t1m7d0g0 = true := by decide +kernel
def c16t1m7d0g1 := stateBlock edgeQ16 1 0x6056a04030200716b78
theorem c16t1m7d0g1ok : deepPass edgeQ16 12 c16t1m7d0g1 = true := by decide +kernel
def c16t1m7d0g2 := stateBlock edgeQ16 8 0x6e0624050403020080495800006e0605230403020080695800006e0605040348020081895800006e0605040302190080415800006e0605040d030200804958000000060504036d02007181580000000605040302006c717b7800000006050403026b00717378
theorem c16t1m7d0g2ok : deepPass edgeQ16 12 c16t1m7d0g2 = true := by decide +kernel
def c16t1m7d0c := c16t1m7d0g0 ++ c16t1m7d0g1 ++ c16t1m7d0g2
theorem c16t1m7d0o : atFront (cliqueMark (storedInput ea16 false)) ea16 edgeQ16 1 0x0 1 c16t1m7d0c = false := by decide +kernel
theorem f16t1n7 : f16t1Run 0x0 1 = false := proveFront (xs:=c16t1m7d0c) (by simp only [c16t1m7d0c,deepAppend,c16t1m7d0g0ok,c16t1m7d0g1ok,c16t1m7d0g2ok,Bool.and_self]) c16t1m7d0o

lemma f16t1 (base : Imp [] 0 13) : Excluded 12 ea16 1 := by
  refine useFront base member16 ready16 (binaryEarlier base shape16 unequal16 (bank0t1Valid base)) ?_ f16t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f16t1Run) f16t1n0 (addMask f16t1n1 (addMask f16t1n2 (addMask f16t1n3 (addMask f16t1n4 (addMask f16t1n5 (addMask f16t1n6 (addMask f16t1n7 (endMasks))))))))
def bank2t1 := bank0t1 ++ [(0, 2), (1, 3), (6, 2), (7, 3)]
lemma bank2t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank2t1, Excluded 12 p 1 := by
  apply finiteExtend (bank0t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f1t1 base
  · exact mirror6 _ _ (f1t1 base)
  · exact f16t1 base
  · exact mirror21 _ _ (f16t1 base)
def f10t1Masks : List (ℕ × ℕ) := [(0x200000000020000000000000000000000000000000080000000000,0),(0x2000000000000000000000004000000000000400000000000000,0),(0x40000000000000000000000080000800008000000080000000,0),(0x0,1)]
lemma f10t1Cover : frontCover (storedInput ea10 false) bank2t1 f10t1Masks = true := by decide +kernel
noncomputable def f10t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea10 false)) [ea10] edgeQ10 0 12 1 h p
theorem f10t1n0 : f10t1Run 0x200000000020000000000000000000000000000000080000000000 0 = false := by decide +kernel
theorem f10t1n1 : f10t1Run 0x2000000000000000000000004000000000000400000000000000 0 = false := by decide +kernel
theorem f10t1n2 : f10t1Run 0x40000000000000000000000080000800008000000080000000 0 = false := by decide +kernel
theorem f10t1n3 : f10t1Run 0x0 1 = false := by decide +kernel
lemma f10t1 (base : Imp [] 0 13) : Excluded 12 ea10 1 := by
  refine useFront base member10 ready10 (binaryEarlier base shape10 unequal10 (bank2t1Valid base)) ?_ f10t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f10t1Run) f10t1n0 (addMask f10t1n1 (addMask f10t1n2 (addMask f10t1n3 (endMasks))))
def f25t1Masks : List (ℕ × ℕ) := [(0x4000000000000000000000000000,0),(0x400000000000000,0),(0x800000000000000000000,0),(0x200000000000000000000000000000000000000000080000000000,0),(0x20000000000000000080000000000000000080000000,0),(0x2040000000000000000000000000000000008000000000000000,0),(0x0,1)]
lemma f25t1Cover : frontCover (storedInput ea25 false) bank2t1 f25t1Masks = true := by decide +kernel
noncomputable def f25t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea25 false)) [ea25] edgeQ25 0 12 1 h p
def c25t1m0d0g0 := stateBlock edgeQ25 11 0x6f0605360403710081a358006f340605360403020091bb57000006053670040302008193580000746f06050403020081b35800006f0605040373020081b358006f060536040373020091b358006f060536040372020091ab5800006f060570040302008193580000000605360403710071a35800006f06053604560300819b5700000006057004030200719358
theorem c25t1m0d0g0ok : deepPass edgeQ25 12 c25t1m0d0g0 = true := by decide +kernel
def c25t1m0d0g1 := stateBlock edgeQ25 11 0x5b6f0605360403020091eb5800776f0605360403020091e35800746f0605360403020091b358006f060536040327020091cb57006f060536040376020091db570000750605360403020081ab58006f060516360403020091d357006f0f0605360403020091cb570000060536040372020081ab58006f350605360403020091c357006f060536040338020091bb57
theorem c25t1m0d0g1ok : deepPass edgeQ25 12 c25t1m0d0g1 = true := by decide +kernel
def c25t1m0d0c := c25t1m0d0g0 ++ c25t1m0d0g1
def c25t1m0d0s := stateBlock edgeQ25 1 0x6f0605360403020081f379
theorem c25t1m0d0o : stepInside edgeQ25 c25t1m0d0c (stateWord edgeQ25 0x6f0605360403020081f379) = false := by decide +kernel
theorem c25t1m0d0sok : deepPass edgeQ25 12 c25t1m0d0s = true := proveInside (xs:=c25t1m0d0c) (by simp only [c25t1m0d0c,deepAppend,c25t1m0d0g0ok,c25t1m0d0g1ok,Bool.and_self]) c25t1m0d0o
def c25t1m0d1c := c25t1m0d0s
theorem c25t1m0d1o : atFront (cliqueMark (storedInput ea25 false)) ea25 edgeQ25 1 0x4000000000000000000000000000 0 c25t1m0d1c = false := by decide +kernel
theorem f25t1n0 : f25t1Run 0x4000000000000000000000000000 0 = false := proveFront (xs:=c25t1m0d1c) c25t1m0d0sok c25t1m0d1o

theorem f25t1n1 : f25t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f25t1n2 : f25t1Run 0x800000000000000000000 0 = false := by decide +kernel
theorem f25t1n3 : f25t1Run 0x200000000000000000000000000000000000000000080000000000 0 = false := by decide +kernel
theorem f25t1n4 : f25t1Run 0x20000000000000000080000000000000000080000000 0 = false := by decide +kernel
theorem f25t1n5 : f25t1Run 0x2040000000000000000000000000000000008000000000000000 0 = false := by decide +kernel
def c25t1m6d0g0 := stateBlock edgeQ25 1 0x60536047803020081fb78
theorem c25t1m6d0g0ok : deepPass edgeQ25 12 c25t1m6d0g0 = true := by decide +kernel
def c25t1m6d0g1 := stateBlock edgeQ25 1 0x6050479030200720378
theorem c25t1m6d0g1ok : deepPass edgeQ25 12 c25t1m6d0g1 = true := by decide +kernel
def c25t1m6d0g2 := stateBlock edgeQ25 1 0x605047803020071fb78
theorem c25t1m6d0g2ok : deepPass edgeQ25 12 c25t1m6d0g2 = true := by decide +kernel
def c25t1m6d0g3 := stateBlock edgeQ25 1 0x6050403730200720b78
theorem c25t1m6d0g3ok : deepPass edgeQ25 12 c25t1m6d0g3 = true := by decide +kernel
def c25t1m6d0g4 := stateBlock edgeQ25 1 0x605360479030200820378
theorem c25t1m6d0g4ok : deepPass edgeQ25 12 c25t1m6d0g4 = true := by decide +kernel
def c25t1m6d0g5 := stateBlock edgeQ25 2 0x74060504030200720b7800000605360403730200820b78
theorem c25t1m6d0g5ok : deepPass edgeQ25 12 c25t1m6d0g5 = true := by decide +kernel
def c25t1m6d0g6 := stateBlock edgeQ25 5 0x6057b040302007213780000007a06050403020071fb7800007406053604030200820b7800005b060536040302008203780000005b060504030200720378
theorem c25t1m6d0g6ok : deepPass edgeQ25 12 c25t1m6d0g6 = true := by decide +kernel
def c25t1m6d0g7 := stateBlock edgeQ25 12 0x605360403820200814158000000810605040302007241580000000605048003020072395800000605360403021900804158000006057b3604030200821378000006053604037f0200823158000006053604037e02008229580000000605047d03020072215800000605360403490200803158000006053604037c02008219580000060536040d0302008049580000060536040e030200815158
theorem c25t1m6d0g7ok : deepPass edgeQ25 12 c25t1m6d0g7 = true := by decide +kernel
def c25t1m6d0g8 := stateBlock edgeQ25 18 0x6050403028600725958000006053604032d02008059580000060536044a0302008219580000060536047d0302008221580000060536040302003d8149580000000685050403020072515800002c060536040302008051580000062a053604030200803958000006053604290302008031580000060536040b030200806958000006240536040302008049580000008406050403020072495800000605363c0403020082295800000605360428030200807158000026060536040302008151580000000605360403190070415800007a0605360403020081fb7800000006050403020083721378
theorem c25t1m6d0g8ok : deepPass edgeQ25 12 c25t1m6d0g8 = true := by decide +kernel
def c25t1m6d0g9 := stateBlock edgeQ25 6 0x6053604030200408269580000060536040302003f826158000084060536040302008249580000064c0536040302008231580000300605360403020081415800000605362f04030200805958
theorem c25t1m6d0g9ok : deepPass edgeQ25 12 c25t1m6d0g9 = true := by decide +kernel
def c25t1m6d0c := c25t1m6d0g0 ++ c25t1m6d0g1 ++ c25t1m6d0g2 ++ c25t1m6d0g3 ++ c25t1m6d0g4 ++ c25t1m6d0g5 ++ c25t1m6d0g6 ++ c25t1m6d0g7 ++ c25t1m6d0g8 ++ c25t1m6d0g9
theorem c25t1m6d0o : atFront (cliqueMark (storedInput ea25 false)) ea25 edgeQ25 1 0x0 1 c25t1m6d0c = false := by decide +kernel
theorem f25t1n6 : f25t1Run 0x0 1 = false := proveFront (xs:=c25t1m6d0c) (by simp only [c25t1m6d0c,deepAppend,c25t1m6d0g0ok,c25t1m6d0g1ok,c25t1m6d0g2ok,c25t1m6d0g3ok,c25t1m6d0g4ok,c25t1m6d0g5ok,c25t1m6d0g6ok,c25t1m6d0g7ok,c25t1m6d0g8ok,c25t1m6d0g9ok,Bool.and_self]) c25t1m6d0o

lemma f25t1 (base : Imp [] 0 13) : Excluded 12 ea25 1 := by
  refine useFront base member25 ready25 (binaryEarlier base shape25 unequal25 (bank2t1Valid base)) ?_ f25t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f25t1Run) f25t1n0 (addMask f25t1n1 (addMask f25t1n2 (addMask f25t1n3 (addMask f25t1n4 (addMask f25t1n5 (addMask f25t1n6 (endMasks)))))))
def bank4t1 := bank2t1 ++ [(2, 4), (3, 4), (8, 4), (9, 4)]
lemma bank4t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank4t1, Excluded 12 p 1 := by
  apply finiteExtend (bank2t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f10t1 base
  · exact mirror12 _ _ (f10t1 base)
  · exact f25t1 base
  · exact mirror27 _ _ (f25t1 base)
def f3t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x4000000000008000000000000000,0),(0x20000000000000000080000000000000000000000000,0),(0x80080000000,0),(0x2040000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f3t1Cover : frontCover (storedInput ea3 false) bank4t1 f3t1Masks = true := by decide +kernel
noncomputable def f3t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea3 false)) [ea3] edgeQ3 0 12 1 h p
theorem f3t1n0 : f3t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f3t1n1 : f3t1Run 0x4000000000008000000000000000 0 = false := by decide +kernel
theorem f3t1n2 : f3t1Run 0x20000000000000000080000000000000000000000000 0 = false := by decide +kernel
theorem f3t1n3 : f3t1Run 0x80080000000 0 = false := by decide +kernel
theorem f3t1n4 : f3t1Run 0x2040000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c3t1m5d0g0 := stateBlock edgeQ3 1 0x6050487030200727378
theorem c3t1m5d0g0ok : deepPass edgeQ3 12 c3t1m5d0g0 = true := by decide +kernel
def c3t1m5d0g1 := stateBlock edgeQ3 1 0x6880504030200727b78
theorem c3t1m5d0g1ok : deepPass edgeQ3 12 c3t1m5d0g1 = true := by decide +kernel
def c3t1m5d0g2 := stateBlock edgeQ3 1 0x6058904030200728378
theorem c3t1m5d0g2ok : deepPass edgeQ3 12 c3t1m5d0g2 = true := by decide +kernel
def c3t1m5d0g3 := stateBlock edgeQ3 1 0x6050403028a628b78
theorem c3t1m5d0g3ok : deepPass edgeQ3 12 c3t1m5d0g3 = true := by decide +kernel
def c3t1m5d0g4 := stateBlock edgeQ3 6 0x62a050403028b0080395800000605040349028b0080315800000605040310028b0080395800000605040d03028b008049580000060504030c028b0080715800000006050403028a00728b78
theorem c3t1m5d0g4ok : deepPass edgeQ3 12 c3t1m5d0g4 = true := by decide +kernel
def c3t1m5d0g5 := stateBlock edgeQ3 9 0x3006050403028b0081415800000605040312028b0080515800000605040b03028b008069580000060504032d028b0080595800000605230403028b0080695800002c06050403028b0080515800000605042903028b0080315800000605042803028b00807158000006052f0403028b00805958
theorem c3t1m5d0g5ok : deepPass edgeQ3 12 c3t1m5d0g5 = true := by decide +kernel
def c3t1m5d0c := c3t1m5d0g0 ++ c3t1m5d0g1 ++ c3t1m5d0g2 ++ c3t1m5d0g3 ++ c3t1m5d0g4 ++ c3t1m5d0g5
theorem c3t1m5d0o : atFront (cliqueMark (storedInput ea3 false)) ea3 edgeQ3 1 0x0 1 c3t1m5d0c = false := by decide +kernel
theorem f3t1n5 : f3t1Run 0x0 1 = false := proveFront (xs:=c3t1m5d0c) (by simp only [c3t1m5d0c,deepAppend,c3t1m5d0g0ok,c3t1m5d0g1ok,c3t1m5d0g2ok,c3t1m5d0g3ok,c3t1m5d0g4ok,c3t1m5d0g5ok,Bool.and_self]) c3t1m5d0o

lemma f3t1 (base : Imp [] 0 13) : Excluded 12 ea3 1 := by
  refine useFront base member3 ready3 (binaryEarlier base shape3 unequal3 (bank4t1Valid base)) ?_ f3t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f3t1Run) f3t1n0 (addMask f3t1n1 (addMask f3t1n2 (addMask f3t1n3 (addMask f3t1n4 (addMask f3t1n5 (endMasks))))))
def f18t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x4000000000000000000080000000,0),(0x2040000020000000000000000080000000008000080000000000,0),(0x0,1)]
lemma f18t1Cover : frontCover (storedInput ea18 false) bank4t1 f18t1Masks = true := by decide +kernel
noncomputable def f18t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea18 false)) [ea18] edgeQ18 0 12 1 h p
theorem f18t1n0 : f18t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f18t1n1 : f18t1Run 0x4000000000000000000080000000 0 = false := by decide +kernel
theorem f18t1n2 : f18t1Run 0x2040000020000000000000000080000000008000080000000000 0 = false := by decide +kernel
def c18t1m3d0g0 := stateBlock edgeQ18 1 0x605048c030200729378
theorem c18t1m3d0g0ok : deepPass edgeQ18 12 c18t1m3d0g0 = true := by decide +kernel
def c18t1m3d0g1 := stateBlock edgeQ18 1 0x6058d04030200729b78
theorem c18t1m3d0g1ok : deepPass edgeQ18 12 c18t1m3d0g1 = true := by decide +kernel
def c18t1m3d0g2 := stateBlock edgeQ18 3 0x900605048c0302008293780000008f06050403020072a378000000060504038e020072a378
theorem c18t1m3d0g2ok : deepPass edgeQ18 12 c18t1m3d0g2 = true := by decide +kernel
def c18t1m3d0g3 := stateBlock edgeQ18 10 0x90062a0504030200803958000090060504031202008051580000900605040b030200806958000000940605040302007293780000000605930403020072b1580000900605042803020080715800000092060504030200729b780000009106050403020072ab78000090060504038e020082a37800009006058d04030200829b78
theorem c18t1m3d0g3ok : deepPass edgeQ18 12 c18t1m3d0g3 = true := by decide +kernel
def c18t1m3d0g4 := stateBlock edgeQ18 10 0x90060504030219008041580000000698050403020072c9580000000605049703020072c158000090060504032d020080595800009006050429030200803158000090060504030c02008071580000000605040302009672ab780000000605040395020072b9580000900605040d03020080495800009006050403100200803958
theorem c18t1m3d0g4ok : deepPass edgeQ18 12 c18t1m3d0g4 = true := by decide +kernel
def c18t1m3d0c := c18t1m3d0g0 ++ c18t1m3d0g1 ++ c18t1m3d0g2 ++ c18t1m3d0g3 ++ c18t1m3d0g4
theorem c18t1m3d0o : atFront (cliqueMark (storedInput ea18 false)) ea18 edgeQ18 1 0x0 1 c18t1m3d0c = false := by decide +kernel
theorem f18t1n3 : f18t1Run 0x0 1 = false := proveFront (xs:=c18t1m3d0c) (by simp only [c18t1m3d0c,deepAppend,c18t1m3d0g0ok,c18t1m3d0g1ok,c18t1m3d0g2ok,c18t1m3d0g3ok,c18t1m3d0g4ok,Bool.and_self]) c18t1m3d0o

lemma f18t1 (base : Imp [] 0 13) : Excluded 12 ea18 1 := by
  refine useFront base member18 ready18 (binaryEarlier base shape18 unequal18 (bank4t1Valid base)) ?_ f18t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f18t1Run) f18t1n0 (addMask f18t1n1 (addMask f18t1n2 (addMask f18t1n3 (endMasks))))
def bank6t1 := bank4t1 ++ [(0, 4), (1, 4), (6, 4), (7, 4)]
lemma bank6t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank6t1, Excluded 12 p 1 := by
  apply finiteExtend (bank4t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f3t1 base
  · exact mirror7 _ _ (f3t1 base)
  · exact f18t1 base
  · exact mirror22 _ _ (f18t1 base)
def f11t1Masks : List (ℕ × ℕ) := [(0x4000000000008000000000000000,0),(0x400000000000000,0),(0x2040000000000000000000000000000000000000000000000000,0),(0x20000000000000000000000000000000080000000000,0),(0x0,1)]
lemma f11t1Cover : frontCover (storedInput ea11 false) bank6t1 f11t1Masks = true := by decide +kernel
noncomputable def f11t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea11 false)) [ea11] edgeQ11 0 12 1 h p
theorem f11t1n0 : f11t1Run 0x4000000000008000000000000000 0 = false := by decide +kernel
theorem f11t1n1 : f11t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f11t1n2 : f11t1Run 0x2040000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem f11t1n3 : f11t1Run 0x20000000000000000000000000000000080000000000 0 = false := by decide +kernel
def c11t1m4d0g0 := stateBlock edgeQ11 1 0x605049903020072d378
theorem c11t1m4d0g0ok : deepPass edgeQ11 12 c11t1m4d0g0 = true := by decide +kernel
def c11t1m4d0g1 := stateBlock edgeQ11 2 0x60504039b020072e378000000069a050403020072db78
theorem c11t1m4d0g1ok : deepPass edgeQ11 12 c11t1m4d0g1 = true := by decide +kernel
def c11t1m4d0g2 := stateBlock edgeQ11 5 0x605040e0302009d8151580000060504030c02009d8071580000060504031202009d80515800000605040d0302009d8049580000009c06050403020072eb78
theorem c11t1m4d0g2ok : deepPass edgeQ11 12 c11t1m4d0g2 = true := by decide +kernel
def c11t1m4d0c := c11t1m4d0g0 ++ c11t1m4d0g1 ++ c11t1m4d0g2
theorem c11t1m4d0o : atFront (cliqueMark (storedInput ea11 false)) ea11 edgeQ11 1 0x0 1 c11t1m4d0c = false := by decide +kernel
theorem f11t1n4 : f11t1Run 0x0 1 = false := proveFront (xs:=c11t1m4d0c) (by simp only [c11t1m4d0c,deepAppend,c11t1m4d0g0ok,c11t1m4d0g1ok,c11t1m4d0g2ok,Bool.and_self]) c11t1m4d0o

lemma f11t1 (base : Imp [] 0 13) : Excluded 12 ea11 1 := by
  refine useFront base member11 ready11 (binaryEarlier base shape11 unequal11 (bank6t1Valid base)) ?_ f11t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f11t1Run) f11t1n0 (addMask f11t1n1 (addMask f11t1n2 (addMask f11t1n3 (addMask f11t1n4 (endMasks)))))
def f26t1Masks : List (ℕ × ℕ) := [(0x2040000020000000000000004000000000000400080000000000,0),(0x8000000000000000,0),(0x0,1)]
lemma f26t1Cover : frontCover (storedInput ea26 false) bank6t1 f26t1Masks = true := by decide +kernel
noncomputable def f26t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea26 false)) [ea26] edgeQ26 0 12 1 h p
theorem f26t1n0 : f26t1Run 0x2040000020000000000000004000000000000400080000000000 0 = false := by decide +kernel
theorem f26t1n1 : f26t1Run 0x8000000000000000 0 = false := by decide +kernel
theorem f26t1n2 : f26t1Run 0x0 1 = false := by decide +kernel
lemma f26t1 (base : Imp [] 0 13) : Excluded 12 ea26 1 := by
  refine useFront base member26 ready26 (binaryEarlier base shape26 unequal26 (bank6t1Valid base)) ?_ f26t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f26t1Run) f26t1n0 (addMask f26t1n1 (addMask f26t1n2 (endMasks)))
def bank8t1 := bank6t1 ++ [(2, 5), (3, 5), (8, 5), (9, 5)]
lemma bank8t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank8t1, Excluded 12 p 1 := by
  apply finiteExtend (bank6t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f11t1 base
  · exact mirror13 _ _ (f11t1 base)
  · exact f26t1 base
  · exact mirror28 _ _ (f26t1 base)
def f4t1Masks : List (ℕ × ℕ) := [(0x2040000000000000000000004000000000008400000000000000,0),(0x0,1)]
lemma f4t1Cover : frontCover (storedInput ea4 false) bank8t1 f4t1Masks = true := by decide +kernel
noncomputable def f4t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea4 false)) [ea4] edgeQ4 0 12 1 h p
theorem f4t1n0 : f4t1Run 0x2040000000000000000000004000000000008400000000000000 0 = false := by decide +kernel
theorem f4t1n1 : f4t1Run 0x0 1 = false := by decide +kernel
lemma f4t1 (base : Imp [] 0 13) : Excluded 12 ea4 1 := by
  refine useFront base member4 ready4 (binaryEarlier base shape4 unequal4 (bank8t1Valid base)) ?_ f4t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f4t1Run) f4t1n0 (addMask f4t1n1 (endMasks))
def f19t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x40000000000000000000004000000000000000000000000000,0),(0x2000000000000000000000000000000000008000000000000000,0),(0x0,1)]
lemma f19t1Cover : frontCover (storedInput ea19 false) bank8t1 f19t1Masks = true := by decide +kernel
noncomputable def f19t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea19 false)) [ea19] edgeQ19 0 12 1 h p
theorem f19t1n0 : f19t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f19t1n1 : f19t1Run 0x40000000000000000000004000000000000000000000000000 0 = false := by decide +kernel
theorem f19t1n2 : f19t1Run 0x2000000000000000000000000000000000008000000000000000 0 = false := by decide +kernel
def c19t1m3d0g0 := stateBlock edgeQ19 1 0x605049e03020072f378
theorem c19t1m3d0g0ok : deepPass edgeQ19 12 c19t1m3d0g0 = true := by decide +kernel
def c19t1m3d0g1 := stateBlock edgeQ19 1 0x60504039f020072fb78
theorem c19t1m3d0g1ok : deepPass edgeQ19 12 c19t1m3d0g1 = true := by decide +kernel
def c19t1m3d0g2 := stateBlock edgeQ19 2 0x605040302a100730b780000000605a004030200730378
theorem c19t1m3d0g2ok : deepPass edgeQ19 12 c19t1m3d0g2 = true := by decide +kernel
def c19t1m3d0g3 := stateBlock edgeQ19 12 0xa2060504034902008031580000a20605040d0302008049580000a2060504030c02008071580000a206050403024400811158000052a20605040302008061580000a2060504031202008051580000a206050403021a008029580000a2060504032d02008059580000a2062a0504030200803958000000060504a30302007311580000a2060504030219008041580000a20605040b030200806958
theorem c19t1m3d0g3ok : deepPass edgeQ19 12 c19t1m3d0g3 = true := by decide +kernel
def c19t1m3d0c := c19t1m3d0g0 ++ c19t1m3d0g1 ++ c19t1m3d0g2 ++ c19t1m3d0g3
theorem c19t1m3d0o : atFront (cliqueMark (storedInput ea19 false)) ea19 edgeQ19 1 0x0 1 c19t1m3d0c = false := by decide +kernel
theorem f19t1n3 : f19t1Run 0x0 1 = false := proveFront (xs:=c19t1m3d0c) (by simp only [c19t1m3d0c,deepAppend,c19t1m3d0g0ok,c19t1m3d0g1ok,c19t1m3d0g2ok,c19t1m3d0g3ok,Bool.and_self]) c19t1m3d0o

lemma f19t1 (base : Imp [] 0 13) : Excluded 12 ea19 1 := by
  refine useFront base member19 ready19 (binaryEarlier base shape19 unequal19 (bank8t1Valid base)) ?_ f19t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f19t1Run) f19t1n0 (addMask f19t1n1 (addMask f19t1n2 (addMask f19t1n3 (endMasks))))
def bank10t1 := bank8t1 ++ [(0, 5), (1, 5), (6, 5), (7, 5)]
lemma bank10t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank10t1, Excluded 12 p 1 := by
  apply finiteExtend (bank8t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f4t1 base
  · exact mirror8 _ _ (f4t1 base)
  · exact f19t1 base
  · exact mirror23 _ _ (f19t1 base)
def f0t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x4000000000000000000000000000,0),(0x40000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f0t1Cover : frontCover (storedInput ea0 false) bank10t1 f0t1Masks = true := by decide +kernel
noncomputable def f0t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea0 false)) [ea0] edgeQ0 0 12 1 h p
theorem f0t1n0 : f0t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f0t1n1 : f0t1Run 0x4000000000000000000000000000 0 = false := by decide +kernel
theorem f0t1n2 : f0t1Run 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c0t1m3d0g0 := stateBlock edgeQ0 1 0xa4060504030200731b78
theorem c0t1m3d0g0ok : deepPass edgeQ0 12 c0t1m3d0g0 = true := by decide +kernel
def c0t1m3d0g1 := stateBlock edgeQ0 1 0xa5060504030200732378
theorem c0t1m3d0g1ok : deepPass edgeQ0 12 c0t1m3d0g1 = true := by decide +kernel
def c0t1m3d0g2 := stateBlock edgeQ0 1 0x605a604030200732b78
theorem c0t1m3d0g2ok : deepPass edgeQ0 12 c0t1m3d0g2 = true := by decide +kernel
def c0t1m3d0g3 := stateBlock edgeQ0 6 0x605a8042803020080715800000605a80403021a0080295800000605a8040b03020080695800000605a804030c02008071580000000605a704030200733378000000000605a7040302633378
theorem c0t1m3d0g3ok : deepPass edgeQ0 12 c0t1m3d0g3 = true := by decide +kernel
def c0t1m3d0g4 := stateBlock edgeQ0 10 0x62a05a80403020080395800000605a8040d0302008049580000260605a80403020081515800000605a8040353020080295800000605a8044703020080415800000605a8046003020080615800002c0605a80403020080515800000605a804030219008041580000062405a80403020080495800000605a82304030200806958
theorem c0t1m3d0g4ok : deepPass edgeQ0 12 c0t1m3d0g4 = true := by decide +kernel
def c0t1m3d0c := c0t1m3d0g0 ++ c0t1m3d0g1 ++ c0t1m3d0g2 ++ c0t1m3d0g3 ++ c0t1m3d0g4
theorem c0t1m3d0o : atFront (cliqueMark (storedInput ea0 false)) ea0 edgeQ0 1 0x0 1 c0t1m3d0c = false := by decide +kernel
theorem f0t1n3 : f0t1Run 0x0 1 = false := proveFront (xs:=c0t1m3d0c) (by simp only [c0t1m3d0c,deepAppend,c0t1m3d0g0ok,c0t1m3d0g1ok,c0t1m3d0g2ok,c0t1m3d0g3ok,c0t1m3d0g4ok,Bool.and_self]) c0t1m3d0o

lemma f0t1 (base : Imp [] 0 13) : Excluded 12 ea0 1 := by
  refine useFront base member0 ready0 (binaryEarlier base shape0 unequal0 (bank10t1Valid base)) ?_ f0t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f0t1Run) f0t1n0 (addMask f0t1n1 (addMask f0t1n2 (addMask f0t1n3 (endMasks))))
def f15t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x40000000000000000000004000000000000000000000000000,0),(0x0,1)]
lemma f15t1Cover : frontCover (storedInput ea15 false) bank10t1 f15t1Masks = true := by decide +kernel
noncomputable def f15t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea15 false)) [ea15] edgeQ15 0 12 1 h p
theorem f15t1n0 : f15t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f15t1n1 : f15t1Run 0x40000000000000000000004000000000000000000000000000 0 = false := by decide +kernel
def c15t1m2d0g0 := stateBlock edgeQ15 1 0x6050403720200733b78
theorem c15t1m2d0g0ok : deepPass edgeQ15 12 c15t1m2d0g0 = true := by decide +kernel
def c15t1m2d0g1 := stateBlock edgeQ15 1 0x60504a9030200734378
theorem c15t1m2d0g1ok : deepPass edgeQ15 12 c15t1m2d0g1 = true := by decide +kernel
def c15t1m2d0g2 := stateBlock edgeQ15 2 0x6050403027100734b7800000000060504037100634b78
theorem c15t1m2d0g2ok : deepPass edgeQ15 12 c15t1m2d0g2 = true := by decide +kernel
def c15t1m2d0g3 := stateBlock edgeQ15 10 0xab060504290302008031580000ab060504031002008039580000ab0605040e0302008151580000ab0605040b0302008069580000ab060504030c020080715800000006050403ad0200736158000000060504ac0302007359580000ab0605040d0302008049580000ab06050403120200805158000000060504030200aa735378
theorem c15t1m2d0g3ok : deepPass edgeQ15 12 c15t1m2d0g3 = true := by decide +kernel
def c15t1m2d0c := c15t1m2d0g0 ++ c15t1m2d0g1 ++ c15t1m2d0g2 ++ c15t1m2d0g3
theorem c15t1m2d0o : atFront (cliqueMark (storedInput ea15 false)) ea15 edgeQ15 1 0x0 1 c15t1m2d0c = false := by decide +kernel
theorem f15t1n2 : f15t1Run 0x0 1 = false := proveFront (xs:=c15t1m2d0c) (by simp only [c15t1m2d0c,deepAppend,c15t1m2d0g0ok,c15t1m2d0g1ok,c15t1m2d0g2ok,c15t1m2d0g3ok,Bool.and_self]) c15t1m2d0o

lemma f15t1 (base : Imp [] 0 13) : Excluded 12 ea15 1 := by
  refine useFront base member15 ready15 (binaryEarlier base shape15 unequal15 (bank10t1Valid base)) ?_ f15t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f15t1Run) f15t1n0 (addMask f15t1n1 (addMask f15t1n2 (endMasks)))
def bank12t1 := bank10t1 ++ [(0, 1), (6, 1)]
lemma bank12t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank12t1, Excluded 12 p 1 := by
  apply finiteExtend (bank10t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f0t1 base
  · exact f15t1 base
def f9t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x40000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f9t1Cover : frontCover (storedInput ea9 false) bank12t1 f9t1Masks = true := by decide +kernel
noncomputable def f9t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea9 false)) [ea9] edgeQ9 0 12 1 h p
theorem f9t1n0 : f9t1Run 0x400000000000000 0 = false := by decide +kernel
theorem f9t1n1 : f9t1Run 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c9t1m2d0g0 := stateBlock edgeQ9 1 0x6050403ae00636b78
theorem c9t1m2d0g0ok : deepPass edgeQ9 12 c9t1m2d0g0 = true := by decide +kernel
def c9t1m2d0g1 := stateBlock edgeQ9 1 0x6050403ae0200736b78
theorem c9t1m2d0g1ok : deepPass edgeQ9 12 c9t1m2d0g1 = true := by decide +kernel
def c9t1m2d0g2 := stateBlock edgeQ9 3 0x6050403b10200738378000000b0060504030200737b78000000af060504030200737378
theorem c9t1m2d0g2ok : deepPass edgeQ9 12 c9t1m2d0g2 = true := by decide +kernel
def c9t1m2d0g3 := stateBlock edgeQ9 12 0x605044a03b2020082195800000605040e03b202008151580000061b050403b2020081195800000605430403b2020080f9580000064c050403b2020082315800003006050403b20200814158000006050403b2480200818958000006050403b2210200811158000006053c0403b2020082295800000605040312b2020080515800000605042903b2020080315800000605040d03b20200804958
theorem c9t1m2d0g3ok : deepPass edgeQ9 12 c9t1m2d0g3 = true := by decide +kernel
def c9t1m2d0c := c9t1m2d0g0 ++ c9t1m2d0g1 ++ c9t1m2d0g2 ++ c9t1m2d0g3
theorem c9t1m2d0o : atFront (cliqueMark (storedInput ea9 false)) ea9 edgeQ9 1 0x0 1 c9t1m2d0c = false := by decide +kernel
theorem f9t1n2 : f9t1Run 0x0 1 = false := proveFront (xs:=c9t1m2d0c) (by simp only [c9t1m2d0c,deepAppend,c9t1m2d0g0ok,c9t1m2d0g1ok,c9t1m2d0g2ok,c9t1m2d0g3ok,Bool.and_self]) c9t1m2d0o

lemma f9t1 (base : Imp [] 0 13) : Excluded 12 ea9 1 := by
  refine useFront base member9 ready9 (binaryEarlier base shape9 unequal9 (bank12t1Valid base)) ?_ f9t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f9t1Run) f9t1n0 (addMask f9t1n1 (addMask f9t1n2 (endMasks)))
def f24t1Masks : List (ℕ × ℕ) := [(0x400000000000000,0),(0x40000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f24t1Cover : frontCover (storedInput ea24 false) bank12t1 f24t1Masks = true := by decide +kernel
noncomputable def f24t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea24 false)) [ea24] edgeQ24 0 12 1 h p
def c24t1m0d0g0 := stateBlock edgeQ24 13 0xb306050403ae3800838b580000b306050403ae0200838b58000000060504033802b673bb5800b306b5050403380200939b5800b30605b4040338020093935800b3060516040338020091bb570000b30605360338020083b3570000b0b306050403020083ab580000afb306050403020083a358006fb30605040338020091bb57000006b5050403380200839b5800000605b40403380200839358000000b306050403ae00738b58
theorem c24t1m0d0g0ok : deepPass edgeQ24 12 c24t1m0d0g0 = true := by decide +kernel
def c24t1m0d0g1 := stateBlock edgeQ24 1 0xb3220605040338020093c357
theorem c24t1m0d0g1ok : deepPass edgeQ24 12 c24t1m0d0g1 = true := by decide +kernel
def c24t1m0d0c := c24t1m0d0g0 ++ c24t1m0d0g1
def c24t1m0d0s := stateBlock edgeQ24 1 0xb30605040338020083cb79
theorem c24t1m0d0o : stepInside edgeQ24 c24t1m0d0c (stateWord edgeQ24 0xb30605040338020083cb79) = false := by decide +kernel
theorem c24t1m0d0sok : deepPass edgeQ24 12 c24t1m0d0s = true := proveInside (xs:=c24t1m0d0c) (by simp only [c24t1m0d0c,deepAppend,c24t1m0d0g0ok,c24t1m0d0g1ok,Bool.and_self]) c24t1m0d0o
def c24t1m0d1c := c24t1m0d0s
theorem c24t1m0d1o : atFront (cliqueMark (storedInput ea24 false)) ea24 edgeQ24 1 0x400000000000000 0 c24t1m0d1c = false := by decide +kernel
theorem f24t1n0 : f24t1Run 0x400000000000000 0 = false := proveFront (xs:=c24t1m0d1c) c24t1m0d0sok c24t1m0d1o

theorem f24t1n1 : f24t1Run 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c24t1m2d0g0 := stateBlock edgeQ24 1 0x6b5050403020073d378
theorem c24t1m2d0g0ok : deepPass edgeQ24 12 c24t1m2d0g0 = true := by decide +kernel
def c24t1m2d0g1 := stateBlock edgeQ24 1 0x605b40403020073db78
theorem c24t1m2d0g1ok : deepPass edgeQ24 12 c24t1m2d0g1 = true := by decide +kernel
def c24t1m2d0g2 := stateBlock edgeQ24 2 0xb30605b40403020083db780000b306b5050403020083d378
theorem c24t1m2d0g2ok : deepPass edgeQ24 12 c24t1m2d0g2 = true := by decide +kernel
def c24t1m2d0g3 := stateBlock edgeQ24 3 0x605040302b80073eb78000000b706050403020073eb78000000000605040302b663e378
theorem c24t1m2d0g3ok : deepPass edgeQ24 12 c24t1m2d0g3 = true := by decide +kernel
def c24t1m2d0g4 := stateBlock edgeQ24 3 0xba06050403020073db78000000b906050403020073d378000000b30605040302b673e378
theorem c24t1m2d0g4ok : deepPass edgeQ24 12 c24t1m2d0g4 = true := by decide +kernel
def c24t1m2d0g5 := stateBlock edgeQ24 8 0xb30605430403020080f95800000006050403be0200740158000000bd06050403020073e378000000bc06050403020073f9580000b3060504030200b683e37800000006bb050403020073f1580000b30605040302b80083eb78000000060504030200b673e378
theorem c24t1m2d0g5ok : deepPass edgeQ24 12 c24t1m2d0g5 = true := by decide +kernel
def c24t1m2d0g6 := stateBlock edgeQ24 14 0xb3064c05040302008231580000b3060504038202008141580000b30605044a0302008219580000b3060504032102008111580000b3060504600302008061580000b3060504035f02008101580000b3060504037f02008231580000b306053c040302008229580000b3060504290302008031580000b306050403490200803158000000060504c00302007411580000b3060504037e02008229580000000605bf040302007409580000b3061b0504030200811958
theorem c24t1m2d0g6ok : deepPass edgeQ24 12 c24t1m2d0g6 = true := by decide +kernel
def c24t1m2d0g7 := stateBlock edgeQ24 15 0xb3062405040302008049580000b3060523040302008069580000b3060504031e02008431580000b3060504030200408269580000b30605040302003f826158000000000605040302c36429580000b3c20605040302008421580000b3300605040302008141580000b306052f040302008059580000b32c0605040302008051580000b3060504280302008071580000b3060504034802008189580000b306050446030200814958000000c20605040302007421580000b3060504030200c1841958
theorem c24t1m2d0g7ok : deepPass edgeQ24 12 c24t1m2d0g7 = true := by decide +kernel
def c24t1m2d0c := c24t1m2d0g0 ++ c24t1m2d0g1 ++ c24t1m2d0g2 ++ c24t1m2d0g3 ++ c24t1m2d0g4 ++ c24t1m2d0g5 ++ c24t1m2d0g6 ++ c24t1m2d0g7
theorem c24t1m2d0o : atFront (cliqueMark (storedInput ea24 false)) ea24 edgeQ24 1 0x0 1 c24t1m2d0c = false := by decide +kernel
theorem f24t1n2 : f24t1Run 0x0 1 = false := proveFront (xs:=c24t1m2d0c) (by simp only [c24t1m2d0c,deepAppend,c24t1m2d0g0ok,c24t1m2d0g1ok,c24t1m2d0g2ok,c24t1m2d0g3ok,c24t1m2d0g4ok,c24t1m2d0g5ok,c24t1m2d0g6ok,c24t1m2d0g7ok,Bool.and_self]) c24t1m2d0o

lemma f24t1 (base : Imp [] 0 13) : Excluded 12 ea24 1 := by
  refine useFront base member24 ready24 (binaryEarlier base shape24 unequal24 (bank12t1Valid base)) ?_ f24t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f24t1Run) f24t1n0 (addMask f24t1n1 (addMask f24t1n2 (endMasks)))
def bank14t1 := bank12t1 ++ [(2, 3), (8, 3)]
lemma bank14t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank14t1, Excluded 12 p 1 := by
  apply finiteExtend (bank12t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f9t1 base
  · exact f24t1 base
def f14t1Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000000000000,1)]
lemma f14t1Cover : frontCover (storedInput ea14 false) bank14t1 f14t1Masks = true := by decide +kernel
noncomputable def f14t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea14 false)) [ea14] edgeQ14 0 12 1 h p
theorem f14t1n0 : f14t1Run 0x40000000000000000000000000000000000000000000000000 1 = false := by decide +kernel
lemma f14t1 (base : Imp [] 0 13) : Excluded 12 ea14 1 := by
  refine useFront base member14 ready14 (binaryEarlier base shape14 unequal14 (bank14t1Valid base)) ?_ f14t1Cover ?_
  · exact ⟨(0x40000000000000000000000000000000000000000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f14t1Run) f14t1n0 (endMasks)
def f29t1Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f29t1Cover : frontCover (storedInput ea29 false) bank14t1 f29t1Masks = true := by decide +kernel
noncomputable def f29t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea29 false)) [ea29] edgeQ29 0 12 1 h p
theorem f29t1n0 : f29t1Run 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c29t1m1d0g0 := stateBlock edgeQ29 1 0x605040302c400743b78
theorem c29t1m1d0g0ok : deepPass edgeQ29 12 c29t1m1d0g0 = true := by decide +kernel
def c29t1m1d0g1 := stateBlock edgeQ29 1 0x605040302c500744378
theorem c29t1m1d0g1ok : deepPass edgeQ29 12 c29t1m1d0g1 = true := by decide +kernel
def c29t1m1d0g2 := stateBlock edgeQ29 1 0x605040302c600744b78
theorem c29t1m1d0g2ok : deepPass edgeQ29 12 c29t1m1d0g2 = true := by decide +kernel
def c29t1m1d0g3 := stateBlock edgeQ29 2 0x910605040302007453780000000605040302c700745378
theorem c29t1m1d0g3ok : deepPass edgeQ29 12 c29t1m1d0g3 = true := by decide +kernel
def c29t1m1d0g4 := stateBlock edgeQ29 6 0x2606050403cb0200815158000006050403cb02c400843b78000006050403cb02c5008443780000000605ca04030200743b78000000060504c903020074437800000006c80504030200744b78
theorem c29t1m1d0g4ok : deepPass edgeQ29 12 c29t1m1d0g4 = true := by decide +kernel
def c29t1m1d0g5 := stateBlock edgeQ29 10 0x6050403cb02c600844b7800000605040312cb02008051580000060504032dcb02008059580000060504037ccb020082195800000605040d03cb02008049580000062a050403cb020080395800000624050403cb02008049580000060504030ccb020080715800000605230403cb020080695800000605040b03cb0200806958
theorem c29t1m1d0g5ok : deepPass edgeQ29 12 c29t1m1d0g5 = true := by decide +kernel
def c29t1m1d0g6 := stateBlock edgeQ29 13 0x3006050403cb02008141580000000605040302cd007461580000060504037fcb0200823158000006053c0403cb02008229580000060504037ecb020082295800000605042903cb020080315800000605040349cb02008031580000000605040302cc0074595800000605040310cb020080395800002c06050403cb020080515800000605042803cb020080715800000605040e03cb0200815158000006050403cb02c700845378
theorem c29t1m1d0g6ok : deepPass edgeQ29 12 c29t1m1d0g6 = true := by decide +kernel
def c29t1m1d0g7 := stateBlock edgeQ29 6 0x64c050403cb0200823158000006052f0403cb020080595800000605044a03cb0200821958000006050403cb021a00802958000006050403cb02190080415800000605040382cb0200814158
theorem c29t1m1d0g7ok : deepPass edgeQ29 12 c29t1m1d0g7 = true := by decide +kernel
def c29t1m1d0c := c29t1m1d0g0 ++ c29t1m1d0g1 ++ c29t1m1d0g2 ++ c29t1m1d0g3 ++ c29t1m1d0g4 ++ c29t1m1d0g5 ++ c29t1m1d0g6 ++ c29t1m1d0g7
theorem c29t1m1d0o : atFront (cliqueMark (storedInput ea29 false)) ea29 edgeQ29 1 0x0 1 c29t1m1d0c = false := by decide +kernel
theorem f29t1n1 : f29t1Run 0x0 1 = false := proveFront (xs:=c29t1m1d0c) (by simp only [c29t1m1d0c,deepAppend,c29t1m1d0g0ok,c29t1m1d0g1ok,c29t1m1d0g2ok,c29t1m1d0g3ok,c29t1m1d0g4ok,c29t1m1d0g5ok,c29t1m1d0g6ok,c29t1m1d0g7ok,Bool.and_self]) c29t1m1d0o

lemma f29t1 (base : Imp [] 0 13) : Excluded 12 ea29 1 := by
  refine useFront base member29 ready29 (binaryEarlier base shape29 unequal29 (bank14t1Valid base)) ?_ f29t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f29t1Run) f29t1n0 (addMask f29t1n1 (endMasks))
def bank16t1 := bank14t1 ++ [(4, 5), (10, 5)]
lemma bank16t1Valid (base : Imp [] 0 13) : ∀ p ∈ bank16t1, Excluded 12 p 1 := by
  apply finiteExtend (bank14t1Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f14t1 base
  · exact f29t1 base
def f30t1Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f30t1Cover : frontCover (storedInput ea30 false) bank16t1 f30t1Masks = true := by decide +kernel
noncomputable def f30t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea30 false)) [ea30] edgeQ30 0 12 0 h p
def c30t1m0d0g0 := stateBlock edgeQ30 4 0x60504037c02007471780000000605044a030200747178000000060504037f020071f17800000006053c04030200746978
theorem c30t1m0d0g0ok : deepPass edgeQ30 12 c30t1m0d0g0 = true := by decide +kernel
def c30t1m0d0g1 := stateBlock edgeQ30 4 0x6050403024500747978000006053c04033b0200846978000000060504037e0200746978000000064c050403020071f178
theorem c30t1m0d0g1ok : deepPass edgeQ30 12 c30t1m0d0g1 = true := by decide +kernel
def c30t1m0d0c := c30t1m0d0g0 ++ c30t1m0d0g1
theorem c30t1m0d0o : atFront (cliqueMark (storedInput ea30 false)) ea30 edgeQ30 0 0x0 1 c30t1m0d0c = false := by decide +kernel
theorem f30t1n0 : f30t1Run 0x0 1 = false := proveFront (xs:=c30t1m0d0c) (by simp only [c30t1m0d0c,deepAppend,c30t1m0d0g0ok,c30t1m0d0g1ok,Bool.and_self]) c30t1m0d0o

lemma f30t1 (base : Imp [] 0 13) : Excluded 12 ea30 0 := by
  refine useFront base member30 ready30 (unaryEarlier base shape30 (bank16t1Valid base)) ?_ f30t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f30t1Run) f30t1n0 (endMasks)
def f32t1Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f32t1Cover : frontCover (storedInput ea32 false) bank16t1 f32t1Masks = true := by decide +kernel
noncomputable def f32t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea32 false)) [ea32] edgeQ32 0 12 0 h p
def c32t1m0d0g0 := stateBlock edgeQ32 2 0x60504031112020084697800000006050403120200746978
theorem c32t1m0d0g0ok : deepPass edgeQ32 12 c32t1m0d0g0 = true := by decide +kernel
def c32t1m0d0g1 := stateBlock edgeQ32 3 0x6050403110c020083c978000000060504030c020073c97800000006050403100200700178
theorem c32t1m0d0g1ok : deepPass edgeQ32 12 c32t1m0d0g1 = true := by decide +kernel
def c32t1m0d0g2 := stateBlock edgeQ32 4 0x6050403021a0074817800000605040311021a00848178000006050403111002008001780000000605042803020073c978
theorem c32t1m0d0g2ok : deepPass edgeQ32 12 c32t1m0d0g2 = true := by decide +kernel
def c32t1m0d0g3 := stateBlock edgeQ32 3 0x60504280311020083c9780000002c060504030200746978000000062a0504030200700178
theorem c32t1m0d0g3ok : deepPass edgeQ32 12 c32t1m0d0g3 = true := by decide +kernel
def c32t1m0d0c := c32t1m0d0g0 ++ c32t1m0d0g1 ++ c32t1m0d0g2 ++ c32t1m0d0g3
theorem c32t1m0d0o : atFront (cliqueMark (storedInput ea32 false)) ea32 edgeQ32 0 0x0 1 c32t1m0d0c = false := by decide +kernel
theorem f32t1n0 : f32t1Run 0x0 1 = false := proveFront (xs:=c32t1m0d0c) (by simp only [c32t1m0d0c,deepAppend,c32t1m0d0g0ok,c32t1m0d0g1ok,c32t1m0d0g2ok,c32t1m0d0g3ok,Bool.and_self]) c32t1m0d0o

lemma f32t1 (base : Imp [] 0 13) : Excluded 12 ea32 0 := by
  refine useFront base member32 ready32 (unaryEarlier base shape32 (bank16t1Valid base)) ?_ f32t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f32t1Run) f32t1n0 (endMasks)
def f34t1Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f34t1Cover : frontCover (storedInput ea34 false) bank16t1 f34t1Masks = true := by decide +kernel
noncomputable def f34t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea34 false)) [ea34] edgeQ34 0 12 0 h p
theorem f34t1n0 : f34t1Run 0x0 1 = false := by decide +kernel
lemma f34t1 (base : Imp [] 0 13) : Excluded 12 ea34 0 := by
  refine useFront base member34 ready34 (unaryEarlier base shape34 (bank16t1Valid base)) ?_ f34t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f34t1Run) f34t1n0 (endMasks)
def f35t1Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f35t1Cover : frontCover (storedInput ea35 false) bank16t1 f35t1Masks = true := by decide +kernel
noncomputable def f35t1Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea35 false)) [ea35] edgeQ35 0 12 0 h p
theorem f35t1n0 : f35t1Run 0x0 1 = false := by decide +kernel
lemma f35t1 (base : Imp [] 0 13) : Excluded 12 ea35 0 := by
  refine useFront base member35 ready35 (unaryEarlier base shape35 (bank16t1Valid base)) ?_ f35t1Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f35t1Run) f35t1n0 (endMasks)
lemma stage1 (base : Imp [] 0 13) : ∀ p ∈ six, Excluded 12 p (remT (unaryE p) 1) := by
  intro e he
  simp only [six,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact f0t1 base
  · exact f1t1 base
  · exact f2t1 base
  · exact f3t1 base
  · exact f4t1 base
  · exact mirror5 _ _ (f2t1 base)
  · exact mirror6 _ _ (f1t1 base)
  · exact mirror7 _ _ (f3t1 base)
  · exact mirror8 _ _ (f4t1 base)
  · exact f9t1 base
  · exact f10t1 base
  · exact f11t1 base
  · exact mirror12 _ _ (f10t1 base)
  · exact mirror13 _ _ (f11t1 base)
  · exact f14t1 base
  · exact f15t1 base
  · exact f16t1 base
  · exact f17t1 base
  · exact f18t1 base
  · exact f19t1 base
  · exact mirror20 _ _ (f17t1 base)
  · exact mirror21 _ _ (f16t1 base)
  · exact mirror22 _ _ (f18t1 base)
  · exact mirror23 _ _ (f19t1 base)
  · exact f24t1 base
  · exact f25t1 base
  · exact f26t1 base
  · exact mirror27 _ _ (f25t1 base)
  · exact mirror28 _ _ (f26t1 base)
  · exact f29t1 base
  · exact f30t1 base
  · exact mirror31 _ _ (f30t1 base)
  · exact f32t1 base
  · exact mirror33 _ _ (f32t1 base)
  · exact f34t1 base
  · exact f35t1 base
def empty2 : List (ℕ × ℕ) := []
lemma empty2Valid (base : Imp [] 0 13) : ∀ p ∈ empty2, Excluded 12 p 2 := by simp [empty2]
def f2t2Masks : List (ℕ × ℕ) := [(0x200000000000000000000000004080040040000400080000000000,0),(0x2040000020040000000000000000000800008000000080000040,0),(0x0,1)]
lemma f2t2Cover : frontCover (storedInput ea2 false) empty2 f2t2Masks = true := by decide +kernel
noncomputable def f2t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea2 false)) [ea2] edgeQ2 0 12 2 h p
theorem f2t2n0 : f2t2Run 0x200000000000000000000000004080040040000400080000000000 0 = false := by decide +kernel
theorem f2t2n1 : f2t2Run 0x2040000020040000000000000000000800008000000080000040 0 = false := by decide +kernel
def c2t2m2d0g0 := stateBlock edgeQ2 3 0x50060504030200701d780000004e060504030200700d7800000000060504035102602578
theorem c2t2m2d0g0ok : deepPass edgeQ2 12 c2t2m2d0g0 = true := by decide +kernel
def c2t2m2d0g1 := stateBlock edgeQ2 9 0x605034d53110200802b580000060504034d021a00802b58000000d0060504030200749b58000000060403ce200200748b5800000006050403cf020074935800000605034d11021a00802b5800000006050403ce0200748b5800000006050403510200702578000000060504034f0200701578
theorem c2t2m2d0g1ok : deepPass edgeQ2 12 c2t2m2d0g1 = true := by decide +kernel
def c2t2m2d0c := c2t2m2d0g0 ++ c2t2m2d0g1
theorem c2t2m2d0o : atFront (cliqueMark (storedInput ea2 false)) ea2 edgeQ2 2 0x0 1 c2t2m2d0c = false := by decide +kernel
theorem f2t2n2 : f2t2Run 0x0 1 = false := proveFront (xs:=c2t2m2d0c) (by simp only [c2t2m2d0c,deepAppend,c2t2m2d0g0ok,c2t2m2d0g1ok,Bool.and_self]) c2t2m2d0o

lemma f2t2 (base : Imp [] 0 13) : Excluded 12 ea2 2 := by
  refine useFront base member2 ready2 (binaryEarlier base shape2 unequal2 (empty2Valid base)) ?_ f2t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f2t2Run) f2t2n0 (addMask f2t2n1 (addMask f2t2n2 (endMasks)))
def f17t2Masks : List (ℕ × ℕ) := [(0x200000000000000000000000000080000040000400000080000000,0),(0x2040000020040000000000004000040800008000080000000040,0),(0x0,1)]
lemma f17t2Cover : frontCover (storedInput ea17 false) empty2 f17t2Masks = true := by decide +kernel
noncomputable def f17t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea17 false)) [ea17] edgeQ17 0 12 2 h p
theorem f17t2n0 : f17t2Run 0x200000000000000000000000000080000040000400000080000000 0 = false := by decide +kernel
theorem f17t2n1 : f17t2Run 0x2040000020040000000000004000040800008000080000000040 0 = false := by decide +kernel
def c17t2m2d0g0 := stateBlock edgeQ17 3 0x605045d03020070dd7800000006055c0403020070d5780000000006050403025860ed78
theorem c17t2m2d0g0ok : deepPass edgeQ17 12 c17t2m2d0g0 = true := by decide +kernel
def c17t2m2d0g1 := stateBlock edgeQ17 20 0x6040320610200710b580000543006040320020081435800005406050311120200805358000054060403202d0200805b58000054060504032d0200805b5800005406050311100200803b5800005406050403100200803b58000054060403212002008113580000541c06054304030080fb58000054621c06050403008103580000001cd1060504030074a35800005406050403021a00802b5800000006050403610200710b58000000060504d203020074ab58000000d106050403020074a35800005406050311021a00802b58000000060503115e020070f3580000000605040302005870ed78000000060504035e020070f3580000000605040302570070e578
theorem c17t2m2d0g1ok : deepPass edgeQ17 12 c17t2m2d0g1 = true := by decide +kernel
def c17t2m2d0c := c17t2m2d0g0 ++ c17t2m2d0g1
theorem c17t2m2d0o : atFront (cliqueMark (storedInput ea17 false)) ea17 edgeQ17 2 0x0 1 c17t2m2d0c = false := by decide +kernel
theorem f17t2n2 : f17t2Run 0x0 1 = false := proveFront (xs:=c17t2m2d0c) (by simp only [c17t2m2d0c,deepAppend,c17t2m2d0g0ok,c17t2m2d0g1ok,Bool.and_self]) c17t2m2d0o

lemma f17t2 (base : Imp [] 0 13) : Excluded 12 ea17 2 := by
  refine useFront base member17 ready17 (binaryEarlier base shape17 unequal17 (empty2Valid base)) ?_ f17t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f17t2Run) f17t2n0 (addMask f17t2n1 (addMask f17t2n2 (endMasks)))
def bank0t2 := empty2 ++ [(0, 3), (1, 2), (6, 3), (7, 2)]
lemma bank0t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank0t2, Excluded 12 p 2 := by
  apply finiteExtend (empty2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f2t2 base
  · exact mirror5 _ _ (f2t2 base)
  · exact f17t2 base
  · exact mirror20 _ _ (f17t2 base)
def f1t2Masks : List (ℕ × ℕ) := [(0x200040000020040000000000004080000800008400000000000040,0),(0x2000000000000000000000000000000000000000080080000000,0),(0x0,1)]
lemma f1t2Cover : frontCover (storedInput ea1 false) bank0t2 f1t2Masks = true := by decide +kernel
noncomputable def f1t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea1 false)) [ea1] edgeQ1 0 12 2 h p
theorem f1t2n0 : f1t2Run 0x200040000020040000000000004080000800008400000000000040 0 = false := by decide +kernel
theorem f1t2n1 : f1t2Run 0x2000000000000000000000000000000000000000080080000000 0 = false := by decide +kernel
theorem f1t2n2 : f1t2Run 0x0 1 = false := by decide +kernel
lemma f1t2 (base : Imp [] 0 13) : Excluded 12 ea1 2 := by
  refine useFront base member1 ready1 (binaryEarlier base shape1 unequal1 (bank0t2Valid base)) ?_ f1t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f1t2Run) f1t2n0 (addMask f1t2n1 (addMask f1t2n2 (endMasks)))
def f16t2Masks : List (ℕ × ℕ) := [(0x202040000020040000000000004080000800008400080080000040,0),(0x0,1)]
lemma f16t2Cover : frontCover (storedInput ea16 false) bank0t2 f16t2Masks = true := by decide +kernel
noncomputable def f16t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea16 false)) [ea16] edgeQ16 0 12 2 h p
theorem f16t2n0 : f16t2Run 0x202040000020040000000000004080000800008400080080000040 0 = false := by decide +kernel
theorem f16t2n1 : f16t2Run 0x0 1 = false := by decide +kernel
lemma f16t2 (base : Imp [] 0 13) : Excluded 12 ea16 2 := by
  refine useFront base member16 ready16 (binaryEarlier base shape16 unequal16 (bank0t2Valid base)) ?_ f16t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f16t2Run) f16t2n0 (addMask f16t2n1 (endMasks))
def bank2t2 := bank0t2 ++ [(0, 2), (1, 3), (6, 2), (7, 3)]
lemma bank2t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank2t2, Excluded 12 p 2 := by
  apply finiteExtend (bank0t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f1t2 base
  · exact mirror6 _ _ (f1t2 base)
  · exact f16t2 base
  · exact mirror21 _ _ (f16t2 base)
def f3t2Masks : List (ℕ × ℕ) := [(0x202040000020000000000000004080000800008400080080000000,0),(0x0,1)]
lemma f3t2Cover : frontCover (storedInput ea3 false) bank2t2 f3t2Masks = true := by decide +kernel
noncomputable def f3t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea3 false)) [ea3] edgeQ3 0 12 2 h p
theorem f3t2n0 : f3t2Run 0x202040000020000000000000004080000800008400080080000000 0 = false := by decide +kernel
def c3t2m1d0g0 := stateBlock edgeQ3 2 0x60504870302007275780000000006050403028a628d78
theorem c3t2m1d0g0ok : deepPass edgeQ3 12 c3t2m1d0g0 = true := by decide +kernel
def c3t2m1d0g1 := stateBlock edgeQ3 6 0x605031110028b00803b58000000060504d403020074bb5800000006050403d3020074b35800000006050403028a00728d780000000605890403020072857800000006880504030200727d78
theorem c3t2m1d0g1ok : deepPass edgeQ3 12 c3t2m1d0g1 = true := by decide +kernel
def c3t2m1d0c := c3t2m1d0g0 ++ c3t2m1d0g1
theorem c3t2m1d0o : atFront (cliqueMark (storedInput ea3 false)) ea3 edgeQ3 2 0x0 1 c3t2m1d0c = false := by decide +kernel
theorem f3t2n1 : f3t2Run 0x0 1 = false := proveFront (xs:=c3t2m1d0c) (by simp only [c3t2m1d0c,deepAppend,c3t2m1d0g0ok,c3t2m1d0g1ok,Bool.and_self]) c3t2m1d0o

lemma f3t2 (base : Imp [] 0 13) : Excluded 12 ea3 2 := by
  refine useFront base member3 ready3 (binaryEarlier base shape3 unequal3 (bank2t2Valid base)) ?_ f3t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f3t2Run) f3t2n0 (addMask f3t2n1 (endMasks))
def f18t2Masks : List (ℕ × ℕ) := [(0x202040000020000000000000004080000800008400080080000000,0),(0x0,1)]
lemma f18t2Cover : frontCover (storedInput ea18 false) bank2t2 f18t2Masks = true := by decide +kernel
noncomputable def f18t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea18 false)) [ea18] edgeQ18 0 12 2 h p
theorem f18t2n0 : f18t2Run 0x202040000020000000000000004080000800008400080080000000 0 = false := by decide +kernel
theorem f18t2n1 : f18t2Run 0x0 1 = false := by decide +kernel
lemma f18t2 (base : Imp [] 0 13) : Excluded 12 ea18 2 := by
  refine useFront base member18 ready18 (binaryEarlier base shape18 unequal18 (bank2t2Valid base)) ?_ f18t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f18t2Run) f18t2n0 (addMask f18t2n1 (endMasks))
def bank4t2 := bank2t2 ++ [(0, 4), (1, 4), (6, 4), (7, 4)]
lemma bank4t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank4t2, Excluded 12 p 2 := by
  apply finiteExtend (bank2t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f3t2 base
  · exact mirror7 _ _ (f3t2 base)
  · exact f18t2 base
  · exact mirror22 _ _ (f18t2 base)
def f10t2Masks : List (ℕ × ℕ) := [(0x202040000020000000000000004000000800008400080000000000,0),(0x0,1)]
lemma f10t2Cover : frontCover (storedInput ea10 false) bank4t2 f10t2Masks = true := by decide +kernel
noncomputable def f10t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea10 false)) [ea10] edgeQ10 0 12 2 h p
theorem f10t2n0 : f10t2Run 0x202040000020000000000000004000000800008400080000000000 0 = false := by decide +kernel
theorem f10t2n1 : f10t2Run 0x0 1 = false := by decide +kernel
lemma f10t2 (base : Imp [] 0 13) : Excluded 12 ea10 2 := by
  refine useFront base member10 ready10 (binaryEarlier base shape10 unequal10 (bank4t2Valid base)) ?_ f10t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f10t2Run) f10t2n0 (addMask f10t2n1 (endMasks))
def f25t2Masks : List (ℕ × ℕ) := [(0x202000000020000000000000004000000800008400080000000000,0),(0x40000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f25t2Cover : frontCover (storedInput ea25 false) bank4t2 f25t2Masks = true := by decide +kernel
noncomputable def f25t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea25 false)) [ea25] edgeQ25 0 12 2 h p
theorem f25t2n0 : f25t2Run 0x202000000020000000000000004000000800008400080000000000 0 = false := by decide +kernel
theorem f25t2n1 : f25t2Run 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c25t2m2d0g0 := stateBlock edgeQ25 3 0x6050403730200720d780000000605047803020071fd7800000006050479030200720578
theorem c25t2m2d0g0ok : deepPass edgeQ25 12 c25t2m2d0g0 = true := by decide +kernel
def c25t2m2d0g1 := stateBlock edgeQ25 6 0x7a06050403020071fd780000060536047903020082057800000605360403730200820d780000060536047803020081fd780000005b06050403020072057800000074060504030200720d78
theorem c25t2m2d0g1ok : deepPass edgeQ25 12 c25t2m2d0g1 = true := by decide +kernel
def c25t2m2d0g2 := stateBlock edgeQ25 28 0x53604033b7e0200822b58000006053604037e0200822b5800000536044a033b0200821b580000053604033b7c0200821b58000006053604037c0200821b58000006053604034902008033580000060536040d030200804b58000006053604080d0200804b5800000605362304080200806b5800000006050403d7020074d358000000060536040319007043580000000504033bd6020074cb58000000060504087d02007223580000060536040e030200815358000006053604080e02008153580000063604032049020080335800005b0605360403020082057800007406053604030200820d7800000006050403d6020074cb5800000006050403d5020074c358000000810605040302007243580000000605040302008372157800000084060504030200724b580000000685050403020072535800000006050403028600725b5800000006050480030200723b580000000605047d03020072235800000006057b04030200721578
theorem c25t2m2d0g2ok : deepPass edgeQ25 12 c25t2m2d0g2 = true := by decide +kernel
def c25t2m2d0g3 := stateBlock edgeQ25 12 0x624053604080200804b5800000605362304030200806b5800000006050403d9020074e358000005360403483b0200818b58000000060504d803020074db580000060536040802190080435800000006040320d5020074c3580000053604033b7f02008233580000063604032082020081435800000605360403820200814358000005363c04033b0200822b58000006362f0403200200805b58
theorem c25t2m2d0g3ok : deepPass edgeQ25 12 c25t2m2d0g3 = true := by decide +kernel
def c25t2m2d0c := c25t2m2d0g0 ++ c25t2m2d0g1 ++ c25t2m2d0g2 ++ c25t2m2d0g3
theorem c25t2m2d0o : atFront (cliqueMark (storedInput ea25 false)) ea25 edgeQ25 2 0x0 1 c25t2m2d0c = false := by decide +kernel
theorem f25t2n2 : f25t2Run 0x0 1 = false := proveFront (xs:=c25t2m2d0c) (by simp only [c25t2m2d0c,deepAppend,c25t2m2d0g0ok,c25t2m2d0g1ok,c25t2m2d0g2ok,c25t2m2d0g3ok,Bool.and_self]) c25t2m2d0o

lemma f25t2 (base : Imp [] 0 13) : Excluded 12 ea25 2 := by
  refine useFront base member25 ready25 (binaryEarlier base shape25 unequal25 (bank4t2Valid base)) ?_ f25t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f25t2Run) f25t2n0 (addMask f25t2n1 (addMask f25t2n2 (endMasks)))
def bank6t2 := bank4t2 ++ [(2, 4), (3, 4), (8, 4), (9, 4)]
lemma bank6t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank6t2, Excluded 12 p 2 := by
  apply finiteExtend (bank4t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f10t2 base
  · exact mirror12 _ _ (f10t2 base)
  · exact f25t2 base
  · exact mirror27 _ _ (f25t2 base)
def f11t2Masks : List (ℕ × ℕ) := [(0x2040000020000000000000004000000000008400080000000000,0),(0x0,1)]
lemma f11t2Cover : frontCover (storedInput ea11 false) bank6t2 f11t2Masks = true := by decide +kernel
noncomputable def f11t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea11 false)) [ea11] edgeQ11 0 12 2 h p
theorem f11t2n0 : f11t2Run 0x2040000020000000000000004000000000008400080000000000 0 = false := by decide +kernel
theorem f11t2n1 : f11t2Run 0x0 1 = false := by decide +kernel
lemma f11t2 (base : Imp [] 0 13) : Excluded 12 ea11 2 := by
  refine useFront base member11 ready11 (binaryEarlier base shape11 unequal11 (bank6t2Valid base)) ?_ f11t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f11t2Run) f11t2n0 (addMask f11t2n1 (endMasks))
def f26t2Masks : List (ℕ × ℕ) := [(0x2040000020000000000000004000000000008400080000000000,0),(0x0,1)]
lemma f26t2Cover : frontCover (storedInput ea26 false) bank6t2 f26t2Masks = true := by decide +kernel
noncomputable def f26t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea26 false)) [ea26] edgeQ26 0 12 2 h p
theorem f26t2n0 : f26t2Run 0x2040000020000000000000004000000000008400080000000000 0 = false := by decide +kernel
theorem f26t2n1 : f26t2Run 0x0 1 = false := by decide +kernel
lemma f26t2 (base : Imp [] 0 13) : Excluded 12 ea26 2 := by
  refine useFront base member26 ready26 (binaryEarlier base shape26 unequal26 (bank6t2Valid base)) ?_ f26t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f26t2Run) f26t2n0 (addMask f26t2n1 (endMasks))
def bank8t2 := bank6t2 ++ [(2, 5), (3, 5), (8, 5), (9, 5)]
lemma bank8t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank8t2, Excluded 12 p 2 := by
  apply finiteExtend (bank6t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f11t2 base
  · exact mirror13 _ _ (f11t2 base)
  · exact f26t2 base
  · exact mirror28 _ _ (f26t2 base)
def f4t2Masks : List (ℕ × ℕ) := [(0x2040000000000000000000004000000000008400000000000000,0),(0x0,1)]
lemma f4t2Cover : frontCover (storedInput ea4 false) bank8t2 f4t2Masks = true := by decide +kernel
noncomputable def f4t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea4 false)) [ea4] edgeQ4 0 12 2 h p
theorem f4t2n0 : f4t2Run 0x2040000000000000000000004000000000008400000000000000 0 = false := by decide +kernel
theorem f4t2n1 : f4t2Run 0x0 1 = false := by decide +kernel
lemma f4t2 (base : Imp [] 0 13) : Excluded 12 ea4 2 := by
  refine useFront base member4 ready4 (binaryEarlier base shape4 unequal4 (bank8t2Valid base)) ?_ f4t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f4t2Run) f4t2n0 (addMask f4t2n1 (endMasks))
def f19t2Masks : List (ℕ × ℕ) := [(0x2040000000000000000000004000000000008400000000000000,0),(0x0,1)]
lemma f19t2Cover : frontCover (storedInput ea19 false) bank8t2 f19t2Masks = true := by decide +kernel
noncomputable def f19t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea19 false)) [ea19] edgeQ19 0 12 2 h p
theorem f19t2n0 : f19t2Run 0x2040000000000000000000004000000000008400000000000000 0 = false := by decide +kernel
theorem f19t2n1 : f19t2Run 0x0 1 = false := by decide +kernel
lemma f19t2 (base : Imp [] 0 13) : Excluded 12 ea19 2 := by
  refine useFront base member19 ready19 (binaryEarlier base shape19 unequal19 (bank8t2Valid base)) ?_ f19t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f19t2Run) f19t2n0 (addMask f19t2n1 (endMasks))
def bank10t2 := bank8t2 ++ [(0, 5), (1, 5), (6, 5), (7, 5)]
lemma bank10t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank10t2, Excluded 12 p 2 := by
  apply finiteExtend (bank8t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f4t2 base
  · exact mirror8 _ _ (f4t2 base)
  · exact f19t2 base
  · exact mirror23 _ _ (f19t2 base)
def f0t2Masks : List (ℕ × ℕ) := [(0x40000000000000000000004000000000000400000000000000,0),(0x0,1)]
lemma f0t2Cover : frontCover (storedInput ea0 false) bank10t2 f0t2Masks = true := by decide +kernel
noncomputable def f0t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea0 false)) [ea0] edgeQ0 0 12 2 h p
theorem f0t2n0 : f0t2Run 0x40000000000000000000004000000000000400000000000000 0 = false := by decide +kernel
theorem f0t2n1 : f0t2Run 0x0 1 = false := by decide +kernel
lemma f0t2 (base : Imp [] 0 13) : Excluded 12 ea0 2 := by
  refine useFront base member0 ready0 (binaryEarlier base shape0 unequal0 (bank10t2Valid base)) ?_ f0t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f0t2Run) f0t2n0 (addMask f0t2n1 (endMasks))
def f15t2Masks : List (ℕ × ℕ) := [(0x40000000000000000000004000000000000400000000000000,0),(0x0,1)]
lemma f15t2Cover : frontCover (storedInput ea15 false) bank10t2 f15t2Masks = true := by decide +kernel
noncomputable def f15t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea15 false)) [ea15] edgeQ15 0 12 2 h p
theorem f15t2n0 : f15t2Run 0x40000000000000000000004000000000000400000000000000 0 = false := by decide +kernel
theorem f15t2n1 : f15t2Run 0x0 1 = false := by decide +kernel
lemma f15t2 (base : Imp [] 0 13) : Excluded 12 ea15 2 := by
  refine useFront base member15 ready15 (binaryEarlier base shape15 unequal15 (bank10t2Valid base)) ?_ f15t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f15t2Run) f15t2n0 (addMask f15t2n1 (endMasks))
def bank12t2 := bank10t2 ++ [(0, 1), (6, 1)]
lemma bank12t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank12t2, Excluded 12 p 2 := by
  apply finiteExtend (bank10t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f0t2 base
  · exact f15t2 base
def f9t2Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000400000000000000,0),(0x0,1)]
lemma f9t2Cover : frontCover (storedInput ea9 false) bank12t2 f9t2Masks = true := by decide +kernel
noncomputable def f9t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea9 false)) [ea9] edgeQ9 0 12 2 h p
theorem f9t2n0 : f9t2Run 0x40000000000000000000000000000000000400000000000000 0 = false := by decide +kernel
def c9t2m1d0g0 := stateBlock edgeQ9 2 0x6050403ae0200736d780000000006050403ae00636d78
theorem c9t2m1d0g0ok : deepPass edgeQ9 12 c9t2m1d0g0 = true := by decide +kernel
def c9t2m1d0g1 := stateBlock edgeQ9 3 0x6050403b10200738578000000b0060504030200737d78000000af060504030200737578
theorem c9t2m1d0g1ok : deepPass edgeQ9 12 c9t2m1d0g1 = true := by decide +kernel
def c9t2m1d0c := c9t2m1d0g0 ++ c9t2m1d0g1
theorem c9t2m1d0o : atFront (cliqueMark (storedInput ea9 false)) ea9 edgeQ9 2 0x0 1 c9t2m1d0c = false := by decide +kernel
theorem f9t2n1 : f9t2Run 0x0 1 = false := proveFront (xs:=c9t2m1d0c) (by simp only [c9t2m1d0c,deepAppend,c9t2m1d0g0ok,c9t2m1d0g1ok,Bool.and_self]) c9t2m1d0o

lemma f9t2 (base : Imp [] 0 13) : Excluded 12 ea9 2 := by
  refine useFront base member9 ready9 (binaryEarlier base shape9 unequal9 (bank12t2Valid base)) ?_ f9t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f9t2Run) f9t2n0 (addMask f9t2n1 (endMasks))
def f24t2Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000400000000000000,0),(0x0,1)]
lemma f24t2Cover : frontCover (storedInput ea24 false) bank12t2 f24t2Masks = true := by decide +kernel
noncomputable def f24t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea24 false)) [ea24] edgeQ24 0 12 2 h p
theorem f24t2n0 : f24t2Run 0x40000000000000000000000000000000000400000000000000 0 = false := by decide +kernel
def c24t2m1d0g0 := stateBlock edgeQ24 4 0xba06050403020073dd7800000006b5050403020073d578000000000605040302b663e5780000000605b40403020073dd78
theorem c24t2m1d0g0ok : deepPass edgeQ24 12 c24t2m1d0g0 = true := by decide +kernel
def c24t2m1d0g1 := stateBlock edgeQ24 11 0xbd06050403020073e57800000006bb050403020073f35800000006050403be0200740358000000bc06050403020073fb58000000060504030200b673e5780000000605040302b80073ed78000000b30605040302b673e5780000b30605b40403020083dd780000b306b5050403020083d578000000b706050403020073ed78000000b906050403020073d578
theorem c24t2m1d0g1ok : deepPass edgeQ24 12 c24t2m1d0g1 = true := by decide +kernel
def c24t2m1d0g2 := stateBlock edgeQ24 33 0xb306050311021a00802b580000b306050403021a00802b580000b3060504030219008043580000b3060504080219008043580000b306050403020040826b580000b30604032002003f8263580000b306040320db020084f3580000b30605040302b80083ed780000b3060504030200b683e57800000006040320db020074f3580000b3060504037f02008233580000b3060403208202008143580000b3060504038202008143580000b3053c04033b0200822b580000b3062f0403200200805b580000b305044a033b0200821b580000001cc206050403007423580000b31c061b05040300811b580000b30605430403020080fb580000b31c06054304030080fb58000000df06050403020074eb58000000de06050403020074f3580000000605040302c300742b580000000504033bda020074eb580000b30504033b7f020082335800000006050403dd0200750358000000060504dc03020074fb5800000006050403db020074f358000000c20605040302007423580000000605bf04030200740b58000000060504c003020074135800000006050403da020074eb58000000000605040302c3642b58
theorem c24t2m1d0g2ok : deepPass edgeQ24 12 c24t2m1d0g2 = true := by decide +kernel
def c24t2m1d0c := c24t2m1d0g0 ++ c24t2m1d0g1 ++ c24t2m1d0g2
theorem c24t2m1d0o : atFront (cliqueMark (storedInput ea24 false)) ea24 edgeQ24 2 0x0 1 c24t2m1d0c = false := by decide +kernel
theorem f24t2n1 : f24t2Run 0x0 1 = false := proveFront (xs:=c24t2m1d0c) (by simp only [c24t2m1d0c,deepAppend,c24t2m1d0g0ok,c24t2m1d0g1ok,c24t2m1d0g2ok,Bool.and_self]) c24t2m1d0o

lemma f24t2 (base : Imp [] 0 13) : Excluded 12 ea24 2 := by
  refine useFront base member24 ready24 (binaryEarlier base shape24 unequal24 (bank12t2Valid base)) ?_ f24t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f24t2Run) f24t2n0 (addMask f24t2n1 (endMasks))
def bank14t2 := bank12t2 ++ [(2, 3), (8, 3)]
lemma bank14t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank14t2, Excluded 12 p 2 := by
  apply finiteExtend (bank12t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f9t2 base
  · exact f24t2 base
def f14t2Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000000000000,1)]
lemma f14t2Cover : frontCover (storedInput ea14 false) bank14t2 f14t2Masks = true := by decide +kernel
noncomputable def f14t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea14 false)) [ea14] edgeQ14 0 12 2 h p
theorem f14t2n0 : f14t2Run 0x40000000000000000000000000000000000000000000000000 1 = false := by decide +kernel
lemma f14t2 (base : Imp [] 0 13) : Excluded 12 ea14 2 := by
  refine useFront base member14 ready14 (binaryEarlier base shape14 unequal14 (bank14t2Valid base)) ?_ f14t2Cover ?_
  · exact ⟨(0x40000000000000000000000000000000000000000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f14t2Run) f14t2n0 (endMasks)
def f29t2Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f29t2Cover : frontCover (storedInput ea29 false) bank14t2 f29t2Masks = true := by decide +kernel
noncomputable def f29t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea29 false)) [ea29] edgeQ29 0 12 2 h p
theorem f29t2n0 : f29t2Run 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c29t2m1d0g0 := stateBlock edgeQ29 3 0x605040302c600744d780000000605040302c5007445780000000605040302c400743d78
theorem c29t2m1d0g0ok : deepPass edgeQ29 12 c29t2m1d0g0 = true := by decide +kernel
def c29t2m1d0g1 := stateBlock edgeQ29 17 0x2c06050311cb020080535800000624050408cb0200804b58000000e5060504030200753358000000e4060504030200752b5800000006050403cb023f726358000000e3060504030200752358000000e2060504030200751b580000000605040302e1007513580000000605040302e000750b5800000006050403cb0240726b580000000605040302cc00745b580000000605040302cd007463580000009106050403020074557800000006c80504030200744d780000000605ca04030200743d78000000060504c90302007445780000000605040302c700745578
theorem c29t2m1d0g1ok : deepPass edgeQ29 12 c29t2m1d0g1 = true := by decide +kernel
def c29t2m1d0g2 := stateBlock edgeQ29 18 0x605040312cb02008053580000060504032dcb0200805b580000062a050403cb0200803b580000000605044603cb02714b5800000605040b03cb0200806b580000060504080bcb0200806b5800002606050408cb020081535800000624050403cb0200804b5800000605230408cb0200806b580000000604032002e000750b580000000605031102cd007463580000000605040802cc00745b58000000060504030200e975435800000006050403e8020075135800000006050403e70200750b58000000e6060504030200753b58000006050403cb02c400843d78000006050403cb02c500844578
theorem c29t2m1d0g2ok : deepPass edgeQ29 12 c29t2m1d0g2 = true := by decide +kernel
def c29t2m1d0c := c29t2m1d0g0 ++ c29t2m1d0g1 ++ c29t2m1d0g2
theorem c29t2m1d0o : atFront (cliqueMark (storedInput ea29 false)) ea29 edgeQ29 2 0x0 1 c29t2m1d0c = false := by decide +kernel
theorem f29t2n1 : f29t2Run 0x0 1 = false := proveFront (xs:=c29t2m1d0c) (by simp only [c29t2m1d0c,deepAppend,c29t2m1d0g0ok,c29t2m1d0g1ok,c29t2m1d0g2ok,Bool.and_self]) c29t2m1d0o

lemma f29t2 (base : Imp [] 0 13) : Excluded 12 ea29 2 := by
  refine useFront base member29 ready29 (binaryEarlier base shape29 unequal29 (bank14t2Valid base)) ?_ f29t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f29t2Run) f29t2n0 (addMask f29t2n1 (endMasks))
def bank16t2 := bank14t2 ++ [(4, 5), (10, 5)]
lemma bank16t2Valid (base : Imp [] 0 13) : ∀ p ∈ bank16t2, Excluded 12 p 2 := by
  apply finiteExtend (bank14t2Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f14t2 base
  · exact f29t2 base
def f30t2Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f30t2Cover : frontCover (storedInput ea30 false) bank16t2 f30t2Masks = true := by decide +kernel
noncomputable def f30t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea30 false)) [ea30] edgeQ30 0 12 1 h p
def c30t2m0d0g0 := stateBlock edgeQ30 3 0x6050403480200747b7800000006053c04030200746b780000000605044a030200747378
theorem c30t2m0d0g0ok : deepPass edgeQ30 12 c30t2m0d0g0 = true := by decide +kernel
def c30t2m0d0g1 := stateBlock edgeQ30 4 0x64c050403020071f378000000060504037e0200746b78000000060504037f020071f378000000060504037c0200747378
theorem c30t2m0d0g1ok : deepPass edgeQ30 12 c30t2m0d0g1 = true := by decide +kernel
def c30t2m0d0g2 := stateBlock edgeQ30 7 0x504033b7f020071f3780000000504033b7e0200746b7800000005044a033b020074737800000006050403020040754b780000000504033b7c0200747378000000053c04033b0200746b7800000006050403024500747b78
theorem c30t2m0d0g2ok : deepPass edgeQ30 12 c30t2m0d0g2 = true := by decide +kernel
def c30t2m0d0g3 := stateBlock edgeQ30 13 0x60504033b7f020081f3780000000504033b020040754b78000006050403103b020080395800000605040d033b02008049580000060504033b7c0200847378000006050403483b0200847b780000060504033b024500847b78000006053c04033b0200846b7800000605044a033b0200847378000000050403483b0200747b780000000504033b024500747b780000004c0504033b020071f37800000006050403ea0200754b78
theorem c30t2m0d0g3ok : deepPass edgeQ30 12 c30t2m0d0g3 = true := by decide +kernel
def c30t2m0d0g4 := stateBlock edgeQ30 17 0x60504032d3b02008059580000062a0504033b02008039580000000f0a0504030200721958000006050428033b020080715800000006050403020100715158000006240504033b0200804958000006052304033b0200806958000006050403ea3b0200854b78000006052f04033b02008059580000060504033b7e0200846b780000060504033b020040854b78000006050429033b02008031580000060504030c3b020080715800000605040b033b02008069580000060504033b021a008029580000060504033b0219008041580000064c0504033b020081f378
theorem c30t2m0d0g4ok : deepPass edgeQ30 12 c30t2m0d0g4 = true := by decide +kernel
def c30t2m0d0c := c30t2m0d0g0 ++ c30t2m0d0g1 ++ c30t2m0d0g2 ++ c30t2m0d0g3 ++ c30t2m0d0g4
theorem c30t2m0d0o : atFront (cliqueMark (storedInput ea30 false)) ea30 edgeQ30 1 0x0 1 c30t2m0d0c = false := by decide +kernel
theorem f30t2n0 : f30t2Run 0x0 1 = false := proveFront (xs:=c30t2m0d0c) (by simp only [c30t2m0d0c,deepAppend,c30t2m0d0g0ok,c30t2m0d0g1ok,c30t2m0d0g2ok,c30t2m0d0g3ok,c30t2m0d0g4ok,Bool.and_self]) c30t2m0d0o

lemma f30t2 (base : Imp [] 0 13) : Excluded 12 ea30 1 := by
  refine useFront base member30 ready30 (unaryEarlier base shape30 (bank16t2Valid base)) ?_ f30t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f30t2Run) f30t2n0 (endMasks)
def f32t2Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f32t2Cover : frontCover (storedInput ea32 false) bank16t2 f32t2Masks = true := by decide +kernel
noncomputable def f32t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea32 false)) [ea32] edgeQ32 0 12 1 h p
def c32t2m0d0g0 := stateBlock edgeQ32 3 0x6050311120200746b780000000605040310020070037800000006050403120200746b78
theorem c32t2m0d0g0ok : deepPass edgeQ32 12 c32t2m0d0g0 = true := by decide +kernel
def c32t2m0d0g1 := stateBlock edgeQ32 4 0x62a05040302007003780000000605042803020073cb78000000060504030c020073cb7800000006050403021a00748378
theorem c32t2m0d0g1ok : deepPass edgeQ32 12 c32t2m0d0g1 = true := by decide +kernel
def c32t2m0d0g2 := stateBlock edgeQ32 4 0x2c060504030200746b7800000605040311120200846b78000000060503110c020073cb7800000006050311100200700378
theorem c32t2m0d0g2ok : deepPass edgeQ32 12 c32t2m0d0g2 = true := by decide +kernel
def c32t2m0d0g3 := stateBlock edgeQ32 5 0x605040353020074837800000605040311100200800378000006050403110c020083cb7800000006050311021a0074837800000605040311021a00848378
theorem c32t2m0d0g3ok : deepPass edgeQ32 12 c32t2m0d0g3 = true := by decide +kernel
def c32t2m0d0g4 := stateBlock edgeQ32 7 0x605040311020017855378000000060504031e0200755378000000060504030200177553780000002c060503110200746b7800000006050311020017755378000000062a05031102007003780000000605280311020073cb78
theorem c32t2m0d0g4ok : deepPass edgeQ32 12 c32t2m0d0g4 = true := by decide +kernel
def c32t2m0d0g5 := stateBlock edgeQ32 13 0x605031e110200755378000000140605330302007051580000060504290311020080315800000605040e031102008151580000060504031102310080695800000605040d0311020080495800002c06050403110200846b780000062a0504031102008003780000060504280311020083cb780000060504031e110200855378000000350605330302007039580000003406053303020070715800000006050353110200748378
theorem c32t2m0d0g5ok : deepPass edgeQ32 12 c32t2m0d0g5 = true := by decide +kernel
def c32t2m0d0g6 := stateBlock edgeQ32 13 0x62405040311020080495800000605230403110200806958000006050403110200408269580000060504031102003d8149580000064c05040311020082315800000605040311023a00805958000006052f04031102008059580000000605363303020070295800000605040311021900804158000006053c040311020082295800000605044a031102008219580000000605040302310070695800000605040353110200848378
theorem c32t2m0d0g6ok : deepPass edgeQ32 12 c32t2m0d0g6 = true := by decide +kernel
def c32t2m0d0c := c32t2m0d0g0 ++ c32t2m0d0g1 ++ c32t2m0d0g2 ++ c32t2m0d0g3 ++ c32t2m0d0g4 ++ c32t2m0d0g5 ++ c32t2m0d0g6
theorem c32t2m0d0o : atFront (cliqueMark (storedInput ea32 false)) ea32 edgeQ32 1 0x0 1 c32t2m0d0c = false := by decide +kernel
theorem f32t2n0 : f32t2Run 0x0 1 = false := proveFront (xs:=c32t2m0d0c) (by simp only [c32t2m0d0c,deepAppend,c32t2m0d0g0ok,c32t2m0d0g1ok,c32t2m0d0g2ok,c32t2m0d0g3ok,c32t2m0d0g4ok,c32t2m0d0g5ok,c32t2m0d0g6ok,Bool.and_self]) c32t2m0d0o

lemma f32t2 (base : Imp [] 0 13) : Excluded 12 ea32 1 := by
  refine useFront base member32 ready32 (unaryEarlier base shape32 (bank16t2Valid base)) ?_ f32t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f32t2Run) f32t2n0 (endMasks)
def f34t2Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f34t2Cover : frontCover (storedInput ea34 false) bank16t2 f34t2Masks = true := by decide +kernel
noncomputable def f34t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea34 false)) [ea34] edgeQ34 0 12 1 h p
def c34t2m0d0g0 := stateBlock edgeQ34 4 0x6050460030200748378000000060504035f0200756378000000061b0504030200747b7800000006054304030200755b78
theorem c34t2m0d0g0ok : deepPass edgeQ34 12 c34t2m0d0g0 = true := by decide +kernel
def c34t2m0d0g1 := stateBlock edgeQ34 7 0x1c060543040300755b78000000060504030200c1756b78000000ed060504030200747b78000000ec060504030200755b78000000eb060504030200756b780000005206050403020074837800000062060504030200756378
theorem c34t2m0d0g1ok : deepPass edgeQ34 12 c34t2m0d0g1 = true := by decide +kernel
def c34t2m0d0g2 := stateBlock edgeQ34 15 0xed1c0605040300747b78000000ec1c0605040300755b780000001c0605040300c1756b7800001c06053c0403020082295800001c060504030c020080715800001c0605040b03020080695800001c0605040312020080515800001c0605042903020080315800001c0605040e030200815158000000521c060504030074837800001c0605040d030200804958000000621c06050403007563780000001c060504035f007563780000001c0605046003007483780000001c061b05040300747b78
theorem c34t2m0d0g2ok : deepPass edgeQ34 12 c34t2m0d0g2 = true := by decide +kernel
def c34t2m0d0c := c34t2m0d0g0 ++ c34t2m0d0g1 ++ c34t2m0d0g2
theorem c34t2m0d0o : atFront (cliqueMark (storedInput ea34 false)) ea34 edgeQ34 1 0x0 1 c34t2m0d0c = false := by decide +kernel
theorem f34t2n0 : f34t2Run 0x0 1 = false := proveFront (xs:=c34t2m0d0c) (by simp only [c34t2m0d0c,deepAppend,c34t2m0d0g0ok,c34t2m0d0g1ok,c34t2m0d0g2ok,Bool.and_self]) c34t2m0d0o

lemma f34t2 (base : Imp [] 0 13) : Excluded 12 ea34 1 := by
  refine useFront base member34 ready34 (unaryEarlier base shape34 (bank16t2Valid base)) ?_ f34t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f34t2Run) f34t2n0 (endMasks)
def f35t2Masks : List (ℕ × ℕ) := [(0x0,1)]
lemma f35t2Cover : frontCover (storedInput ea35 false) bank16t2 f35t2Masks = true := by decide +kernel
noncomputable def f35t2Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea35 false)) [ea35] edgeQ35 0 12 1 h p
theorem f35t2n0 : f35t2Run 0x0 1 = false := by decide +kernel
lemma f35t2 (base : Imp [] 0 13) : Excluded 12 ea35 1 := by
  refine useFront base member35 ready35 (unaryEarlier base shape35 (bank16t2Valid base)) ?_ f35t2Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f35t2Run) f35t2n0 (endMasks)
lemma stage2 (base : Imp [] 0 13) : ∀ p ∈ six, Excluded 12 p (remT (unaryE p) 2) := by
  intro e he
  simp only [six,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact f0t2 base
  · exact f1t2 base
  · exact f2t2 base
  · exact f3t2 base
  · exact f4t2 base
  · exact mirror5 _ _ (f2t2 base)
  · exact mirror6 _ _ (f1t2 base)
  · exact mirror7 _ _ (f3t2 base)
  · exact mirror8 _ _ (f4t2 base)
  · exact f9t2 base
  · exact f10t2 base
  · exact f11t2 base
  · exact mirror12 _ _ (f10t2 base)
  · exact mirror13 _ _ (f11t2 base)
  · exact f14t2 base
  · exact f15t2 base
  · exact f16t2 base
  · exact f17t2 base
  · exact f18t2 base
  · exact f19t2 base
  · exact mirror20 _ _ (f17t2 base)
  · exact mirror21 _ _ (f16t2 base)
  · exact mirror22 _ _ (f18t2 base)
  · exact mirror23 _ _ (f19t2 base)
  · exact f24t2 base
  · exact f25t2 base
  · exact f26t2 base
  · exact mirror27 _ _ (f25t2 base)
  · exact mirror28 _ _ (f26t2 base)
  · exact f29t2 base
  · exact f30t2 base
  · exact mirror31 _ _ (f30t2 base)
  · exact f32t2 base
  · exact mirror33 _ _ (f32t2 base)
  · exact f34t2 base
  · exact f35t2 base
def empty3 : List (ℕ × ℕ) := []
lemma empty3Valid (base : Imp [] 0 13) : ∀ p ∈ empty3, Excluded 12 p 3 := by simp [empty3]
def f11t3Masks : List (ℕ × ℕ) := [(0x202040000020040000000000004080040840008400080080000040,1)]
lemma f11t3Cover : frontCover (storedInput ea11 false) empty3 f11t3Masks = true := by decide +kernel
noncomputable def f11t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea11 false)) [ea11] edgeQ11 0 12 3 h p
theorem f11t3n0 : f11t3Run 0x202040000020040000000000004080040840008400080080000040 1 = false := by decide +kernel
lemma f11t3 (base : Imp [] 0 13) : Excluded 12 ea11 3 := by
  refine useFront base member11 ready11 (binaryEarlier base shape11 unequal11 (empty3Valid base)) ?_ f11t3Cover ?_
  · exact ⟨(0x202040000020040000000000004080040840008400080080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f11t3Run) f11t3n0 (endMasks)
def f26t3Masks : List (ℕ × ℕ) := [(0x202040000020040000000000004080040840008400080080000040,1)]
lemma f26t3Cover : frontCover (storedInput ea26 false) empty3 f26t3Masks = true := by decide +kernel
noncomputable def f26t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea26 false)) [ea26] edgeQ26 0 12 3 h p
theorem f26t3n0 : f26t3Run 0x202040000020040000000000004080040840008400080080000040 1 = false := by decide +kernel
lemma f26t3 (base : Imp [] 0 13) : Excluded 12 ea26 3 := by
  refine useFront base member26 ready26 (binaryEarlier base shape26 unequal26 (empty3Valid base)) ?_ f26t3Cover ?_
  · exact ⟨(0x202040000020040000000000004080040840008400080080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f26t3Run) f26t3n0 (endMasks)
def bank0t3 := empty3 ++ [(2, 5), (3, 5), (8, 5), (9, 5)]
lemma bank0t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank0t3, Excluded 12 p 3 := by
  apply finiteExtend (empty3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f11t3 base
  · exact mirror13 _ _ (f11t3 base)
  · exact f26t3 base
  · exact mirror28 _ _ (f26t3 base)
def f2t3Masks : List (ℕ × ℕ) := [(0x202040000000040000000000004080040840008400000080000040,1)]
lemma f2t3Cover : frontCover (storedInput ea2 false) bank0t3 f2t3Masks = true := by decide +kernel
noncomputable def f2t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea2 false)) [ea2] edgeQ2 0 12 3 h p
theorem f2t3n0 : f2t3Run 0x202040000000040000000000004080040840008400000080000040 1 = false := by decide +kernel
lemma f2t3 (base : Imp [] 0 13) : Excluded 12 ea2 3 := by
  refine useFront base member2 ready2 (binaryEarlier base shape2 unequal2 (bank0t3Valid base)) ?_ f2t3Cover ?_
  · exact ⟨(0x202040000000040000000000004080040840008400000080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f2t3Run) f2t3n0 (endMasks)
def f17t3Masks : List (ℕ × ℕ) := [(0x202040000000040000000000004080040840008400000080000040,1)]
lemma f17t3Cover : frontCover (storedInput ea17 false) bank0t3 f17t3Masks = true := by decide +kernel
noncomputable def f17t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea17 false)) [ea17] edgeQ17 0 12 3 h p
theorem f17t3n0 : f17t3Run 0x202040000000040000000000004080040840008400000080000040 1 = false := by decide +kernel
lemma f17t3 (base : Imp [] 0 13) : Excluded 12 ea17 3 := by
  refine useFront base member17 ready17 (binaryEarlier base shape17 unequal17 (bank0t3Valid base)) ?_ f17t3Cover ?_
  · exact ⟨(0x202040000000040000000000004080040840008400000080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f17t3Run) f17t3n0 (endMasks)
def bank2t3 := bank0t3 ++ [(0, 3), (1, 2), (6, 3), (7, 2)]
lemma bank2t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank2t3, Excluded 12 p 3 := by
  apply finiteExtend (bank0t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f2t3 base
  · exact mirror5 _ _ (f2t3 base)
  · exact f17t3 base
  · exact mirror20 _ _ (f17t3 base)
def f4t3Masks : List (ℕ × ℕ) := [(0x202040000000040000000000004080000800008400000080000040,1)]
lemma f4t3Cover : frontCover (storedInput ea4 false) bank2t3 f4t3Masks = true := by decide +kernel
noncomputable def f4t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea4 false)) [ea4] edgeQ4 0 12 3 h p
theorem f4t3n0 : f4t3Run 0x202040000000040000000000004080000800008400000080000040 1 = false := by decide +kernel
lemma f4t3 (base : Imp [] 0 13) : Excluded 12 ea4 3 := by
  refine useFront base member4 ready4 (binaryEarlier base shape4 unequal4 (bank2t3Valid base)) ?_ f4t3Cover ?_
  · exact ⟨(0x202040000000040000000000004080000800008400000080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f4t3Run) f4t3n0 (endMasks)
def f19t3Masks : List (ℕ × ℕ) := [(0x202040000000040000000000004080000800008400000080000040,1)]
lemma f19t3Cover : frontCover (storedInput ea19 false) bank2t3 f19t3Masks = true := by decide +kernel
noncomputable def f19t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea19 false)) [ea19] edgeQ19 0 12 3 h p
theorem f19t3n0 : f19t3Run 0x202040000000040000000000004080000800008400000080000040 1 = false := by decide +kernel
lemma f19t3 (base : Imp [] 0 13) : Excluded 12 ea19 3 := by
  refine useFront base member19 ready19 (binaryEarlier base shape19 unequal19 (bank2t3Valid base)) ?_ f19t3Cover ?_
  · exact ⟨(0x202040000000040000000000004080000800008400000080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f19t3Run) f19t3n0 (endMasks)
def bank4t3 := bank2t3 ++ [(0, 5), (1, 5), (6, 5), (7, 5)]
lemma bank4t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank4t3, Excluded 12 p 3 := by
  apply finiteExtend (bank2t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f4t3 base
  · exact mirror8 _ _ (f4t3 base)
  · exact f19t3 base
  · exact mirror23 _ _ (f19t3 base)
def f3t3Masks : List (ℕ × ℕ) := [(0x200040000000040000000000004080000800000400000080000040,1)]
lemma f3t3Cover : frontCover (storedInput ea3 false) bank4t3 f3t3Masks = true := by decide +kernel
noncomputable def f3t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea3 false)) [ea3] edgeQ3 0 12 3 h p
theorem f3t3n0 : f3t3Run 0x200040000000040000000000004080000800000400000080000040 1 = false := by decide +kernel
lemma f3t3 (base : Imp [] 0 13) : Excluded 12 ea3 3 := by
  refine useFront base member3 ready3 (binaryEarlier base shape3 unequal3 (bank4t3Valid base)) ?_ f3t3Cover ?_
  · exact ⟨(0x200040000000040000000000004080000800000400000080000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f3t3Run) f3t3n0 (endMasks)
def f18t3Masks : List (ℕ × ℕ) := [(0x200048001000040000000000004080002800020400000080002040,1)]
lemma f18t3Cover : frontCover (storedInput ea18 true) bank4t3 f18t3Masks = true := by decide +kernel
noncomputable def f18t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea18 true)) [ea18] edgeQ18 0 12 3 h p
theorem f18t3n0 : f18t3Run 0x200048001000040000000000004080002800020400000080002040 1 = false := by decide +kernel
lemma f18t3 (base : Imp [] 0 13) : Excluded 12 ea18 3 := by
  refine useFront base member18 ready18 (binaryEarlier base shape18 unequal18 (bank4t3Valid base)) ?_ f18t3Cover ?_
  · exact ⟨(0x200048001000040000000000004080002800020400000080002040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f18t3Run) f18t3n0 (endMasks)
def bank6t3 := bank4t3 ++ [(0, 4), (1, 4), (6, 4), (7, 4)]
lemma bank6t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank6t3, Excluded 12 p 3 := by
  apply finiteExtend (bank4t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f3t3 base
  · exact mirror7 _ _ (f3t3 base)
  · exact f18t3 base
  · exact mirror22 _ _ (f18t3 base)
def f10t3Masks : List (ℕ × ℕ) := [(0x200040000000040000000000004000000800000400000000000040,1)]
lemma f10t3Cover : frontCover (storedInput ea10 false) bank6t3 f10t3Masks = true := by decide +kernel
noncomputable def f10t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea10 false)) [ea10] edgeQ10 0 12 3 h p
theorem f10t3n0 : f10t3Run 0x200040000000040000000000004000000800000400000000000040 1 = false := by decide +kernel
lemma f10t3 (base : Imp [] 0 13) : Excluded 12 ea10 3 := by
  refine useFront base member10 ready10 (binaryEarlier base shape10 unequal10 (bank6t3Valid base)) ?_ f10t3Cover ?_
  · exact ⟨(0x200040000000040000000000004000000800000400000000000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f10t3Run) f10t3n0 (endMasks)
def f25t3Masks : List (ℕ × ℕ) := [(0x200040000000040000000000004000000800000400000000000040,1)]
lemma f25t3Cover : frontCover (storedInput ea25 false) bank6t3 f25t3Masks = true := by decide +kernel
noncomputable def f25t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea25 false)) [ea25] edgeQ25 0 12 3 h p
theorem f25t3n0 : f25t3Run 0x200040000000040000000000004000000800000400000000000040 1 = false := by decide +kernel
lemma f25t3 (base : Imp [] 0 13) : Excluded 12 ea25 3 := by
  refine useFront base member25 ready25 (binaryEarlier base shape25 unequal25 (bank6t3Valid base)) ?_ f25t3Cover ?_
  · exact ⟨(0x200040000000040000000000004000000800000400000000000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f25t3Run) f25t3n0 (endMasks)
def bank8t3 := bank6t3 ++ [(2, 4), (3, 4), (8, 4), (9, 4)]
lemma bank8t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank8t3, Excluded 12 p 3 := by
  apply finiteExtend (bank6t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f10t3 base
  · exact mirror12 _ _ (f10t3 base)
  · exact f25t3 base
  · exact mirror27 _ _ (f25t3 base)
def f1t3Masks : List (ℕ × ℕ) := [(0x40000000040000000000004000000000000400000000000040,1)]
lemma f1t3Cover : frontCover (storedInput ea1 false) bank8t3 f1t3Masks = true := by decide +kernel
noncomputable def f1t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea1 false)) [ea1] edgeQ1 0 12 3 h p
theorem f1t3n0 : f1t3Run 0x40000000040000000000004000000000000400000000000040 1 = false := by decide +kernel
lemma f1t3 (base : Imp [] 0 13) : Excluded 12 ea1 3 := by
  refine useFront base member1 ready1 (binaryEarlier base shape1 unequal1 (bank8t3Valid base)) ?_ f1t3Cover ?_
  · exact ⟨(0x40000000040000000000004000000000000400000000000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f1t3Run) f1t3n0 (endMasks)
def f16t3Masks : List (ℕ × ℕ) := [(0x50000100040000000010204000100020000400000000000040,1)]
lemma f16t3Cover : frontCover (storedInput ea16 true) bank8t3 f16t3Masks = true := by decide +kernel
noncomputable def f16t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea16 true)) [ea16] edgeQ16 0 12 3 h p
theorem f16t3n0 : f16t3Run 0x50000100040000000010204000100020000400000000000040 1 = false := by decide +kernel
lemma f16t3 (base : Imp [] 0 13) : Excluded 12 ea16 3 := by
  refine useFront base member16 ready16 (binaryEarlier base shape16 unequal16 (bank8t3Valid base)) ?_ f16t3Cover ?_
  · exact ⟨(0x50000100040000000010204000100020000400000000000040,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f16t3Run) f16t3n0 (endMasks)
def bank10t3 := bank8t3 ++ [(0, 2), (1, 3), (6, 2), (7, 3)]
lemma bank10t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank10t3, Excluded 12 p 3 := by
  apply finiteExtend (bank8t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact f1t3 base
  · exact mirror6 _ _ (f1t3 base)
  · exact f16t3 base
  · exact mirror21 _ _ (f16t3 base)
def f0t3Masks : List (ℕ × ℕ) := [(0x41020000010002000000004000000000000404000040000000,1)]
lemma f0t3Cover : frontCover (storedInput ea0 true) bank10t3 f0t3Masks = true := by decide +kernel
noncomputable def f0t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea0 true)) [ea0] edgeQ0 0 12 3 h p
theorem f0t3n0 : f0t3Run 0x41020000010002000000004000000000000404000040000000 1 = false := by decide +kernel
lemma f0t3 (base : Imp [] 0 13) : Excluded 12 ea0 3 := by
  refine useFront base member0 ready0 (binaryEarlier base shape0 unequal0 (bank10t3Valid base)) ?_ f0t3Cover ?_
  · exact ⟨(0x41020000010002000000004000000000000404000040000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f0t3Run) f0t3n0 (endMasks)
def f15t3Masks : List (ℕ × ℕ) := [(0x40000000000000000000004000000000000400000000000000,1)]
lemma f15t3Cover : frontCover (storedInput ea15 false) bank10t3 f15t3Masks = true := by decide +kernel
noncomputable def f15t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea15 false)) [ea15] edgeQ15 0 12 3 h p
theorem f15t3n0 : f15t3Run 0x40000000000000000000004000000000000400000000000000 1 = false := by decide +kernel
lemma f15t3 (base : Imp [] 0 13) : Excluded 12 ea15 3 := by
  refine useFront base member15 ready15 (binaryEarlier base shape15 unequal15 (bank10t3Valid base)) ?_ f15t3Cover ?_
  · exact ⟨(0x40000000000000000000004000000000000400000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f15t3Run) f15t3n0 (endMasks)
def bank12t3 := bank10t3 ++ [(0, 1), (6, 1)]
lemma bank12t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank12t3, Excluded 12 p 3 := by
  apply finiteExtend (bank10t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f0t3 base
  · exact f15t3 base
def f9t3Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000400000000000000,1)]
lemma f9t3Cover : frontCover (storedInput ea9 false) bank12t3 f9t3Masks = true := by decide +kernel
noncomputable def f9t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea9 false)) [ea9] edgeQ9 0 12 3 h p
theorem f9t3n0 : f9t3Run 0x40000000000000000000000000000000000400000000000000 1 = false := by decide +kernel
lemma f9t3 (base : Imp [] 0 13) : Excluded 12 ea9 3 := by
  refine useFront base member9 ready9 (binaryEarlier base shape9 unequal9 (bank12t3Valid base)) ?_ f9t3Cover ?_
  · exact ⟨(0x40000000000000000000000000000000000400000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f9t3Run) f9t3n0 (endMasks)
def f24t3Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000400000000000000,1)]
lemma f24t3Cover : frontCover (storedInput ea24 false) bank12t3 f24t3Masks = true := by decide +kernel
noncomputable def f24t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea24 false)) [ea24] edgeQ24 0 12 3 h p
theorem f24t3n0 : f24t3Run 0x40000000000000000000000000000000000400000000000000 1 = false := by decide +kernel
lemma f24t3 (base : Imp [] 0 13) : Excluded 12 ea24 3 := by
  refine useFront base member24 ready24 (binaryEarlier base shape24 unequal24 (bank12t3Valid base)) ?_ f24t3Cover ?_
  · exact ⟨(0x40000000000000000000000000000000000400000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f24t3Run) f24t3n0 (endMasks)
def bank14t3 := bank12t3 ++ [(2, 3), (8, 3)]
lemma bank14t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank14t3, Excluded 12 p 3 := by
  apply finiteExtend (bank12t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f9t3 base
  · exact f24t3 base
def f14t3Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000000000000,1)]
lemma f14t3Cover : frontCover (storedInput ea14 false) bank14t3 f14t3Masks = true := by decide +kernel
noncomputable def f14t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea14 false)) [ea14] edgeQ14 0 12 3 h p
theorem f14t3n0 : f14t3Run 0x40000000000000000000000000000000000000000000000000 1 = false := by decide +kernel
lemma f14t3 (base : Imp [] 0 13) : Excluded 12 ea14 3 := by
  refine useFront base member14 ready14 (binaryEarlier base shape14 unequal14 (bank14t3Valid base)) ?_ f14t3Cover ?_
  · exact ⟨(0x40000000000000000000000000000000000000000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f14t3Run) f14t3n0 (endMasks)
def f29t3Masks : List (ℕ × ℕ) := [(0x40000000000000000000000000000000000000000000000000,1)]
lemma f29t3Cover : frontCover (storedInput ea29 false) bank14t3 f29t3Masks = true := by decide +kernel
noncomputable def f29t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea29 false)) [ea29] edgeQ29 0 12 3 h p
theorem f29t3n0 : f29t3Run 0x40000000000000000000000000000000000000000000000000 1 = false := by decide +kernel
lemma f29t3 (base : Imp [] 0 13) : Excluded 12 ea29 3 := by
  refine useFront base member29 ready29 (binaryEarlier base shape29 unequal29 (bank14t3Valid base)) ?_ f29t3Cover ?_
  · exact ⟨(0x40000000000000000000000000000000000000000000000000,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f29t3Run) f29t3n0 (endMasks)
def bank16t3 := bank14t3 ++ [(4, 5), (10, 5)]
lemma bank16t3Valid (base : Imp [] 0 13) : ∀ p ∈ bank16t3, Excluded 12 p 3 := by
  apply finiteExtend (bank14t3Valid base)
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact f14t3 base
  · exact f29t3 base
def f30t3Masks : List (ℕ × ℕ) := [(0x20000200000000000020,0),(0x100000080000000000000000000000000000000000000000000000,0),(0x10000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f30t3Cover : frontCover (storedInput ea30 true) bank16t3 f30t3Masks = true := by decide +kernel
noncomputable def f30t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea30 true)) [ea30] edgeQ30 0 12 2 h p
theorem f30t3n0 : f30t3Run 0x20000200000000000020 0 = false := by decide +kernel
theorem f30t3n1 : f30t3Run 0x100000080000000000000000000000000000000000000000000000 0 = false := by decide +kernel
theorem f30t3n2 : f30t3Run 0x10000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c30t3m3d0g0 := stateBlock edgeQ30 53 0x2a050311070200703b58000000042903200702007033580000000504290307020070335800000005280311070200707358000000050428030702007073580000000504030702010071535800000005040e030702007153580000000a050403270200721b5800000605040d03070200804b580000000503110c0702007073580000060503110c0702008073580000060504030c07020080735800000605040b03070200806b580000060504080b070200806b5800000026050403070200715358000000050425080702007153580000000605042503020071535800000024050403070200704b5800000024050408070200704b5800000005230408070200706b58000000220a0504030200718b58000000040321200702007113580000001f0a0504030200726b580000000504031e070200743358000000060504031d0200711b580000001b050403070200711b580000001c1b0504030700711b5800000005040307021a00702b5800000605031107021a00802b58000000050403070219007043580000000a050403020018726b5800000005031107020017743358000000050403070200177433580000000a05160403020072335800000006050403150200714358000000140a0504030200722b5800000005031107021300705358000000060504030213007053580000000503111207020070535800000005031110070200703b5800000005040310070200703b580000000f0a0504030200721b58000000060504080201007153580000000504080e07020071535800000005040d03070200704b580000000504080d070200704b580000060504080d070200804b580000000504030c07020070735800000005040b03070200706b580000000504080b070200706b580000000a050403020900718b580000000504080702010071535800000006050403020100715358
theorem c30t3m3d0g0ok : deepPass edgeQ30 12 c30t3m3d0g0 = true := by decide +kernel
def c30t3m3d0g1 := stateBlock edgeQ30 17 0x3004032007020071435800000004031520070200714358000000060403152002007143580000002f040320070200705b58000000052f0403070200705b580000062f040320070200805b5800000005040307021300705358000000060503110213007053580000000504031207020070535800000005042e03070200722b580000000a05042e030200722b580000000403202d070200705b5800000605031110070200803b5800000605040310070200803b580000002c0503110702007053580000002c050403070200705358000000060504032b0200705358
theorem c30t3m3d0g1ok : deepPass edgeQ30 12 c30t3m3d0g1 = true := by decide +kernel
def c30t3m3d0c := c30t3m3d0g0 ++ c30t3m3d0g1
theorem c30t3m3d0o : atFront (cliqueMark (storedInput ea30 true)) ea30 edgeQ30 2 0x0 1 c30t3m3d0c = false := by decide +kernel
theorem f30t3n3 : f30t3Run 0x0 1 = false := proveFront (xs:=c30t3m3d0c) (by simp only [c30t3m3d0c,deepAppend,c30t3m3d0g0ok,c30t3m3d0g1ok,Bool.and_self]) c30t3m3d0o

lemma f30t3 (base : Imp [] 0 13) : Excluded 12 ea30 2 := by
  refine useFront base member30 ready30 (unaryEarlier base shape30 (bank16t3Valid base)) ?_ f30t3Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f30t3Run) f30t3n0 (addMask f30t3n1 (addMask f30t3n2 (addMask f30t3n3 (endMasks))))
def f32t3Masks : List (ℕ × ℕ) := [(0x2000000000000000000040000020,0),(0x20000000000002000000000,0),(0x1000000000000000000000000000000000000000000000000000,0),(0x0,1)]
lemma f32t3Cover : frontCover (storedInput ea32 true) bank16t3 f32t3Masks = true := by decide +kernel
noncomputable def f32t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea32 true)) [ea32] edgeQ32 0 12 2 h p
theorem f32t3n0 : f32t3Run 0x2000000000000000000040000020 0 = false := by decide +kernel
theorem f32t3n1 : f32t3Run 0x20000000000002000000000 0 = false := by decide +kernel
theorem f32t3n2 : f32t3Run 0x1000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
def c32t3m3d0g0 := stateBlock edgeQ32 48 0x605040832023100806b5800000006050332380200707358000000260605033202007153580000002606050832020071535800000006240508320200704b580000260605040832020081535800000006053704030200706b5800000006053704080200706b58000005040332483b0200818b580000060403322120020081135800000006053603320200702b58000000060547033202007043580000060504470832020080435800000006054603320200714b5800000006050332024500718b58000000060503320244007113580000000605430332020070fb580000000605040342020070635800000006053303024100702b58000000060503320219007043580000060504083202190080435800000006050332020040726b580000000603322002003f7263580000000605033202003f7263580000000605330302003e7433580000000605033202003d714b58000000053c03323b0200722b5800000006050403023a00705b58000000062f0332200200705b5800000035060503320200703b5800000006050403390200705b580000003406050332020070735800000006050e033202007153580000000605080e32020071535800000006050d03320200704b580000000605080d320200704b5800000006050332023100706b5800000006050408023100706b580000000605330338020070735800000006052308320200706b5800000006053708320200706b58000000140605330302007053580000000605080b320200706b5800000006053633030200702b5800000035060533030200703b580000003406053303020070735800000006050832023100706b5800000006050403023100706b58
theorem c32t3m3d0g0ok : deepPass edgeQ32 12 c32t3m3d0g0 = true := by decide +kernel
def c32t3m3d0g1 := stateBlock edgeQ32 20 0x4c050403323b020082335800000006033220023a00705b5800000006052f03320200705b5800000014060503320200705358000000060332202d0200705b58000000060503322d0200705b5800000604033220023a00805b5800000006033932200200705b580000000605332e0302007053580000000605334b030200703b58000000054a03323b0200721b5800000006054a03320200721b58000000062903322002007033580000000603322049020070335800000605040e033202008153580000060504080e32020081535800000605040d03320200804b580000060504080d320200804b5800000006050b03320200706b5800000605040332023100806b58
theorem c32t3m3d0g1ok : deepPass edgeQ32 12 c32t3m3d0g1 = true := by decide +kernel
def c32t3m3d0c := c32t3m3d0g0 ++ c32t3m3d0g1
theorem c32t3m3d0o : atFront (cliqueMark (storedInput ea32 true)) ea32 edgeQ32 2 0x0 1 c32t3m3d0c = false := by decide +kernel
theorem f32t3n3 : f32t3Run 0x0 1 = false := proveFront (xs:=c32t3m3d0c) (by simp only [c32t3m3d0c,deepAppend,c32t3m3d0g0ok,c32t3m3d0g1ok,Bool.and_self]) c32t3m3d0o

lemma f32t3 (base : Imp [] 0 13) : Excluded 12 ea32 2 := by
  refine useFront base member32 ready32 (unaryEarlier base shape32 (bank16t3Valid base)) ?_ f32t3Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f32t3Run) f32t3n0 (addMask f32t3n1 (addMask f32t3n2 (addMask f32t3n3 (endMasks))))
def f34t3Masks : List (ℕ × ℕ) := [(0x4000000000000000000000000000000010000000000001020,0),(0x800000000000000000000001000000000000000000000,0),(0x0,1)]
lemma f34t3Cover : frontCover (storedInput ea34 true) bank16t3 f34t3Masks = true := by decide +kernel
noncomputable def f34t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea34 true)) [ea34] edgeQ34 0 12 2 h p
theorem f34t3n0 : f34t3Run 0x4000000000000000000000000000000010000000000001020 0 = false := by decide +kernel
theorem f34t3n1 : f34t3Run 0x800000000000000000000001000000000000000000000 0 = false := by decide +kernel
theorem f34t3n2 : f34t3Run 0x0 1 = false := by decide +kernel
lemma f34t3 (base : Imp [] 0 13) : Excluded 12 ea34 2 := by
  refine useFront base member34 ready34 (unaryEarlier base shape34 (bank16t3Valid base)) ?_ f34t3Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f34t3Run) f34t3n0 (addMask f34t3n1 (addMask f34t3n2 (endMasks)))
def f35t3Masks : List (ℕ × ℕ) := [(0x10000100000000000010200000100020,0),(0x0,1)]
lemma f35t3Cover : frontCover (storedInput ea35 true) bank16t3 f35t3Masks = true := by decide +kernel
noncomputable def f35t3Run (h p : ℕ) := markedChk (cliqueMark (storedInput ea35 true)) [ea35] edgeQ35 0 12 2 h p
theorem f35t3n0 : f35t3Run 0x10000100000000000010200000100020 0 = false := by decide +kernel
theorem f35t3n1 : f35t3Run 0x0 1 = false := by decide +kernel
lemma f35t3 (base : Imp [] 0 13) : Excluded 12 ea35 2 := by
  refine useFront base member35 ready35 (unaryEarlier base shape35 (bank16t3Valid base)) ?_ f35t3Cover ?_
  · exact ⟨(0x0,1),by decide +kernel,rfl⟩
  · exact addMask (f:=f35t3Run) f35t3n0 (addMask f35t3n1 (endMasks))
lemma stage3 (base : Imp [] 0 13) : ∀ p ∈ six, Excluded 12 p (remT (unaryE p) 3) := by
  intro e he
  simp only [six,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact f0t3 base
  · exact f1t3 base
  · exact f2t3 base
  · exact f3t3 base
  · exact f4t3 base
  · exact mirror5 _ _ (f2t3 base)
  · exact mirror6 _ _ (f1t3 base)
  · exact mirror7 _ _ (f3t3 base)
  · exact mirror8 _ _ (f4t3 base)
  · exact f9t3 base
  · exact f10t3 base
  · exact f11t3 base
  · exact mirror12 _ _ (f10t3 base)
  · exact mirror13 _ _ (f11t3 base)
  · exact f14t3 base
  · exact f15t3 base
  · exact f16t3 base
  · exact f17t3 base
  · exact f18t3 base
  · exact f19t3 base
  · exact mirror20 _ _ (f17t3 base)
  · exact mirror21 _ _ (f16t3 base)
  · exact mirror22 _ _ (f18t3 base)
  · exact mirror23 _ _ (f19t3 base)
  · exact f24t3 base
  · exact f25t3 base
  · exact f26t3 base
  · exact mirror27 _ _ (f25t3 base)
  · exact mirror28 _ _ (f26t3 base)
  · exact f29t3 base
  · exact f30t3 base
  · exact mirror31 _ _ (f30t3 base)
  · exact f32t3 base
  · exact mirror33 _ _ (f32t3 base)
  · exact f34t3 base
  · exact f35t3 base
lemma upperCases (base : Imp [] 0 13) {t : ℕ} (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ e ∈ six, Excluded 12 e (remT (unaryE e) t) := by
  interval_cases t
  · exact stage1 base
  · exact stage2 base
  · exact stage3 base
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_0 : chk [] rStrong 0 11 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_11 : chk [] rStrong 0 11 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_10 : chk [] rStrong 0 11 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_9 : chk [] rStrong 0 11 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_8 : chk [] rStrong 0 11 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_7 : chk [] rStrong 0 11 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_6 : chk [] rStrong 0 11 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_5 : chk [] rStrong 0 11 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_4 : chk [] rStrong 0 11 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_3 : chk [] rStrong 0 11 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_2 : chk [] rStrong 0 11 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_11_1 : chk [] rStrong 0 11 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_12 : chk [] rStrong 0 12 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_11 : chk [] rStrong 0 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_10 : chk [] rStrong 0 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_9 : chk [] rStrong 0 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_8 : chk [] rStrong 0 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_7 : chk [] rStrong 0 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_6 : chk [] rStrong 0 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_5 : chk [] rStrong 0 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem m_12_4 : chk [] rStrong 0 12 4 FF 1 = false := by decide +kernel
lemma i12 : Imp [] 0 12 := imp_ts (Or.inl rfl) strong_p (by norm_num) iStrong (fun t ht => by
  interval_cases t
  · exact one m_11_0
  · exact one m_11_1
  · exact one m_11_2
  · exact one m_11_3
  · exact one m_11_4
  · exact one m_11_5
  · exact one m_11_6
  · exact one m_11_7
  · exact one m_11_8
  · exact one m_11_9
  · exact one m_11_10
  · exact one m_11_11)
lemma no12 {t : ℕ} {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 12 t S) : False := by
  have hmin : ∀ q < 12, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => i12 q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 12 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 13 := by have := hm0.size.2; omega
  by_cases hlow : t ≤ 3
  · apply firstExcluded i12 _ hS hl
    exact lowerCases i12 (Nat.zero_le _) hlow
  · have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 12 t p.1 p.2 = false := by
      have ht4 : 4 ≤ t := by omega
      interval_cases t
      · exact one m_12_4
      · exact one m_12_5
      · exact one m_12_6
      · exact one m_12_7
      · exact one m_12_8
      · exact one m_12_9
      · exact one m_12_10
      · exact one m_12_11
      · exact one m_12_12
    exact imp_of_live (L := 13) (Or.inl rfl) strong_p (by norm_num) iStrong (by omega) hS hl hmin (Or.inr hM)

lemma iroot : Imp [] 0 13 := by
  intro q hq hs
  obtain ⟨k,hk,t,S,hS,hl⟩ := hs.live
  by_cases h : k < 12
  · exact i12 k h (hl.sol.mono le_rfl hS)
  · have he : k = 12 := by omega
    subst k
    exact no12 hS hl
def b1095z0 : List BState := [cs 0 11 3 0x9ce549527495674 [0,1,2,3,4,5,6],cs 0 10 2 0x9ce52a527494a94 [0,7,1,8,3,5,6],cs 0 11 3 0x9ce92a4a74aca93 [0,1,9,8,10,5,6],cs 0 11 3 0x9c654a527395694 [0,11,1,3,4,5,6],cs 0 11 3 0x9c692a5273aca94 [0,12,1,8,10,5,6],cs 0 11 3 0x9ce549527495674 [0,1,10,2,4,5,6],cs 0 11 3 0x9ce748d2749d654 [0,1,13,10,14,4,6],cs 0 11 3 0x9ce93a4674ace92 [0,1,15,10,4,16,5],cs 0 10 2 0x9ce54a4a7495691 [0,17,1,15,3,4,5],cs 0 10 2 0x9ce9295274aca34 [0,18,1,13,8,10,6],cs 0 11 3 0x9ce748d2749d654 [0,1,10,14,4,5,6],cs 0 11 3 0x9ce92a4a74aca93 [0,1,9,10,4,5,6]]
theorem b1095z0ok : rowsPass rStrong 13 b1095z0 = true := by decide +kernel
def b1095z1 : List BState := [cs 0 11 3 0x9ce93a4674ace92 [0,1,10,4,16,5,6],cs 0 10 2 0x9ce34a46749d692 [0,1,15,3,19,4,5],cs 0 10 2 0x9ce9494a74ad631 [20,0,1,15,13,10,4],cs 0 11 3 0x9c654a527395694 [0,11,1,10,4,5,6],cs 0 11 3 0x9c692a5273aca94 [0,12,1,10,4,5,6],cs 0 10 2 0x9ce31a52749ce94 [0,1,8,3,21,5,6],cs 0 10 2 0x9ce918d274ace54 [0,1,13,8,22,10,6],cs 0 10 2 0x9ce948c674ad652 [0,1,15,13,23,10,4],cs 0 11 3 0x9ce52a527495294 [0,1,24,3,4,5,6],cs 0 11 3 0x9ce52a5274a4a94 [0,1,25,8,10,5,6],cs 0 11 3 0x9ce54a4a7495693 [0,1,26,3,4,5,6],cs 0 11 3 0x9ce9295274aca74 [0,1,27,8,10,5,6],cs 0 10 2 0x9ce348d2749d654 [0,1,13,3,28,4,6],cs 0 10 2 0x9ce549527495634 [0,29,1,13,3,4,6],cs 0 10 2 0x9ce92a4a74aca91 [0,30,1,15,8,10,5],cs 0 11 3 0x8ce54a525495694 [31,0,1,3,4,5,6]]
theorem b1095z1ok : rowsPass rStrong 13 b1095z1 = true := by decide +kernel
def b1095z2 : List BState := [cs 0 11 3 0x9c274a52729d694 [0,10,4,5,6,32,33],cs 0 11 3 0x9ca94a4672ad692 [0,1,15,34,10,4,5],cs 0 11 3 0x9ce33a52749ce94 [0,1,3,4,35,5,6],cs 0 11 3 0x9ce349d2749d654 [0,1,3,4,5,36,6],cs 0 11 3 0x9ce34a4e749d692 [0,1,3,4,5,6,37],cs 0 11 3 0x9ce52a527495294 [0,1,10,24,4,5,6],cs 0 11 3 0x9ce52a5274a4a94 [0,1,25,10,4,5,6],cs 0 11 3 0x9ce54a4a74a5691 [0,1,38,15,10,4,5],cs 0 11 3 0x9ce71a52749ce94 [0,1,8,10,39,5,6],cs 0 11 3 0x9ce74a46749d692 [0,1,15,10,40,4,5],cs 0 11 3 0x9ce919d274ace54 [0,1,8,10,5,41,6],cs 0 11 3 0x9ce9295274ad234 [0,1,42,13,10,4,6],cs 0 11 3 0x9ce938d274ace54 [0,1,13,10,4,43,6],cs 0 10 2 0x9ce91a4674ace92 [0,1,15,8,44,10,5],cs 0 11 3 0x8ce92a5254aca94 [45,0,1,8,10,5,6],cs 0 11 3 0x8ce9495254ad634 [46,0,1,13,10,4,6],cs 0 11 3 0x8ce94a4a54ad691 [47,0,1,15,10,4,5],cs 0 11 3 0x94e34a52349d694 [0,1,3,48,4,5,6],cs 0 11 3 0x94e91a5234ace94 [0,1,8,49,10,5,6],cs 0 11 3 0x94e948d234ad654 [0,1,13,50,10,4,6]]
theorem b1095z2ok : rowsPass rStrong 13 b1095z2 = true := by decide +kernel
def b1095z3 : List BState := [cs 0 11 3 0x9c274a52729d694 [0,1,10,4,5,6,33],cs 0 11 3 0x9c293a5272ace94 [0,10,4,5,6,32,51],cs 0 11 3 0x9c692a5271ad294 [0,10,52,4,5,6,32],cs 0 11 3 0x9c69495273ad634 [0,53,1,13,10,4,6],cs 0 11 3 0x9c694a4a73ad691 [0,54,1,15,10,4,5],cs 0 11 3 0x9ca34a52729d694 [0,1,3,55,4,5,6],cs 0 11 3 0x9ca34a52729d694 [0,1,10,55,4,5,6],cs 0 11 3 0x9ca91a5272ace94 [0,1,56,10,4,5,6],cs 0 11 3 0x9ca91a5272ace94 [0,1,8,56,10,5,6],cs 0 11 3 0x9ca948d272ad654 [0,1,13,57,10,4,6],cs 0 11 3 0x9ca94a4672ad692 [0,1,34,10,4,5,6],cs 0 11 3 0x9ce33a52749ce94 [0,1,10,4,35,5,6],cs 0 11 3 0x9ce349d2749d654 [0,1,10,4,5,36,6],cs 0 11 3 0x9ce34a4e749d692 [0,1,10,4,5,6,37],cs 0 11 3 0x9ce5495274a5634 [0,1,58,10,4,5,6],cs 0 11 3 0x9ce5495274a5634 [0,1,58,13,10,4,6],cs 0 11 3 0x9ce54a4a7495693 [0,1,10,26,4,5,6],cs 0 11 3 0x9ce74a46749d692 [0,1,10,40,4,5,6],cs 0 11 3 0x9ce91a4e74ace92 [0,1,8,10,5,6,59],cs 0 11 3 0x9ce9295274aca74 [0,1,27,10,4,5,6],cs 0 11 3 0x9ce92a4a74ad291 [0,1,60,10,4,5,6],cs 0 11 3 0x9ce92a4a74ad291 [0,1,60,15,10,4,5]]
theorem b1095z3ok : rowsPass rStrong 13 b1095z3 = true := by decide +kernel
def b1095z4 : List BState := [cs 0 11 3 0x9ce938d274ace54 [0,1,10,4,43,5,6],cs 0 11 3 0x9ce948ce74ad652 [0,1,13,10,4,6,61],cs 0 11 3 0x9ce9494a74ad633 [0,1,62,13,10,4,6],cs 0 11 3 0x9ce949c674ad652 [0,1,15,10,4,5,63],cs 0 10 2 0x9ce52a527494a94 [0,7,1,3,4,5,6],cs 0 10 2 0x9ce52a527494a94 [0,7,1,8,10,5,6],cs 0 11 3 0x8c694a5251ad694 [64,0,10,4,5,6,32],cs 0 11 3 0x94e34a52349d694 [0,1,10,48,4,5,6],cs 0 11 3 0x94e94a4634ad692 [0,1,15,65,10,4,5],cs 0 11 3 0x9c293a5272ace94 [0,1,10,4,5,6,51],cs 0 11 3 0x9c654a5271a5694 [0,66,10,4,5,6,32],cs 0 11 3 0x9c654a5271a5694 [0,1,66,10,4,5,6],cs 0 11 3 0x9c692a5271ad294 [0,1,10,52,4,5,6],cs 0 11 3 0x9c69495271ad674 [0,10,4,67,5,6,32],cs 0 11 3 0x9c69495273ad634 [0,53,1,10,4,5,6],cs 0 11 3 0x9c694a4a71ad693 [0,10,4,5,68,6,32],cs 0 11 3 0x9c694a4a71ad693 [0,1,10,4,5,68,6],cs 0 11 3 0x9c694a4a73ad691 [0,54,1,10,4,5,6],cs 0 11 3 0x9ca948d272ad654 [0,1,57,10,4,5,6],cs 0 11 3 0x9ce54a4a74a5691 [0,1,38,10,4,5,6],cs 0 11 3 0x9ce71a52749ce94 [0,1,10,39,4,5,6],cs 0 11 3 0x9ce919d274ace54 [0,1,10,4,5,41,6],cs 0 11 3 0x9ce91a4e74ace92 [0,1,10,4,5,6,59],cs 0 11 3 0x9ce9295274ad234 [0,1,42,10,4,5,6],cs 0 11 3 0x9ce948ce74ad652 [0,1,10,4,5,6,61],cs 0 11 3 0x9ce9494a74ad633 [0,1,62,10,4,5,6]]
theorem b1095z4ok : rowsPass rStrong 13 b1095z4 = true := by decide +kernel
def b1095z5 : List BState := [cs 0 11 3 0x9ce9494a74ad671 [0,1,69,10,4,5,6],cs 0 11 3 0x9ce9494a74ad671 [0,1,69,15,10,4,5],cs 0 10 2 0x9ce31a52749ce94 [0,1,3,4,21,5,6],cs 0 10 2 0x9ce31a52749ce94 [0,1,8,10,21,5,6],cs 0 10 2 0x9ce52a527494a94 [0,7,1,10,4,5,6],cs 0 10 2 0x9ce54a4a7495691 [0,17,1,3,4,5,6],cs 0 10 2 0x9ce54a4a7495691 [0,17,1,15,10,4,5],cs 0 10 2 0x9ce9295274aca34 [0,18,1,10,4,5,6],cs 0 10 2 0x9ce9295274aca34 [0,18,1,8,10,5,6],cs 0 10 2 0x9ce9295274aca34 [0,18,1,13,10,4,6],cs 0 10 2 0x9ce9494a74ad631 [20,0,1,15,10,4,5],cs 0 11 3 0x84e93a5234ace94 [1,10,4,5,6,70,71],cs 0 11 3 0x8c694a5251ad694 [64,0,1,10,4,5,6],cs 0 11 3 0x8ce54a525495694 [31,0,1,10,4,5,6],cs 0 11 3 0x8ce92a5254aca94 [45,0,1,10,4,5,6],cs 0 11 3 0x8ce9495254ad634 [46,0,1,10,4,5,6],cs 0 11 3 0x8ce94a4a54ad691 [47,0,1,10,4,5,6],cs 0 11 3 0x94294a5232ad694 [0,10,4,5,6,32,72],cs 0 11 3 0x94e91a5234ace94 [0,1,49,10,4,5,6],cs 0 11 3 0x94e948d234ad654 [0,1,50,10,4,5,6],cs 0 11 3 0x94e94a4634ad692 [0,1,65,10,4,5,6],cs 0 11 3 0x9c2949d272ad654 [0,10,4,5,6,32,73],cs 0 11 3 0x9c69495271ad674 [0,1,10,4,67,5,6],cs 0 11 3 0x9ce949c674ad652 [0,1,10,4,5,63,6],cs 0 10 2 0x9c2948d272ad654 [0,13,10,4,6,32,74],cs 0 10 2 0x9ce31a52749ce94 [0,1,10,4,21,5,6],cs 0 10 2 0x9ce34a46749d692 [0,1,3,19,4,5,6],cs 0 10 2 0x9ce34a46749d692 [0,1,10,19,4,5,6],cs 0 10 2 0x9ce34a46749d692 [0,1,15,10,19,4,5],cs 0 10 2 0x9ce549527495634 [0,29,1,3,4,5,6],cs 0 10 2 0x9ce54a4a7495691 [0,17,1,10,4,5,6],cs 0 10 2 0x9ce918d274ace54 [0,1,22,10,4,5,6],cs 0 10 2 0x9ce918d274ace54 [0,1,8,22,10,5,6],cs 0 10 2 0x9ce918d274ace54 [0,1,13,22,10,4,6],cs 0 10 2 0x9ce948c674ad652 [0,1,23,10,4,5,6],cs 0 10 2 0x9ce948c674ad652 [0,1,13,23,10,4,6]]
theorem b1095z5ok : rowsPass rStrong 13 b1095z5 = true := by decide +kernel
def b1095z6 : List BState := [cs 0 10 2 0x9ce948c674ad652 [0,1,15,23,10,4,5],cs 0 10 2 0x9ce9494a74ad631 [20,0,1,10,4,5,6],cs 0 10 2 0x9ce9494a74ad631 [20,0,1,13,10,4,6],cs 0 11 3 0x84a94a5232ad694 [1,10,4,5,6,70,75],cs 0 11 3 0x84e74a52349d694 [1,10,4,5,6,70,76],cs 0 11 3 0x84e74a52349d694 [0,1,10,4,5,6,76],cs 0 11 3 0x84e93a5234ace94 [0,1,10,4,5,6,71],cs 0 11 3 0x84e949d234ad654 [1,10,4,5,6,70,77],cs 0 11 3 0x84e94a4e34ad692 [1,10,4,5,6,70,78],cs 0 11 3 0x84e94a4e34ad692 [0,1,10,4,5,6,78],cs 0 11 3 0x8ce54a5214a5694 [1,79,10,4,5,6,70],cs 0 11 3 0x8ce54a5214a5694 [0,1,79,10,4,5,6],cs 0 11 3 0x8ce92a5214ad294 [1,10,80,4,5,6,70],cs 0 11 3 0x8ce92a5214ad294 [0,1,10,80,4,5,6],cs 0 11 3 0x8ce9495214ad674 [1,10,4,81,5,6,70],cs 0 11 3 0x8ce94a4a14ad693 [1,10,4,5,82,6,70],cs 0 11 3 0x94294a5232ad694 [0,1,10,4,5,6,72],cs 0 11 3 0x9c2949d272ad654 [0,1,10,4,5,6,73],cs 0 11 3 0x9c294a4e72ad692 [0,10,4,5,6,32,83],cs 0 11 3 0x9c294a4e72ad692 [0,1,10,4,5,6,83],cs 0 10 2 0x84e34a52349d694 [1,10,4,5,6,70,84],cs 0 10 2 0x84e34a52349d694 [0,1,3,4,5,6,84],cs 0 10 2 0x84e91a5234ace94 [1,10,4,5,6,70,85],cs 0 10 2 0x84e91a5234ace94 [1,8,10,5,6,70,85],cs 0 10 2 0x84e91a5234ace94 [0,1,10,4,5,6,85],cs 0 10 2 0x84e94a4634ad692 [0,1,15,10,4,5,86],cs 0 10 2 0x8ce92a5214aca94 [0,1,87,8,10,5,6],cs 0 10 2 0x8ce9495214ad634 [0,1,88,10,4,5,6],cs 0 10 2 0x8ce9495214ad634 [0,1,88,13,10,4,6],cs 0 10 2 0x8ce94a4a14ad691 [0,1,89,15,10,4,5],cs 0 10 2 0x9c234a52729d694 [0,1,3,4,5,6,90],cs 0 10 2 0x9c234a52729d694 [0,1,10,4,5,6,90],cs 0 10 2 0x9c2948d272ad654 [0,10,4,5,6,32,74],cs 0 10 2 0x9c2948d272ad654 [0,1,10,4,5,6,74],cs 0 10 2 0x9c2948d272ad654 [0,1,13,10,4,6,74],cs 0 10 2 0x9c294a4672ad692 [0,10,4,5,6,32,91]]
theorem b1095z6ok : rowsPass rStrong 13 b1095z6 = true := by decide +kernel
def b1095z7 : List BState := [cs 0 10 2 0x9c294a4672ad692 [0,15,10,4,5,32,91],cs 0 10 2 0x9c294a4672ad692 [0,1,10,4,5,6,91],cs 0 10 2 0x9c294a4672ad692 [0,1,15,10,4,5,91],cs 0 10 2 0x9c654a527195694 [0,92,3,4,5,6,32],cs 0 10 2 0x9c654a527195694 [0,10,92,4,5,6,32],cs 0 10 2 0x9c654a527195694 [0,1,92,3,4,5,6],cs 0 10 2 0x9c654a527195694 [0,1,10,92,4,5,6],cs 0 10 2 0x9c692a5271aca94 [0,93,10,4,5,6,32],cs 0 10 2 0x9c692a5271aca94 [0,93,8,10,5,6,32],cs 0 10 2 0x9c692a5271aca94 [0,1,93,10,4,5,6],cs 0 10 2 0x9c692a5271aca94 [0,1,93,8,10,5,6],cs 0 10 2 0x9c69495271ad634 [0,1,94,10,4,5,6],cs 0 10 2 0x9c69495271ad634 [0,1,94,13,10,4,6],cs 0 10 2 0x9c694a4a71ad691 [0,95,10,4,5,6,32],cs 0 10 2 0x9c694a4a71ad691 [0,1,95,15,10,4,5],cs 0 10 2 0x9ce348d2749d654 [0,1,3,28,4,5,6],cs 0 10 2 0x9ce348d2749d654 [0,1,10,28,4,5,6],cs 0 10 2 0x9ce549527495634 [0,29,1,10,4,5,6],cs 0 10 2 0x9ce549527495634 [0,29,1,13,10,4,6],cs 0 10 2 0x9ce91a4674ace92 [0,1,8,44,10,5,6],cs 0 10 2 0x9ce91a4674ace92 [0,1,15,44,10,4,5],cs 0 10 2 0x9ce92a4a74aca91 [0,30,1,8,10,5,6],cs 0 10 2 0x9ce92a4a74aca91 [0,30,1,15,10,4,5],cs 0 11 3 0x84a94a5232ad694 [0,1,10,4,5,6,75],cs 0 11 3 0x84e949d234ad654 [0,1,10,4,5,6,77],cs 0 11 3 0x8c694a5213ad694 [96,1,10,4,5,6,70],cs 0 11 3 0x8c694a5213ad694 [0,96,1,10,4,5,6],cs 0 11 3 0x8ce9495214ad674 [0,1,10,4,81,5,6],cs 0 11 3 0x8ce94a4a14ad693 [0,1,10,4,5,82,6],cs 0 10 2 0x84294a5232ad694 [1,10,4,5,6,70,97],cs 0 10 2 0x84294a5232ad694 [0,10,4,5,6,32,97],cs 0 10 2 0x84294a5232ad694 [0,1,10,4,5,6,97],cs 0 10 2 0x84e34a52349d694 [1,3,4,5,6,70,84],cs 0 10 2 0x84e34a52349d694 [0,1,10,4,5,6,84],cs 0 10 2 0x84e91a5234ace94 [0,1,8,10,5,6,85],cs 0 10 2 0x84e948d234ad654 [1,10,4,5,6,70,98]]
theorem b1095z7ok : rowsPass rStrong 13 b1095z7 = true := by decide +kernel
def b1095z8 : List BState := [cs 0 10 2 0x84e948d234ad654 [1,13,10,4,6,70,98]]
theorem b1095z8ok : rowsPass rStrong 13 b1095z8 = true := by decide +kernel
def m1095 := b1095z0 ++ b1095z1 ++ b1095z2 ++ b1095z3 ++ b1095z4 ++ b1095z5 ++ b1095z6 ++ b1095z7 ++ b1095z8
theorem z1095 : outerRun [] rStrong 13 4 0x0 1 m1095 = false := by decide +kernel
theorem leaf1095 : chk [] rStrong 0 13 4 0x0 1 = false := by
  apply joinRows (xs:=m1095) _ z1095
  simp only [m1095,rowsAppend,b1095z0ok,b1095z1ok,b1095z2ok,b1095z3ok,b1095z4ok,b1095z5ok,b1095z6ok,b1095z7ok,b1095z8ok,Bool.and_self]

theorem leaf1096 : chk [] rStrong 0 13 4 0x281800422140000001500000000800000202000400000002800000 0 = false := by decide +kernel
theorem leaf1097 : chk [] rStrong 0 13 4 0x4000050220050000400000000a6008500000b 0 = false := by decide +kernel
theorem leaf1098 : chk [] rStrong 0 13 4 0x2a200085002080002000420000000001010000800002420000000 0 = false := by decide +kernel
theorem leaf1099 : chk [] rStrong 0 13 4 0x1000080000000000004020180c004002004000010101210008020 0 = false := by decide +kernel
theorem leaf1100 : chk [] rStrong 0 13 4 0x40040c08020000008000481008040100004000000048010400 0 = false := by decide +kernel
theorem leaf1101 : chk [] rStrong 0 13 4 0x80010030541800081000000000010000800000400000024104 0 = false := by decide +kernel
theorem leaf1102 : chk [] rStrong 0 13 4 0x8000800020034000002202904001090040000000040010 0 = false := by decide +kernel
theorem leaf1103 : chk [] rStrong 0 13 4 0x4000000200008200202080000120008000400300084100200080 0 = false := by decide +kernel
theorem leaf1104 : chk [] rStrong 0 13 4 0x400100001000080800800000000280800040026018800500000 0 = false := by decide +kernel
theorem leaf1105 : chk [] rStrong 0 13 4 0x11d200000006400000104100000000000208080000000003040 0 = false := by decide +kernel
theorem leaf1106 : chk [] rStrong 0 13 4 0x10000200000401004000000a040001000080023009000000080800 0 = false := by decide +kernel
theorem leaf1107 : chk [] rStrong 0 13 4 0x40020000080200118000000010480420068100000000000000200 0 = false := by decide +kernel
lemma rootRun4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 4 p.1 p.2 = false := by
  refine ⟨_, ?_, addMask (f:=chk [] rStrong 0 13 4) leaf1095 (addMask leaf1096 (addMask leaf1097 (addMask leaf1098 (addMask leaf1099 (addMask leaf1100 (addMask leaf1101 (addMask leaf1102 (addMask leaf1103 (addMask leaf1104 (addMask leaf1105 (addMask leaf1106 (addMask leaf1107 endMasks))))))))))))⟩
  decide +kernel
theorem leaf1108 : chk [] rStrong 0 13 5 FF 1 = false := by decide +kernel
lemma rootRun5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 5 p.1 p.2 = false := by
  exact one leaf1108
theorem leaf1109 : chk [] rStrong 0 13 6 FF 1 = false := by decide +kernel
lemma rootRun6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 6 p.1 p.2 = false := by
  exact one leaf1109
theorem leaf1110 : chk [] rStrong 0 13 7 FF 1 = false := by decide +kernel
lemma rootRun7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 7 p.1 p.2 = false := by
  exact one leaf1110
theorem leaf1111 : chk [] rStrong 0 13 8 FF 1 = false := by decide +kernel
lemma rootRun8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 8 p.1 p.2 = false := by
  exact one leaf1111
theorem leaf1112 : chk [] rStrong 0 13 9 FF 1 = false := by decide +kernel
lemma rootRun9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 9 p.1 p.2 = false := by
  exact one leaf1112
theorem leaf1113 : chk [] rStrong 0 13 10 FF 1 = false := by decide +kernel
lemma rootRun10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 10 p.1 p.2 = false := by
  exact one leaf1113
theorem leaf1114 : chk [] rStrong 0 13 11 FF 1 = false := by decide +kernel
lemma rootRun11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 11 p.1 p.2 = false := by
  exact one leaf1114
theorem leaf1115 : chk [] rStrong 0 13 12 FF 1 = false := by decide +kernel
lemma rootRun12 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 12 p.1 p.2 = false := by
  exact one leaf1115
theorem leaf1116 : chk [] rStrong 0 13 13 FF 1 = false := by decide +kernel
lemma rootRun13 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 13 p.1 p.2 = false := by
  exact one leaf1116
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 13 t S) : False := by
  have hmin : ∀ q < 13, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 13 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 14 := by have := hm0.size.2; omega
  by_cases hlow : t ≤ 3
  · apply firstExcluded iroot _ hS hl
    exact upperCases iroot ht1 hlow
  · have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 t p.1 p.2 = false := by
      have ht4 : 4 ≤ t := by omega
      interval_cases t
      · exact rootRun4
      · exact rootRun5
      · exact rootRun6
      · exact rootRun7
      · exact rootRun8
      · exact rootRun9
      · exact rootRun10
      · exact rootRun11
      · exact rootRun12
      · exact rootRun13
    exact imp_of_live (L := 14) (Or.inl rfl) strong_p (by norm_num) iStrong (by omega) hS hl hmin (Or.inr hM)
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
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1 && x 2) || (x 0 && x 1 && x 3) || (x 0 && x 2 && x 3) || (x 1 && x 2 && x 3) || (x 1 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 2 && x 3 && x 4) || (x 0 && x 1 && x 5) || (x 0 && x 2 && x 4 && x 5) || (x 1 && x 3 && x 4 && x 5)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 2 0) ||| (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0) ||| (rawP.getD 2 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0)
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

def target : (Fin 6 → Bool) → Bool := fun x => Nat.testBit (4276676744 * 2 ^ 32 + 4206946432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem f_target : ∀ x : Fin 6 → Bool, f x = target x := by
  decide +kernel

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [15, 18]⟩], 19⟩

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
end PEqualNP.Outside.L_meta_47789

theorem PEqualNP.Outside.L_meta_47789 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4206946432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4206946432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_47789.solve
