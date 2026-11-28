import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48075
def bigNat_0 : Nat := 0xffeffefff7ffbffbffd7ffafff57ff6dddffdffdffd6ffed5ff7ffeedbbbbbbfffeeffffb6bfffeffffaffffbfffeffffbfff0000000000000000
def bigNat_1 : Nat := 0x800112444444000110000494000100005000040001000040000000000000000000
def bigNat_2 : Nat := 0x100100100080040040028005000a800922200200200290012a00000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0xfff0000000fff1ffe20000038003ffbff8dffc28001338083303308e79c251c0509868265e4261c09978265e099c000000000000000032e32e1973cb8cb865d3cb87971257245c45cd5cd5c666e149700000c3b83bbfffee00000680000ffffa00003fffeffffbfffdfbf7efdfbf7efdf
def bigNat_4 : Nat := 0x1ffe0000007ff80001ffe80000383ff8003ffa1ffd88002558c105307124a8c49ae21129b84a2a44a6e128b04aae12ac00000000000000004d64d676b0b59359dac075a6eb41ab49c4bac2acbad03b6c46b0000e183b8380000effffb0bfffe00002ffff80000ffffbfffefdfbf7efdfbf7ef
def bigNat_5 : Nat := 0x1ffc0000007ff0000fff40000ffe1803ffbff80001ffda0004ae80250570249c9496766c254c89532495b6256d895342574000000000000000089ae9aa4d526ba6a934766a8cd45cd0c89b35b352340b3ad14d7ffe01b83b800000effffb60000000002ffffbfffe00003ffff7efdfbf7efdfbf7
def bigNat_6 : Nat := 0x1ffc0000000007ff7ffa00000000ffec003ffbffbffac00000008cf15000755471f0118786d466f119bc11938464e1193846780000000000000000f62962cb1658bd8bec55988b3116f16111dc5dc5dc56cc201b17ffeec003bbbfffe0000036bfffeffff800000000000003ffffbf7efdfbf7efdfb
def bigNat_7 : Nat := 0x1ffdffdffefff000000000000000ffedbb800000000000000000f0819b66000781001e0404878701e1c01e1c078701e1c078400000000000000000e7ce7cf3e79f21f30f861f0c3e04fe6ddd1f91f91f928fc553e7ffeedbb800000000000036bfffeffffaffffbfffeffff8000fdfbf7efdfbf7efd
def bigNat_8 : Nat := 0x1ffdffdffefff7ff7ffafff5ffea000000000000000000000000ff01db776667fe019ff80007f801fe001fe007f801fe007f800000000000000000f80f80fc07e03e03f017e02fc057000001e01e01e004f0081c07ffeedbbbbbbfffeeffff800000000000000000000000000007efdfbf7efdfbf7e
def bigNat_9 : Nat := 0xffeffefff7ffbffbffd7ffafff57ff6dddffdffdffd6ffed5ff7ffeedbbbbbbfffeeffffb6bfffeffffaffffbfffeffffbfffffffffffffffffff
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
def NN : Nat := 469
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
def segsX : List (ℕ × ℕ) := [(63, 78), (78, 96), (96, 114), (114, 132), (132, 134), (134, 152), (152, 170), (170, 172), (172, 175), (175, 178), (178, 196), (196, 200), (200, 218), (218, 222), (222, 226), (226, 230), (230, 234), (234, 238), (238, 241), (241, 244), (244, 248), (248, 263)]
def segsY : List (ℕ × ℕ) := [(263, 273), (273, 275), (275, 277), (277, 280), (280, 292), (292, 295), (295, 297), (297, 309), (309, 321), (321, 333), (333, 337), (337, 341), (341, 344), (344, 347), (347, 359), (359, 361), (361, 363), (363, 376), (376, 378), (378, 391), (391, 393), (393, 406), (406, 418), (418, 431), (431, 444), (444, 456), (456, 468)]
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
  have : Std.Symm (fun a c : L_meta_48075.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
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
    {go : (L_meta_48075.X → L_meta_48075.X → Bool) → List L_meta_48075.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_48075.X.s e
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_48075.X → L_meta_48075.X → Bool) → List L_meta_48075.X → Bool,
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_48075.X.s e))
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
def pairDrops : List Nat := [1116699717876112387303418150015524939969239449707755449068068452195962398431461949739235115438743893082885776877317852999936408658545731535, 1884420303730314601688061319187678600079434217351982677994961627342144434595454897770787461296522377158818162684186544179275256907777305559, 149241887724188696962891159709117693949368217383550304064830235884392754834301672201171872167572643128005109965624182445198058171840517828059, 103480577395761467393143406743803635172433966032065524541873978051472599368815587072156156723221044274276734505856198854365007106405683392221, 142937200429441631321311630655692105679475639796018394175824751209594747122572233605557016108288250717191528143587805176901760622162798423902, 27219480729132827531782231435946235095136047779653611150237658607644447814535561076955755284022566298825286993928233101468170569785129169895, 202820087560076189969681958312381590086581875968872561406947273372912756136442569692422243999805355860066995476655867032710885801982816876011, 206216729467390822793815099791167662343340943045399849745217460374086766577793935126603047268794226533876429710204263059252314063002438170349, 214405839664378312889798404370833535738428811670792687749789324678789054407646367827946385142274940090459414363928340490479620542565883557742, 381538111449460384038197805951968828898686959631362217703026456637900813431468212517631471498147239935574910501130959166964518423406290205171, 385724526592854731435173316107212292885164661945183517178115164913031178180771814642368201404177113117804885087809697006108260239968114146037, 405075881365286999669289835968568508971440295483328515055109987462181686586464140485769962073537226423253494847681688345401718249758671092598, 761870931736348677526813277246992179146702770815976117960218195733635963129208171696485523943055250770548829985233367671169587267338338467065, 761878201010954565428440841599071078772913382908870423407973305451378809721256255703318658069449094081031392432279155005398542905163980389754, 761959526020603992378978560267612720280769002848886734992000923831786761466615252663498096768188915906805399651652202583512662274080216399484, 1524291261628589810333972550682990332883932217261020743052596360007325489058420892986627552511374432176782046647569522696098331638712808505343, 1524108211824797297148197942408544005896461028346990019343745616629321316506542589228142977605120422769468965463041084310995087186096992288767, 789311966320815732174032840994387304216096720789195668820950661650766352189868523104511176197381185583994474476786166099430375170882410643455, 786154625050779827002434312626647109679898175352199909253707390256097777730078949033639139911244799502822628509571568683877993022701109772287, 777221050024253076318831832727521122505290418464607983530977061492456373898770039089038409853043126037784605762807617989908728018810945142783, 1524118343753166289200675467182900092968325968314303265922478110361232323313161590989602825116349478704536905826253797861393241534161383063551, 764006303929219494477695207754892339440604236917612699910547431998561655778366263328104278768976412109205361732512553046195183421902878146559, 809977491788182725909894647912052854307285700216555247996606591377237582976469661034272883838653843008085762628109479906206016576105838804991, 769776404168814663748866880659948476049559943260693936683850271687708809898636387555576435449970896253074789258924993127808371915532649103359, 763076268298609602442248687402506911418391426109718543591111617882833390117591611080782900715825973106383967568875060633537757724657395433471, 809977491788182091786747011282572611221622414540660543154488472271476612260391214983888069764957784595526348526162988960043911353183747702783, 780943372951972282603814308761306300675476648148802415746070512051754251099789564624618961189328937798658418704775106944707221987861930704895, 786154625050779171402794739089386841695783180964353677855642440099613833661450396509651665176687851979797648709597253656045109593944784633855, 767543010412183139977877395039675516232180794975263288231687671253187097797151811622963980958980516355005881271037038190480871511415117053951, 762703990606148171807400176195753288553461128076316228358706713267497652825472924837082442265705946609501241476343698896688043886277036081151]
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
    have : Std.Symm (fun a b : L_meta_48075.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_48075.X.s e)) hpb
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

def rt3 : List (ℕ × ℕ) := [(22, 2), (25, 2), (37, 2), (38, 2), (41, 2), (42, 2), (44, 2), (448, 2), (704, 2), (832, 2), (896, 2), (1792, 2), (2240, 2), (2368, 2), (2688, 2), (2816, 2), (3136, 2), (3200, 2), (3328, 2), (3584, 2)]
def rt2 : List (ℕ × ℕ) := [(3, 3), (5, 2), (6, 3), (9, 3), (10, 2), (12, 2), (17, 2), (18, 2), (20, 2), (24, 2), (33, 3), (34, 3), (36, 5), (40, 5), (48, 3), (66, 4), (68, 4), (72, 5), (80, 5), (96, 6), (129, 4), (132, 5), (136, 4), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (264, 4), (272, 5), (288, 5), (320, 5), (384, 3), (513, 5), (514, 5), (516, 4), (528, 5), (544, 5), (576, 3), (640, 5), (768, 6), (1025, 5), (1026, 5), (1028, 4), (1032, 4), (1056, 5), (1088, 2), (1152, 2), (1280, 3), (1536, 3), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2064, 3), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def rt1 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
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
lemma pairOk0 : okE [] (subsetRows rt 4096) (4096, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk1 : okE [] (subsetRows rt 4101) (4101, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk2 : okE [] (subsetRows rt 4102) (4102, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk3 : okE [] (subsetRows rt 4103) (4103, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk4 : okE [] (subsetRows rt 4104) (4104, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk5 : okE [] (subsetRows rt 4105) (4105, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk6 : okE [] (subsetRows rt 4106) (4106, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk7 : okE [] (subsetRows rt 4109) (4109, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk8 : okE [] (subsetRows rt 4110) (4110, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk9 : okE [] (subsetRows rt 4111) (4111, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk10 : okE [] (subsetRows rt 4114) (4114, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk11 : okE [] (subsetRows rt 4115) (4115, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk12 : okE [] (subsetRows rt 4116) (4116, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk13 : okE [] (subsetRows rt 4117) (4117, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk14 : okE [] (subsetRows rt 4120) (4120, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk15 : okE [] (subsetRows rt 4123) (4123, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk16 : okE [] (subsetRows rt 4124) (4124, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairOk17 : okE [] (subsetRows rt 4125) (4125, 10) = true := by decide +kernel
def pairBounds : List (ℕ × ℕ) := [(4096, 10), (4101, 10), (4102, 11), (4103, 11), (4104, 11), (4105, 10), (4106, 10), (4109, 10), (4110, 11), (4111, 11), (4114, 11), (4115, 11), (4116, 11), (4117, 11), (4120, 11), (4123, 11), (4124, 11), (4125, 10)]
lemma pairValid : ∀ p ∈ pairBounds, Imp [] p.1 p.2 := by
  intro p hp
  simp only [pairBounds, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact imp_okE (Or.inl rfl) pairOk17 (fun q hq => ir q (subsetRows_mem hq))
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
def q2_0 : List (ℕ × ℕ) := [(36, 4), (40, 4), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 4), (320, 5), (513, 5), (514, 5), (528, 5), (544, 4), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 4), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_0 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 8), (64, 9), (128, 9), (256, 8), (512, 8), (1024, 7), (2048, 8)]
def extra_0 : List (ℕ × ℕ) := [(4111, 11)]
def edgeQ0 := q1_0 ++ q2_0 ++ extra_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep0 : six.contains ea0 && allB.all (fun p => okEdge ea0 p.1) &&
  q2_0.all (pass ea0 (lowRt ea0)) &&
  q1_0.all (pass ea0 (q2_0 ++ lowRt ea0)) &&
  extra_0.all (fun p => (lowAll ea0).any (fun b => qual b p)) &&
  pOk 0 edgeQ0 && okEdge ea0 0 = true := by decide +kernel
def ea3 : ℕ × ℕ := (0, 4)
def q2_3 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 4), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 4), (2304, 4), (2560, 5), (3072, 6)]
def q1_3 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 8), (256, 8), (512, 9), (1024, 8), (2048, 8)]
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
def q2_4 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 4), (544, 5), (640, 4), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_4 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 8), (1024, 8), (2048, 8)]
def extra_4 : List (ℕ × ℕ) := [(4115, 11)]
def edgeQ4 := q1_4 ++ q2_4 ++ extra_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep4 : six.contains ea4 && allB.all (fun p => okEdge ea4 p.1) &&
  q2_4.all (pass ea4 (lowRt ea4)) &&
  q1_4.all (pass ea4 (q2_4 ++ lowRt ea4)) &&
  extra_4.all (fun p => (lowAll ea4).any (fun b => qual b p)) &&
  pOk 0 edgeQ4 && okEdge ea4 0 = true := by decide +kernel
def ea5 : ℕ × ℕ := (1, 2)
def q2_5 : List (ℕ × ℕ) := [(36, 5), (40, 4), (72, 4), (80, 5), (96, 5), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 4), (2050, 5), (2052, 5), (2056, 4), (2112, 4), (2176, 5), (2304, 5), (2560, 4), (3072, 6)]
def q1_5 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 6), (16, 6), (32, 9), (64, 8), (128, 9), (256, 9), (512, 9), (1024, 7), (2048, 7)]
def extra_5 : List (ℕ × ℕ) := [(4116, 11)]
def edgeQ5 := q1_5 ++ q2_5 ++ extra_5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep5 : six.contains ea5 && allB.all (fun p => okEdge ea5 p.1) &&
  q2_5.all (pass ea5 (lowRt ea5)) &&
  q1_5.all (pass ea5 (q2_5 ++ lowRt ea5)) &&
  extra_5.all (fun p => (lowAll ea5).any (fun b => qual b p)) &&
  pOk 0 edgeQ5 && okEdge ea5 0 = true := by decide +kernel
def ea6 : ℕ × ℕ := (1, 3)
def q2_6 : List (ℕ × ℕ) := [(36, 4), (40, 5), (72, 5), (80, 5), (96, 5), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 4), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_6 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 8), (128, 9), (256, 9), (512, 9), (1024, 7), (2048, 8)]
def extra_6 : List (ℕ × ℕ) := [(4117, 11)]
def edgeQ6 := q1_6 ++ q2_6 ++ extra_6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep6 : six.contains ea6 && allB.all (fun p => okEdge ea6 p.1) &&
  q2_6.all (pass ea6 (lowRt ea6)) &&
  q1_6.all (pass ea6 (q2_6 ++ lowRt ea6)) &&
  extra_6.all (fun p => (lowAll ea6).any (fun b => qual b p)) &&
  pOk 0 edgeQ6 && okEdge ea6 0 = true := by decide +kernel
def ea9 : ℕ × ℕ := (2, 3)
def q2_9 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 5), (132, 5), (144, 5), (160, 5), (192, 4), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 4), (1026, 4), (1056, 4), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_9 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 8), (64, 8), (128, 8), (256, 9), (512, 9), (1024, 7), (2048, 8)]
def extra_9 : List (ℕ × ℕ) := [(4120, 11)]
def edgeQ9 := q1_9 ++ q2_9 ++ extra_9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep9 : six.contains ea9 && allB.all (fun p => okEdge ea9 p.1) &&
  q2_9.all (pass ea9 (lowRt ea9)) &&
  q1_9.all (pass ea9 (q2_9 ++ lowRt ea9)) &&
  extra_9.all (fun p => (lowAll ea9).any (fun b => qual b p)) &&
  pOk 0 edgeQ9 && okEdge ea9 0 = true := by decide +kernel
def ea12 : ℕ × ℕ := (3, 4)
def q2_12 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 4), (2304, 4), (2560, 5), (3072, 6)]
def q1_12 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 8), (128, 8), (256, 9), (512, 9), (1024, 8), (2048, 8)]
def extra_12 : List (ℕ × ℕ) := [(4123, 11)]
def edgeQ12 := q1_12 ++ q2_12 ++ extra_12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep12 : six.contains ea12 && allB.all (fun p => okEdge ea12 p.1) &&
  q2_12.all (pass ea12 (lowRt ea12)) &&
  q1_12.all (pass ea12 (q2_12 ++ lowRt ea12)) &&
  extra_12.all (fun p => (lowAll ea12).any (fun b => qual b p)) &&
  pOk 0 edgeQ12 && okEdge ea12 0 = true := by decide +kernel
def ea13 : ℕ × ℕ := (3, 5)
def q2_13 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 4), (96, 6), (132, 5), (144, 5), (160, 6), (192, 4), (257, 5), (258, 5), (272, 5), (288, 5), (320, 4), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_13 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 8), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
def extra_13 : List (ℕ × ℕ) := [(4124, 11)]
def edgeQ13 := q1_13 ++ q2_13 ++ extra_13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep13 : six.contains ea13 && allB.all (fun p => okEdge ea13 p.1) &&
  q2_13.all (pass ea13 (lowRt ea13)) &&
  q1_13.all (pass ea13 (q2_13 ++ lowRt ea13)) &&
  extra_13.all (fun p => (lowAll ea13).any (fun b => qual b p)) &&
  pOk 0 edgeQ13 && okEdge ea13 0 = true := by decide +kernel
def ea14 : ℕ × ℕ := (4, 5)
def q2_14 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 4), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 4), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_14 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 6), (8, 6), (16, 6), (32, 9), (64, 8), (128, 8), (256, 8), (512, 8), (1024, 8), (2048, 8)]
def extra_14 : List (ℕ × ℕ) := [(4125, 10)]
def edgeQ14 := q1_14 ++ q2_14 ++ extra_14
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep14 : six.contains ea14 && allB.all (fun p => okEdge ea14 p.1) &&
  q2_14.all (pass ea14 (lowRt ea14)) &&
  q1_14.all (pass ea14 (q2_14 ++ lowRt ea14)) &&
  extra_14.all (fun p => (lowAll ea14).any (fun b => qual b p)) &&
  pOk 0 edgeQ14 && okEdge ea14 0 = true := by decide +kernel
def ea15 : ℕ × ℕ := (6, 1)
def q2_15 : List (ℕ × ℕ) := [(36, 4), (40, 4), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 4), (320, 5), (513, 5), (514, 5), (528, 5), (544, 4), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 4), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_15 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 8), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 7), (2048, 8)]
def extra_15 : List (ℕ × ℕ) := [(4096, 10)]
def edgeQ15 := q1_15 ++ q2_15 ++ extra_15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep15 : six.contains ea15 && allB.all (fun p => okEdge ea15 p.1) &&
  q2_15.all (pass ea15 (lowRt ea15)) &&
  q1_15.all (pass ea15 (q2_15 ++ lowRt ea15)) &&
  extra_15.all (fun p => (lowAll ea15).any (fun b => qual b p)) &&
  pOk 0 edgeQ15 && okEdge ea15 0 = true := by decide +kernel
def ea20 : ℕ × ℕ := (7, 2)
def q2_20 : List (ℕ × ℕ) := [(36, 5), (40, 4), (72, 4), (80, 4), (96, 5), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 4), (544, 4), (640, 5), (768, 6), (1025, 4), (1026, 5), (1056, 5), (2049, 4), (2050, 5), (2052, 5), (2056, 4), (2112, 4), (2176, 5), (2304, 5), (2560, 4), (3072, 6)]
def q1_20 : List (ℕ × ℕ) := [(1, 6), (2, 7), (4, 7), (8, 6), (16, 5), (32, 9), (64, 8), (128, 9), (256, 9), (512, 8), (1024, 8), (2048, 7)]
def extra_20 : List (ℕ × ℕ) := [(4101, 10)]
def edgeQ20 := q1_20 ++ q2_20 ++ extra_20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep20 : six.contains ea20 && allB.all (fun p => okEdge ea20 p.1) &&
  q2_20.all (pass ea20 (lowRt ea20)) &&
  q1_20.all (pass ea20 (q2_20 ++ lowRt ea20)) &&
  extra_20.all (fun p => (lowAll ea20).any (fun b => qual b p)) &&
  pOk 0 edgeQ20 && okEdge ea20 0 = true := by decide +kernel
def ea21 : ℕ × ℕ := (7, 3)
def q2_21 : List (ℕ × ℕ) := [(36, 4), (40, 5), (72, 5), (80, 5), (96, 5), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 4), (320, 4), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 4), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_21 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 8), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
def extra_21 : List (ℕ × ℕ) := [(4102, 11)]
def edgeQ21 := q1_21 ++ q2_21 ++ extra_21
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep21 : six.contains ea21 && allB.all (fun p => okEdge ea21 p.1) &&
  q2_21.all (pass ea21 (lowRt ea21)) &&
  q1_21.all (pass ea21 (q2_21 ++ lowRt ea21)) &&
  extra_21.all (fun p => (lowAll ea21).any (fun b => qual b p)) &&
  pOk 0 edgeQ21 && okEdge ea21 0 = true := by decide +kernel
def ea22 : ℕ × ℕ := (7, 4)
def q2_22 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 4), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 4), (258, 5), (272, 5), (288, 4), (320, 5), (513, 4), (514, 5), (528, 5), (544, 4), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 4), (2056, 5), (2112, 4), (2176, 5), (2304, 5), (2560, 4), (3072, 6)]
def q1_22 : List (ℕ × ℕ) := [(1, 6), (2, 7), (4, 6), (8, 7), (16, 6), (32, 9), (64, 8), (128, 9), (256, 9), (512, 8), (1024, 8), (2048, 8)]
def extra_22 : List (ℕ × ℕ) := [(4103, 11)]
def edgeQ22 := q1_22 ++ q2_22 ++ extra_22
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep22 : six.contains ea22 && allB.all (fun p => okEdge ea22 p.1) &&
  q2_22.all (pass ea22 (lowRt ea22)) &&
  q1_22.all (pass ea22 (q2_22 ++ lowRt ea22)) &&
  extra_22.all (fun p => (lowAll ea22).any (fun b => qual b p)) &&
  pOk 0 edgeQ22 && okEdge ea22 0 = true := by decide +kernel
def ea23 : ℕ × ℕ := (7, 5)
def q2_23 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 4), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 4), (258, 5), (272, 4), (288, 5), (320, 4), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_23 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 8), (512, 9), (1024, 8), (2048, 8)]
def extra_23 : List (ℕ × ℕ) := [(4104, 11)]
def edgeQ23 := q1_23 ++ q2_23 ++ extra_23
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep23 : six.contains ea23 && allB.all (fun p => okEdge ea23 p.1) &&
  q2_23.all (pass ea23 (lowRt ea23)) &&
  q1_23.all (pass ea23 (q2_23 ++ lowRt ea23)) &&
  extra_23.all (fun p => (lowAll ea23).any (fun b => qual b p)) &&
  pOk 0 edgeQ23 && okEdge ea23 0 = true := by decide +kernel
def ea24 : ℕ × ℕ := (8, 3)
def q2_24 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 5), (132, 5), (144, 5), (160, 5), (192, 4), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 4), (1026, 4), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_24 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 8), (64, 8), (128, 8), (256, 9), (512, 9), (1024, 7), (2048, 8)]
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
def q2_25 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 4), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 4), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 4), (2052, 5), (2056, 5), (2112, 4), (2176, 5), (2304, 5), (2560, 4), (3072, 6)]
def q1_25 : List (ℕ × ℕ) := [(1, 7), (2, 6), (4, 7), (8, 7), (16, 6), (32, 9), (64, 8), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
def extra_25 : List (ℕ × ℕ) := [(4106, 10)]
def edgeQ25 := q1_25 ++ q2_25 ++ extra_25
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep25 : six.contains ea25 && allB.all (fun p => okEdge ea25 p.1) &&
  q2_25.all (pass ea25 (lowRt ea25)) &&
  q1_25.all (pass ea25 (q2_25 ++ lowRt ea25)) &&
  extra_25.all (fun p => (lowAll ea25).any (fun b => qual b p)) &&
  pOk 0 edgeQ25 && okEdge ea25 0 = true := by decide +kernel
def ea28 : ℕ × ℕ := (9, 5)
def q2_28 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 4), (96, 6), (132, 4), (144, 5), (160, 6), (192, 4), (257, 4), (258, 4), (272, 5), (288, 5), (320, 4), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 4), (1026, 4), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_28 : List (ℕ × ℕ) := [(1, 7), (2, 6), (4, 7), (8, 7), (16, 6), (32, 9), (64, 8), (128, 9), (256, 8), (512, 9), (1024, 7), (2048, 8)]
def extra_28 : List (ℕ × ℕ) := [(4109, 10)]
def edgeQ28 := q1_28 ++ q2_28 ++ extra_28
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep28 : six.contains ea28 && allB.all (fun p => okEdge ea28 p.1) &&
  q2_28.all (pass ea28 (lowRt ea28)) &&
  q1_28.all (pass ea28 (q2_28 ++ lowRt ea28)) &&
  extra_28.all (fun p => (lowAll ea28).any (fun b => qual b p)) &&
  pOk 0 edgeQ28 && okEdge ea28 0 = true := by decide +kernel
def ea29 : ℕ × ℕ := (10, 5)
def q2_29 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 4), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 4), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_29 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
def extra_29 : List (ℕ × ℕ) := [(4110, 11)]
def edgeQ29 := q1_29 ++ q2_29 ++ extra_29
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep29 : six.contains ea29 && allB.all (fun p => okEdge ea29 p.1) &&
  q2_29.all (pass ea29 (lowRt ea29)) &&
  q1_29.all (pass ea29 (q2_29 ++ lowRt ea29)) &&
  extra_29.all (fun p => (lowAll ea29).any (fun b => qual b p)) &&
  pOk 0 edgeQ29 && okEdge ea29 0 = true := by decide +kernel
def ea31 : ℕ × ℕ := (13, 0)
def q2_31 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_31 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
def extra_31 : List (ℕ × ℕ) := []
def edgeQ31 := q1_31 ++ q2_31 ++ extra_31
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgePrep31 : six.contains ea31 && allB.all (fun p => okEdge ea31 p.1) &&
  q2_31.all (pass ea31 (lowRt ea31)) &&
  q1_31.all (pass ea31 (q2_31 ++ lowRt ea31)) &&
  extra_31.all (fun p => (lowAll ea31).any (fun b => qual b p)) &&
  pOk 0 edgeQ31 && okEdge ea31 0 = true := by decide +kernel
def ea32 : ℕ × ℕ := (14, 0)
def q2_32 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_32 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
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
def q2_34 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_34 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
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
def q2_35 : List (ℕ × ℕ) := [(36, 5), (40, 5), (72, 5), (80, 5), (96, 6), (132, 5), (144, 5), (160, 6), (192, 5), (257, 5), (258, 5), (272, 5), (288, 5), (320, 5), (513, 5), (514, 5), (528, 5), (544, 5), (640, 5), (768, 6), (1025, 5), (1026, 5), (1056, 5), (2049, 5), (2050, 5), (2052, 5), (2056, 5), (2112, 5), (2176, 5), (2304, 5), (2560, 5), (3072, 6)]
def q1_35 : List (ℕ × ℕ) := [(1, 7), (2, 7), (4, 7), (8, 7), (16, 6), (32, 9), (64, 9), (128, 9), (256, 9), (512, 9), (1024, 8), (2048, 8)]
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
noncomputable def markedChk (R : ℕ → ℕ) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc ((avl P m (rawL E)).map (fun w => {w with r := R w.s})) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma markedTop {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T) (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (flag : ∃ p ∈ M, p.2 = 1) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) (forbid : ∀ k0 d a b S1, k' = k0+1 → R a ≠ 0 → R b ≠ 0 → Bi Z0 d a b S S1 → Live Z0 m T k0 t S1 → False) : False := by
  obtain ⟨p0,hp0,hp1⟩ := flag
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
  rcases front hR2 hl hmW with hlR | ⟨k0,d,a,b,S1,hk0,ha,hb,hbi,ht⟩
  · apply mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) (un p0 hp0).1 ?_ k' hk ⟨hlR,hmin.2⟩ (hyk.imp id fun ⟨q1,q2,q3⟩ => ⟨q1,q2,q3.toR⟩)
    have h := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1] at h
    exact h
  · exact forbid k0 d a b S1 hk0 ha hb hbi ht
theorem marked_imp_live (R : ℕ → ℕ) (rr : RR R) (rr2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (rsub : ∀ x, R x ≠ 0 → x ∈ WZ E Z)
    (forbid : ∀ k0 d a b S1, k = k0+1 → R a ≠ 0 → R b ≠ 0 → Bi Z0 d a b S S1 → Live Z0 (mz Z) (tz Z) k0 t S1 → False)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), (∃ p ∈ M, p.2 = 1) ∧ ∀ p ∈ M, markedChk R E Q Z (L - 1) t p.1 p.2 = false) : False := by
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
  refine markedTop X rr rr2 hMf all hst hcod (by omega) hl ?_ forbid
  intro q hq hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl (rsub _ hx)
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

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

def prim := rawP.map (fun x => x &&& mz 0)
def markRaw (s : ℕ) : ℕ := if prim.contains s then 3 else 0
def rawHit (s : ℕ) := six.any (fun p => !unaryE p && okEdge p 0 && exv p 0 == s)
lemma rawPairs : prim.all (fun a => prim.all (fun b => a == b ||
    (rawHit (op true a b) && rawHit (op false a b)))) = true := by decide +kernel
lemma rawMem (x : ℕ) (hx : markRaw x ≠ 0) : x ∈ prim := by
  simpa [markRaw] using hx
lemma unaryMarked {e : ℕ × ℕ} {Q : List (ℕ × ℕ)} {x t : ℕ}
    (he : e ∈ six) (eq : exv e 0 = ip x 0 ^^^ mz 0) (oe : okEdge e 0 = true)
    (base : Imp [] 0 13) (hp : pOk 0 Q = true) (bounds : ∀ p ∈ Q, Imp [e] p.1 p.2)
    (bin : ∀ p ∈ six, unaryE p = false → Excluded 12 p (t+1))
    (num : markedChk markRaw [e] Q 0 12 t 0 1 = false) : Excluded 12 e t := by
  intro S hs hl
  have rr : RR markRaw := by
    intro d a b ha hb
    have h := rawMem _ ha
    have h' := rawMem _ hb
    cases d <;> simp [Al, markRaw, h, h']
  have rr2 : ∀ d a b, (markRaw a = 0 ∨ markRaw b = 0) → Al markRaw d a b := by
    rintro d a b (h | h) <;> simp [Al,h]
  apply marked_imp_live markRaw rr rr2 (E := [e]) (Q := Q) (L := 13) (Or.inr ⟨e,he,rfl,base⟩) hp (by decide) bounds (by decide) hs hl
  · intro q hq sol; exact base (q+1) (by omega) (prefixOne oe sol)
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (rawMem _ hw)
    exact ⟨v, by simp [rawL,hv], rfl⟩
  · intro k0 d a b S1 hk ha hb bi tail
    obtain rfl : k0 = 11 := by omega
    have h := List.all_eq_true.mp (List.all_eq_true.mp rawPairs a (rawMem _ ha)) b (rawMem _ hb)
    have hn := bi.1
    simp only [beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true] at h
    have hh := h.resolve_left hn
    obtain ⟨p,hp',hhp⟩ := List.any_eq_true.mp (show rawHit (op d a b) = true by cases d <;> tauto)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hhp
    apply swapUnary (x := x) base hhp.1.2 (bin p hp' hhp.1.1) hhp.2.symm ?_ bi tail
    simpa only [←eq] using (hs.trans (extra_sub e 0))
  · exact Or.inr ⟨[(0,1)], ⟨(0,1),by simp,rfl⟩,by simpa using num⟩

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

def cliqueMark (inputs : List ℕ) (w : ℕ) : ℕ := if inputs.contains w then 3 else 0

def priorGate (prior : List (ℕ × ℕ)) (v : ℕ) : Bool :=
  prior.any fun p => okEdge p 0 && exv p 0 == v

def cliqueCovered (inputs : List ℕ) (prior : List (ℕ × ℕ)) : Bool :=
  inputs.all fun a => inputs.all fun b => a == b ||
    (priorGate prior (op true a b) && priorGate prior (op false a b))

lemma binaryMarked {e : ℕ × ℕ} {Q prior : List (ℕ × ℕ)} {inputs : List ℕ}
    {x y t : ℕ} {firstOp : Bool}
    (he : e ∈ six) (eq : exv e 0 = op firstOp (ip x 0) (ip y 0))
    (distinct : ip x 0 ≠ ip y 0) (oe : okEdge e 0 = true)
    (base : Imp [] 0 13) (hp : pOk 0 Q = true) (bounds : ∀ p ∈ Q, Imp [e] p.1 p.2)
    (prims : inputs.all prim.contains = true) (covered : cliqueCovered inputs prior = true)
    (earlier : ∀ p ∈ prior, Excluded 12 p t)
    (num : markedChk (cliqueMark inputs) [e] Q 0 12 t 0 1 = false) : Excluded 12 e t := by
  intro S hs hl
  have mem {w : ℕ} (h : cliqueMark inputs w ≠ 0) : w ∈ inputs := by
    simpa [cliqueMark] using h
  have rr : RR (cliqueMark inputs) := by
    intro d a b ha hb
    have h := mem ha
    have h' := mem hb
    cases d <;> simp [Al, cliqueMark, h, h']
  have rr2 : ∀ d a b, (cliqueMark inputs a = 0 ∨ cliqueMark inputs b = 0) → Al (cliqueMark inputs) d a b := by
    rintro d a b (h | h) <;> simp [Al,h]
  apply marked_imp_live (cliqueMark inputs) rr rr2 (E := [e]) (Q := Q) (L := 13)
    (Or.inr ⟨e,he,rfl,base⟩) hp (by decide) bounds (by decide) hs hl
  · intro q hq sol; exact base (q+1) (by omega) (prefixOne oe sol)
  · intro w hw
    have hprim : w ∈ prim := by simpa using List.all_eq_true.mp prims w (mem hw)
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hprim
    exact ⟨v, by simp [rawL,hv], rfl⟩
  · intro k0 d a b S1 hk ha hb bi tail
    obtain rfl : k0 = 11 := by omega
    have h := List.all_eq_true.mp (List.all_eq_true.mp covered a (mem ha)) b (mem hb)
    have hn := bi.1
    simp only [beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true] at h
    have hh := h.resolve_left hn
    have found : priorGate prior (op d a b) = true := by cases d <;> tauto
    obtain ⟨p,member,hp'⟩ := List.any_eq_true.mp found
    simp only [Bool.and_eq_true, beq_iff_eq] at hp'
    apply swapBinary (firstOp := firstOp) base hp'.1 (earlier p member) (ip_mem x 0) (ip_mem y 0) distinct hp'.2.symm ?_ bi tail
    simpa only [←eq] using (hs.trans (extra_sub e 0))
  · exact Or.inr ⟨[(0,1)], ⟨(0,1),by simp,rfl⟩,by simpa using num⟩

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
noncomputable section
def budgetTop (cb : Nat → Nat → Nat → Nat → List W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (cb 0) l m g k t z v y) (Nat.beq ph 1)) true
      (node (cb 1 (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def budgetStart (cb : Nat → Nat → Nat → Nat → List W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => budgetTop cb l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
lemma dListCons {α : Type} {P : α → Prop} {a : α} {as : List α}
    (one : P a) (rest : ∀ x ∈ as, P x) : ∀ x ∈ a :: as, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact one
  · exact rest _ h
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

noncomputable section
def dSubs (d : Bool) (l : Nat) : List W → Nat → List (List W)
  | [], _ => [[]]
  | w::r, c => ((dSubs d l r (c ||| sp d l w.s)).map (w :: ·)) ++
      (if (c ||| cov d l r) == l then dSubs d l r c else [])
def dRows (R : Nat → Nat) (E Q : List (Nat × Nat)) (Z t : Nat) :=
  dSubs (pos t) (lz Z) ((avl (PZ Q) (mz Z) (rawL E)).map (fun w => {w with r := R w.s})) 0
abbrev DW := List W
abbrev DY := (ℕ × DW)
abbrev DS := DeepState
def tBegin (d : Bool) (l e : ℕ) (v : DW) : List ℕ :=
  if tst d l e v (fun _ => true) then [if tst d l e v (fun a => a == 0) then 0 else 1] else []
def tIns (w : W) : DW → Option DW
  | [] => some [w]
  | x::xs => if x.s ≤ w.s then (if x.s = w.s then none else some (w::x::xs))
      else (tIns w xs).map (x::·)
def tChild (g z : ℕ) (v : DW) : List DY :=
  if (z &&& g) = g then [(z,v)] else []
def tGate (m g e z : ℕ) (v : DW) (a b : X) (dis : Bool) : List DY := Id.run do
  let n := v.length-1
  let p := if dis then a.u &&& b.q else (a.u &&& b.s) ^^^ a.u
  let q := if dis then b.u &&& a.q else (b.u &&& a.s) ^^^ b.u
  if v.length > e && (p ||| q) != 0 then return []
  if v.length = e && p*q != 0 then return []
  let s := if dis then a.s ||| b.s else a.s &&& b.s
  if s == 0 || s == m then return []
  let x := if dis then a.w.a &&& b.w.a else a.w.a ||| b.w.a
  let y := if dis then a.w.b ||| b.w.b else a.w.b &&& b.w.b
  let zz := (z+(a.w.c &&& b.w.c))-(x ||| y)
  if (zz &&& g) != g then return []
  let some ws := tIns ⟨s,x,y,x ||| y,0⟩ v | return []
  let del (u v : ℕ) := ws.filter (fun w => w.s != u && w.s != v)
  return (if p==0 && q==0 then tChild g zz (del a.w.s b.w.s) else []) ++
    (if n+1 ≤ e && q==0 then tChild g (zz-a.w.c) (del b.w.s b.w.s) else []) ++
    (if n+1 ≤ e && p==0 then tChild g (zz-b.w.c) (del a.w.s a.w.s) else []) ++
    (if n+2 ≤ e then tChild g (zz-a.w.c-b.w.c) ws else [])
def tNode (d : Bool) (l m g e z which a b H : ℕ) (v : DW) : List DY := Id.run do
  let xs := mkX d l (wst d l v) v
  let xr := fr xs
  let xf := fs xs
  let unord (u : List X) := u.zipIdx.flatMap (fun (w,i) => (u.drop (i+1)).map (w,·))
  let pp := if which == 0 then unord xr ++ xr.flatMap (fun w => xf.map (w,·))
    else if which == 1 then (xs.filter (fun w => w.s==a)).flatMap (fun w => (xs.filter (fun u => u.s != a)).map (w,·))
    else if which == 2 then (xs.filter (fun w => w.s==a)).flatMap (fun w => (xs.filter (fun u => u.s==b)).map (w,·))
    else if which == 3 then unord xf else (unord xf).filter (fun (w,u) => hb H (w.s+u.s))
  return pp.flatMap (fun (x,y) => tGate m g e z v x y false ++ tGate m g e z v x y true)
def tNot (m g e z q : ℕ) (v : DW) : List (ℕ × DY) := v.flatMap fun a => Id.run do
  if a.s+1==q then return []
  let s := a.s ^^^ m
  let some ws := tIns ⟨s,a.b,a.a,a.c,0⟩ v | return []
  let zz := z-a.c
  return ((if v.length ≤ e then tChild g zz (ws.filter (fun w => w.s != a.s)) else []) ++
    (if v.length+1 ≤ e then tChild g (zz-a.c) ws else [])).map (s,·)
def tMoves (mode fuel l m g k t z y : ℕ) (v : DW) : List DS :=
  (tNode (pos t) l m g (k-t-y) z 0 0 0 0 v).map (fun (z,v) => deepPack mode fuel (k-1) t z v) ++
  (if t=0 then [] else
    let s := t-1
    (tNot m g (k-s-y) z 0 v).flatMap fun (q,z,v) =>
      (tBegin (pos s) l (k-s) v).flatMap fun y =>
        (tNode (pos s) l m g (k-1-s-y) z 1 q 0 0 v).map (fun (z,v) => deepPack mode fuel (k-2) s z v) ++
        (if s=0 then [] else
          let u := s-1
          (tNot m g (k-1-u-y) z (q+1) v).flatMap fun (q',z,v) =>
            (tBegin (pos u) l (k-1-u) v).flatMap fun y =>
              (tNode (pos u) l m g (k-2-u-y) z 2 q q' 0 v).map (fun (z,v) => deepPack mode fuel (k-3) u z v)))
def tLeaves (l m g K : ℕ) (s : DS) : List DS :=
  let (mode,fuel,k,t,z,ws) := s
  let v := ws.map fun (a,b,c,x,r) => (⟨a,b,c,x,r⟩ : W)
  if fuel=0 ∨ v.length≤1 then [] else (tBegin (pos t) l (k+1-t) v).flatMap fun y =>
    if mode=0 then tMoves 0 (fuel-1) l m g k t z y v else
      (tNode (pos t) l m g (k-t-y) z 3 0 0 0 v).map (fun (z,v) => deepPack 1 (fuel-1) (k-1) t z v) ++
      tMoves 0 K l m g k t z y v
def tRoot (R : ℕ → ℕ) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : List DS :=
  let l := lz Z
  let m := mz Z
  let g := pL (Q.map fun _ => 16)
  let B := pL (Q.map fun e => 16+(K-e.2))
  (dRows R E Q Z t).flatMap fun v => Id.run do
    if !(hasP (pwr E Z) v) || v.length > K+1-t || v.length ≤ 1 then return []
    let z := B-sumc v
    if (z &&& g) != g then return []
    return (tBegin (pos t) l (K+1-t) v).flatMap fun y =>
      (tNode (pos t) l m g (K-t-y) z 4 0 0 H v).map (fun (z,v) => deepPack 1 K (K-1) t z v) ++
      (if ph=1 then tMoves 0 K l m g K t z y v else [])

def dSel (ss : List DS) (ii : List ℕ) : List DS := ii.map (fun j => ss.getD j default)
def dGood (ev : DS → Bool) (ss : List DS) := ss.all (fun s => !(ev s))
theorem dCat {ev : DS → Bool} {u v : List DS} (h : dGood ev u = true) (k : dGood ev v = true) : dGood ev (u++v) = true := by
  change (u++v).all _ = true
  rw [List.all_append]
  exact Bool.and_eq_true_iff.mpr ⟨h,k⟩
theorem dOne {ev : DS → Bool} {s : DS} (h : ev s = false) : dGood ev [s] = true := by simp [dGood,h]
theorem dFord {ev : DS → Bool} {ss : List DS} (h : dGood ev ss = true) : ∀ x ∈ ss, ev x = false := by
  simpa only [dGood,List.all_eq_true,Bool.not_eq_true'] using h
end
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
def lplain : List ℕ := [63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 57, 59, 58, 61, 60, 62, 63, 457, 457, 457, 457, 457, 457, 457, 457, 457, 457, 457, 457, 457, 457, 939, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 458, 939, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 462, 939, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 461, 939, 304, 939, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 460, 939, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 459, 939, 285, 939, 355, 355, 939, 354, 354, 939, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 464, 939, 402, 402, 402, 939, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 463, 939, 386, 386, 386, 939, 416, 416, 416, 939, 415, 415, 415, 939, 440, 440, 440, 939, 466, 466, 466, 939, 465, 465, 939, 454, 454, 939, 453, 453, 453, 939, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 467, 939, 457, 458, 462, 461, 460, 459, 464, 463, 467, 939, 458, 939, 462, 939, 461, 464, 939, 457, 458, 462, 461, 304, 460, 459, 464, 402, 463, 467, 939, 460, 463, 939, 459, 939, 457, 458, 462, 461, 460, 459, 285, 464, 463, 386, 467, 939, 457, 458, 462, 461, 460, 459, 355, 464, 463, 416, 467, 939, 457, 458, 462, 461, 460, 459, 354, 464, 463, 415, 467, 939, 458, 462, 460, 939, 458, 461, 459, 939, 462, 461, 939, 460, 459, 939, 457, 458, 462, 461, 460, 459, 355, 354, 464, 463, 467, 939, 463, 939, 464, 939, 457, 458, 462, 461, 460, 459, 464, 402, 463, 386, 440, 467, 939, 464, 939, 457, 458, 462, 461, 460, 459, 464, 402, 463, 416, 466, 467, 939, 463, 939, 457, 458, 462, 461, 460, 459, 464, 463, 386, 415, 453, 467, 939, 457, 458, 462, 461, 460, 459, 464, 463, 416, 415, 467, 939, 457, 458, 462, 461, 460, 459, 464, 463, 440, 466, 454, 467, 939, 457, 458, 462, 461, 460, 459, 464, 463, 440, 465, 453, 467, 939, 457, 458, 462, 461, 460, 459, 464, 463, 466, 465, 467, 939, 457, 458, 462, 461, 460, 459, 464, 463, 454, 453, 467, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 939, 741, 777, 760, 801, 789, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 741, 743, 777, 760, 801, 789, 809, 805, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 741, 765, 777, 760, 801, 789, 809, 815, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 741, 763, 777, 760, 801, 789, 805, 815, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 777, 939, 741, 777, 748, 760, 801, 789, 809, 812, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 741, 777, 745, 760, 801, 789, 805, 812, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 760, 939, 801, 827, 939, 789, 827, 939, 741, 763, 777, 760, 801, 789, 827, 829, 844, 861, 874, 859, 886, 912, 899, 936, 924, 939, 777, 844, 874, 939, 741, 777, 748, 760, 801, 789, 827, 831, 844, 874, 846, 859, 886, 912, 899, 936, 924, 939, 760, 844, 859, 939, 801, 874, 886, 939, 789, 859, 886, 939, 844, 912, 899, 939, 874, 912, 936, 939, 899, 936, 939, 912, 924, 939, 859, 899, 924, 939, 741, 777, 760, 801, 789, 827, 844, 874, 859, 886, 912, 899, 936, 924, 939, 741, 741, 741, 741, 741, 741, 741, 741, 741, 939, 743, 939, 765, 939, 763, 763, 939, 777, 777, 777, 777, 777, 777, 777, 777, 777, 777, 777, 939, 748, 748, 939, 745, 939, 760, 760, 760, 760, 760, 760, 760, 760, 760, 760, 760, 939, 801, 801, 801, 801, 801, 801, 801, 801, 801, 801, 801, 939, 789, 789, 789, 789, 789, 789, 789, 789, 789, 789, 789, 939, 809, 809, 809, 939, 805, 805, 805, 939, 815, 815, 939, 812, 812, 939, 827, 827, 827, 827, 827, 827, 827, 827, 827, 827, 827, 939, 831, 939, 829, 939, 844, 844, 844, 844, 844, 844, 844, 844, 844, 844, 844, 844, 939, 861, 939, 874, 874, 874, 874, 874, 874, 874, 874, 874, 874, 874, 874, 939, 846, 939, 859, 859, 859, 859, 859, 859, 859, 859, 859, 859, 859, 859, 939, 886, 886, 886, 886, 886, 886, 886, 886, 886, 886, 886, 939, 912, 912, 912, 912, 912, 912, 912, 912, 912, 912, 912, 912, 939, 899, 899, 899, 899, 899, 899, 899, 899, 899, 899, 899, 899, 939, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 939, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 939]
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
lemma use1 : useFacts tblplain (0, 2) (1, 3) = true := by decide +kernel
lemma mirror1 (k t : ℕ) : Excluded k (1, 3) t → Excluded k (0, 2) t := pullExcluded actplain (liftFacts factsplain use1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use2 : useFacts tblplain (0, 3) (1, 2) = true := by decide +kernel
lemma mirror2 (k t : ℕ) : Excluded k (1, 2) t → Excluded k (0, 3) t := pullExcluded actplain (liftFacts factsplain use2)
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
lemma use10 : useFacts tblplain (2, 4) (3, 4) = true := by decide +kernel
lemma mirror10 (k t : ℕ) : Excluded k (3, 4) t → Excluded k (2, 4) t := pullExcluded actplain (liftFacts factsplain use10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use11 : useFacts tblplain (2, 5) (3, 5) = true := by decide +kernel
lemma mirror11 (k t : ℕ) : Excluded k (3, 5) t → Excluded k (2, 5) t := pullExcluded actplain (liftFacts factsplain use11)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use16 : useFacts tblplain (6, 2) (7, 3) = true := by decide +kernel
lemma mirror16 (k t : ℕ) : Excluded k (7, 3) t → Excluded k (6, 2) t := pullExcluded actplain (liftFacts factsplain use16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use17 : useFacts tblplain (6, 3) (7, 2) = true := by decide +kernel
lemma mirror17 (k t : ℕ) : Excluded k (7, 2) t → Excluded k (6, 3) t := pullExcluded actplain (liftFacts factsplain use17)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use18 : useFacts tblplain (6, 4) (7, 4) = true := by decide +kernel
lemma mirror18 (k t : ℕ) : Excluded k (7, 4) t → Excluded k (6, 4) t := pullExcluded actplain (liftFacts factsplain use18)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use19 : useFacts tblplain (6, 5) (7, 5) = true := by decide +kernel
lemma mirror19 (k t : ℕ) : Excluded k (7, 5) t → Excluded k (6, 5) t := pullExcluded actplain (liftFacts factsplain use19)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use26 : useFacts tblplain (8, 5) (9, 5) = true := by decide +kernel
lemma mirror26 (k t : ℕ) : Excluded k (9, 5) t → Excluded k (8, 5) t := pullExcluded actplain (liftFacts factsplain use26)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use27 : useFacts tblplain (9, 4) (8, 4) = true := by decide +kernel
lemma mirror27 (k t : ℕ) : Excluded k (8, 4) t → Excluded k (9, 4) t := pullExcluded actplain (liftFacts factsplain use27)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma use30 : useFacts tblplain (12, 0) (13, 0) = true := by decide +kernel
lemma mirror30 (k t : ℕ) : Excluded k (13, 0) t → Excluded k (12, 0) t := pullExcluded actplain (liftFacts factsplain use30)
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
def ready3 := prepSound ea3 q1_3 q2_3 extra_3 edgePrep3
noncomputable def ec3 (k t h p : ℕ) := chk [ea3] edgeQ3 0 k (remT (unaryE ea3) t) h p
def ready4 := prepSound ea4 q1_4 q2_4 extra_4 edgePrep4
noncomputable def ec4 (k t h p : ℕ) := chk [ea4] edgeQ4 0 k (remT (unaryE ea4) t) h p
def ready5 := prepSound ea5 q1_5 q2_5 extra_5 edgePrep5
noncomputable def ec5 (k t h p : ℕ) := chk [ea5] edgeQ5 0 k (remT (unaryE ea5) t) h p
def ready6 := prepSound ea6 q1_6 q2_6 extra_6 edgePrep6
noncomputable def ec6 (k t h p : ℕ) := chk [ea6] edgeQ6 0 k (remT (unaryE ea6) t) h p
def ready9 := prepSound ea9 q1_9 q2_9 extra_9 edgePrep9
noncomputable def ec9 (k t h p : ℕ) := chk [ea9] edgeQ9 0 k (remT (unaryE ea9) t) h p
def ready12 := prepSound ea12 q1_12 q2_12 extra_12 edgePrep12
noncomputable def ec12 (k t h p : ℕ) := chk [ea12] edgeQ12 0 k (remT (unaryE ea12) t) h p
def ready13 := prepSound ea13 q1_13 q2_13 extra_13 edgePrep13
noncomputable def ec13 (k t h p : ℕ) := chk [ea13] edgeQ13 0 k (remT (unaryE ea13) t) h p
def ready14 := prepSound ea14 q1_14 q2_14 extra_14 edgePrep14
noncomputable def ec14 (k t h p : ℕ) := chk [ea14] edgeQ14 0 k (remT (unaryE ea14) t) h p
def ready15 := prepSound ea15 q1_15 q2_15 extra_15 edgePrep15
noncomputable def ec15 (k t h p : ℕ) := chk [ea15] edgeQ15 0 k (remT (unaryE ea15) t) h p
def ready20 := prepSound ea20 q1_20 q2_20 extra_20 edgePrep20
noncomputable def ec20 (k t h p : ℕ) := chk [ea20] edgeQ20 0 k (remT (unaryE ea20) t) h p
def ready21 := prepSound ea21 q1_21 q2_21 extra_21 edgePrep21
noncomputable def ec21 (k t h p : ℕ) := chk [ea21] edgeQ21 0 k (remT (unaryE ea21) t) h p
def ready22 := prepSound ea22 q1_22 q2_22 extra_22 edgePrep22
noncomputable def ec22 (k t h p : ℕ) := chk [ea22] edgeQ22 0 k (remT (unaryE ea22) t) h p
def ready23 := prepSound ea23 q1_23 q2_23 extra_23 edgePrep23
noncomputable def ec23 (k t h p : ℕ) := chk [ea23] edgeQ23 0 k (remT (unaryE ea23) t) h p
def ready24 := prepSound ea24 q1_24 q2_24 extra_24 edgePrep24
noncomputable def ec24 (k t h p : ℕ) := chk [ea24] edgeQ24 0 k (remT (unaryE ea24) t) h p
def ready25 := prepSound ea25 q1_25 q2_25 extra_25 edgePrep25
noncomputable def ec25 (k t h p : ℕ) := chk [ea25] edgeQ25 0 k (remT (unaryE ea25) t) h p
def ready28 := prepSound ea28 q1_28 q2_28 extra_28 edgePrep28
noncomputable def ec28 (k t h p : ℕ) := chk [ea28] edgeQ28 0 k (remT (unaryE ea28) t) h p
def ready29 := prepSound ea29 q1_29 q2_29 extra_29 edgePrep29
noncomputable def ec29 (k t h p : ℕ) := chk [ea29] edgeQ29 0 k (remT (unaryE ea29) t) h p
def ready31 := prepSound ea31 q1_31 q2_31 extra_31 edgePrep31
noncomputable def ec31 (k t h p : ℕ) := chk [ea31] edgeQ31 0 k (remT (unaryE ea31) t) h p
def ready32 := prepSound ea32 q1_32 q2_32 extra_32 edgePrep32
noncomputable def ec32 (k t h p : ℕ) := chk [ea32] edgeQ32 0 k (remT (unaryE ea32) t) h p
def ready34 := prepSound ea34 q1_34 q2_34 extra_34 edgePrep34
noncomputable def ec34 (k t h p : ℕ) := chk [ea34] edgeQ34 0 k (remT (unaryE ea34) t) h p
def ready35 := prepSound ea35 q1_35 q2_35 extra_35 edgePrep35
noncomputable def ec35 (k t h p : ℕ) := chk [ea35] edgeQ35 0 k (remT (unaryE ea35) t) h p
set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
theorem leaf1 : ec0 11 1 FF 1 = false := by decide +kernel
lemma u0k11t1 : runCase ea0 edgeQ0 11 1 := by
  exact one leaf1
set_option maxRecDepth 100000 in
theorem leaf2 : ec0 11 2 FF 1 = false := by decide +kernel
lemma u0k11t2 : runCase ea0 edgeQ0 11 2 := by
  exact one leaf2
set_option maxRecDepth 100000 in
theorem leaf3 : ec0 11 3 FF 1 = false := by decide +kernel
lemma u0k11t3 : runCase ea0 edgeQ0 11 3 := by
  exact one leaf3
lemma lower0 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea0 edgeQ0 11 t := by
  interval_cases t
  · exact u0k11t0
  · exact u0k11t1
  · exact u0k11t2
  · exact u0k11t3
set_option maxRecDepth 100000 in
theorem leaf4 : ec3 11 0 FF 1 = false := by decide +kernel
lemma u3k11t0 : runCase ea3 edgeQ3 11 0 := by
  exact one leaf4
set_option maxRecDepth 100000 in
theorem leaf5 : ec3 11 1 FF 1 = false := by decide +kernel
lemma u3k11t1 : runCase ea3 edgeQ3 11 1 := by
  exact one leaf5
set_option maxRecDepth 100000 in
theorem leaf6 : ec3 11 2 FF 1 = false := by decide +kernel
lemma u3k11t2 : runCase ea3 edgeQ3 11 2 := by
  exact one leaf6
set_option maxRecDepth 100000 in
theorem leaf7 : ec3 11 3 FF 1 = false := by decide +kernel
lemma u3k11t3 : runCase ea3 edgeQ3 11 3 := by
  exact one leaf7
lemma lower3 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea3 edgeQ3 11 t := by
  interval_cases t
  · exact u3k11t0
  · exact u3k11t1
  · exact u3k11t2
  · exact u3k11t3
set_option maxRecDepth 100000 in
theorem leaf8 : ec4 11 0 FF 1 = false := by decide +kernel
lemma u4k11t0 : runCase ea4 edgeQ4 11 0 := by
  exact one leaf8
set_option maxRecDepth 100000 in
theorem leaf9 : ec4 11 1 FF 1 = false := by decide +kernel
lemma u4k11t1 : runCase ea4 edgeQ4 11 1 := by
  exact one leaf9
set_option maxRecDepth 100000 in
theorem leaf10 : ec4 11 2 FF 1 = false := by decide +kernel
lemma u4k11t2 : runCase ea4 edgeQ4 11 2 := by
  exact one leaf10
set_option maxRecDepth 100000 in
theorem leaf11 : ec4 11 3 FF 1 = false := by decide +kernel
lemma u4k11t3 : runCase ea4 edgeQ4 11 3 := by
  exact one leaf11
lemma lower4 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea4 edgeQ4 11 t := by
  interval_cases t
  · exact u4k11t0
  · exact u4k11t1
  · exact u4k11t2
  · exact u4k11t3
set_option maxRecDepth 100000 in
theorem leaf12 : ec5 11 0 FF 1 = false := by decide +kernel
lemma u5k11t0 : runCase ea5 edgeQ5 11 0 := by
  exact one leaf12
set_option maxRecDepth 100000 in
theorem leaf13 : ec5 11 1 FF 1 = false := by decide +kernel
lemma u5k11t1 : runCase ea5 edgeQ5 11 1 := by
  exact one leaf13
set_option maxRecDepth 100000 in
theorem leaf14 : ec5 11 2 FF 1 = false := by decide +kernel
lemma u5k11t2 : runCase ea5 edgeQ5 11 2 := by
  exact one leaf14
set_option maxRecDepth 100000 in
theorem leaf15 : ec5 11 3 FF 1 = false := by decide +kernel
lemma u5k11t3 : runCase ea5 edgeQ5 11 3 := by
  exact one leaf15
lemma lower5 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea5 edgeQ5 11 t := by
  interval_cases t
  · exact u5k11t0
  · exact u5k11t1
  · exact u5k11t2
  · exact u5k11t3
set_option maxRecDepth 100000 in
theorem leaf16 : ec6 11 0 FF 1 = false := by decide +kernel
lemma u6k11t0 : runCase ea6 edgeQ6 11 0 := by
  exact one leaf16
set_option maxRecDepth 100000 in
theorem leaf17 : ec6 11 1 FF 1 = false := by decide +kernel
lemma u6k11t1 : runCase ea6 edgeQ6 11 1 := by
  exact one leaf17
set_option maxRecDepth 100000 in
theorem leaf18 : ec6 11 2 FF 1 = false := by decide +kernel
lemma u6k11t2 : runCase ea6 edgeQ6 11 2 := by
  exact one leaf18
set_option maxRecDepth 100000 in
theorem leaf19 : ec6 11 3 FF 1 = false := by decide +kernel
lemma u6k11t3 : runCase ea6 edgeQ6 11 3 := by
  exact one leaf19
lemma lower6 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea6 edgeQ6 11 t := by
  interval_cases t
  · exact u6k11t0
  · exact u6k11t1
  · exact u6k11t2
  · exact u6k11t3
set_option maxRecDepth 100000 in
theorem leaf20 : ec9 11 0 FF 1 = false := by decide +kernel
lemma u9k11t0 : runCase ea9 edgeQ9 11 0 := by
  exact one leaf20
set_option maxRecDepth 100000 in
theorem leaf21 : ec9 11 1 FF 1 = false := by decide +kernel
lemma u9k11t1 : runCase ea9 edgeQ9 11 1 := by
  exact one leaf21
set_option maxRecDepth 100000 in
theorem leaf22 : ec9 11 2 FF 1 = false := by decide +kernel
lemma u9k11t2 : runCase ea9 edgeQ9 11 2 := by
  exact one leaf22
set_option maxRecDepth 100000 in
theorem leaf23 : ec9 11 3 FF 1 = false := by decide +kernel
lemma u9k11t3 : runCase ea9 edgeQ9 11 3 := by
  exact one leaf23
lemma lower9 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea9 edgeQ9 11 t := by
  interval_cases t
  · exact u9k11t0
  · exact u9k11t1
  · exact u9k11t2
  · exact u9k11t3
set_option maxRecDepth 100000 in
theorem leaf24 : ec12 11 0 FF 1 = false := by decide +kernel
lemma u12k11t0 : runCase ea12 edgeQ12 11 0 := by
  exact one leaf24
set_option maxRecDepth 100000 in
theorem leaf25 : ec12 11 1 FF 1 = false := by decide +kernel
lemma u12k11t1 : runCase ea12 edgeQ12 11 1 := by
  exact one leaf25
set_option maxRecDepth 100000 in
theorem leaf26 : ec12 11 2 FF 1 = false := by decide +kernel
lemma u12k11t2 : runCase ea12 edgeQ12 11 2 := by
  exact one leaf26
set_option maxRecDepth 100000 in
theorem leaf27 : ec12 11 3 FF 1 = false := by decide +kernel
lemma u12k11t3 : runCase ea12 edgeQ12 11 3 := by
  exact one leaf27
lemma lower12 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea12 edgeQ12 11 t := by
  interval_cases t
  · exact u12k11t0
  · exact u12k11t1
  · exact u12k11t2
  · exact u12k11t3
set_option maxRecDepth 100000 in
theorem leaf28 : ec13 11 0 FF 1 = false := by decide +kernel
lemma u13k11t0 : runCase ea13 edgeQ13 11 0 := by
  exact one leaf28
set_option maxRecDepth 100000 in
theorem leaf29 : ec13 11 1 FF 1 = false := by decide +kernel
lemma u13k11t1 : runCase ea13 edgeQ13 11 1 := by
  exact one leaf29
set_option maxRecDepth 100000 in
theorem leaf30 : ec13 11 2 FF 1 = false := by decide +kernel
lemma u13k11t2 : runCase ea13 edgeQ13 11 2 := by
  exact one leaf30
set_option maxRecDepth 100000 in
theorem leaf31 : ec13 11 3 FF 1 = false := by decide +kernel
lemma u13k11t3 : runCase ea13 edgeQ13 11 3 := by
  exact one leaf31
lemma lower13 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea13 edgeQ13 11 t := by
  interval_cases t
  · exact u13k11t0
  · exact u13k11t1
  · exact u13k11t2
  · exact u13k11t3
set_option maxRecDepth 100000 in
theorem leaf32 : ec14 11 0 FF 1 = false := by decide +kernel
lemma u14k11t0 : runCase ea14 edgeQ14 11 0 := by
  exact one leaf32
set_option maxRecDepth 100000 in
theorem leaf33 : ec14 11 1 FF 1 = false := by decide +kernel
lemma u14k11t1 : runCase ea14 edgeQ14 11 1 := by
  exact one leaf33
set_option maxRecDepth 100000 in
theorem leaf34 : ec14 11 2 FF 1 = false := by decide +kernel
lemma u14k11t2 : runCase ea14 edgeQ14 11 2 := by
  exact one leaf34
set_option maxRecDepth 100000 in
theorem leaf35 : ec14 11 3 FF 1 = false := by decide +kernel
lemma u14k11t3 : runCase ea14 edgeQ14 11 3 := by
  exact one leaf35
lemma lower14 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea14 edgeQ14 11 t := by
  interval_cases t
  · exact u14k11t0
  · exact u14k11t1
  · exact u14k11t2
  · exact u14k11t3
set_option maxRecDepth 100000 in
theorem leaf36 : ec15 11 0 FF 1 = false := by decide +kernel
lemma u15k11t0 : runCase ea15 edgeQ15 11 0 := by
  exact one leaf36
set_option maxRecDepth 100000 in
theorem leaf37 : ec15 11 1 FF 1 = false := by decide +kernel
lemma u15k11t1 : runCase ea15 edgeQ15 11 1 := by
  exact one leaf37
set_option maxRecDepth 100000 in
theorem leaf38 : ec15 11 2 FF 1 = false := by decide +kernel
lemma u15k11t2 : runCase ea15 edgeQ15 11 2 := by
  exact one leaf38
set_option maxRecDepth 100000 in
theorem leaf39 : ec15 11 3 FF 1 = false := by decide +kernel
lemma u15k11t3 : runCase ea15 edgeQ15 11 3 := by
  exact one leaf39
lemma lower15 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea15 edgeQ15 11 t := by
  interval_cases t
  · exact u15k11t0
  · exact u15k11t1
  · exact u15k11t2
  · exact u15k11t3
set_option maxRecDepth 100000 in
theorem leaf40 : ec20 11 0 FF 1 = false := by decide +kernel
lemma u20k11t0 : runCase ea20 edgeQ20 11 0 := by
  exact one leaf40
set_option maxRecDepth 100000 in
theorem leaf41 : ec20 11 1 FF 1 = false := by decide +kernel
lemma u20k11t1 : runCase ea20 edgeQ20 11 1 := by
  exact one leaf41
set_option maxRecDepth 100000 in
theorem leaf42 : ec20 11 2 FF 1 = false := by decide +kernel
lemma u20k11t2 : runCase ea20 edgeQ20 11 2 := by
  exact one leaf42
set_option maxRecDepth 100000 in
theorem leaf43 : ec20 11 3 FF 1 = false := by decide +kernel
lemma u20k11t3 : runCase ea20 edgeQ20 11 3 := by
  exact one leaf43
lemma lower20 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea20 edgeQ20 11 t := by
  interval_cases t
  · exact u20k11t0
  · exact u20k11t1
  · exact u20k11t2
  · exact u20k11t3
set_option maxRecDepth 100000 in
theorem leaf44 : ec21 11 0 FF 1 = false := by decide +kernel
lemma u21k11t0 : runCase ea21 edgeQ21 11 0 := by
  exact one leaf44
set_option maxRecDepth 100000 in
theorem leaf45 : ec21 11 1 FF 1 = false := by decide +kernel
lemma u21k11t1 : runCase ea21 edgeQ21 11 1 := by
  exact one leaf45
set_option maxRecDepth 100000 in
theorem leaf46 : ec21 11 2 FF 1 = false := by decide +kernel
lemma u21k11t2 : runCase ea21 edgeQ21 11 2 := by
  exact one leaf46
set_option maxRecDepth 100000 in
theorem leaf47 : ec21 11 3 FF 1 = false := by decide +kernel
lemma u21k11t3 : runCase ea21 edgeQ21 11 3 := by
  exact one leaf47
lemma lower21 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea21 edgeQ21 11 t := by
  interval_cases t
  · exact u21k11t0
  · exact u21k11t1
  · exact u21k11t2
  · exact u21k11t3
set_option maxRecDepth 100000 in
theorem leaf48 : ec22 11 0 FF 1 = false := by decide +kernel
lemma u22k11t0 : runCase ea22 edgeQ22 11 0 := by
  exact one leaf48
set_option maxRecDepth 100000 in
theorem leaf49 : ec22 11 1 FF 1 = false := by decide +kernel
lemma u22k11t1 : runCase ea22 edgeQ22 11 1 := by
  exact one leaf49
set_option maxRecDepth 100000 in
theorem leaf50 : ec22 11 2 FF 1 = false := by decide +kernel
lemma u22k11t2 : runCase ea22 edgeQ22 11 2 := by
  exact one leaf50
set_option maxRecDepth 100000 in
theorem leaf51 : ec22 11 3 FF 1 = false := by decide +kernel
lemma u22k11t3 : runCase ea22 edgeQ22 11 3 := by
  exact one leaf51
lemma lower22 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea22 edgeQ22 11 t := by
  interval_cases t
  · exact u22k11t0
  · exact u22k11t1
  · exact u22k11t2
  · exact u22k11t3
set_option maxRecDepth 100000 in
theorem leaf52 : ec23 11 0 FF 1 = false := by decide +kernel
lemma u23k11t0 : runCase ea23 edgeQ23 11 0 := by
  exact one leaf52
set_option maxRecDepth 100000 in
theorem leaf53 : ec23 11 1 FF 1 = false := by decide +kernel
lemma u23k11t1 : runCase ea23 edgeQ23 11 1 := by
  exact one leaf53
set_option maxRecDepth 100000 in
theorem leaf54 : ec23 11 2 FF 1 = false := by decide +kernel
lemma u23k11t2 : runCase ea23 edgeQ23 11 2 := by
  exact one leaf54
set_option maxRecDepth 100000 in
theorem leaf55 : ec23 11 3 FF 1 = false := by decide +kernel
lemma u23k11t3 : runCase ea23 edgeQ23 11 3 := by
  exact one leaf55
lemma lower23 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea23 edgeQ23 11 t := by
  interval_cases t
  · exact u23k11t0
  · exact u23k11t1
  · exact u23k11t2
  · exact u23k11t3
set_option maxRecDepth 100000 in
theorem leaf56 : ec24 11 0 FF 1 = false := by decide +kernel
lemma u24k11t0 : runCase ea24 edgeQ24 11 0 := by
  exact one leaf56
set_option maxRecDepth 100000 in
theorem leaf57 : ec24 11 1 FF 1 = false := by decide +kernel
lemma u24k11t1 : runCase ea24 edgeQ24 11 1 := by
  exact one leaf57
set_option maxRecDepth 100000 in
theorem leaf58 : ec24 11 2 FF 1 = false := by decide +kernel
lemma u24k11t2 : runCase ea24 edgeQ24 11 2 := by
  exact one leaf58
set_option maxRecDepth 100000 in
theorem leaf59 : ec24 11 3 FF 1 = false := by decide +kernel
lemma u24k11t3 : runCase ea24 edgeQ24 11 3 := by
  exact one leaf59
lemma lower24 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea24 edgeQ24 11 t := by
  interval_cases t
  · exact u24k11t0
  · exact u24k11t1
  · exact u24k11t2
  · exact u24k11t3
set_option maxRecDepth 100000 in
theorem leaf60 : ec25 11 0 FF 1 = false := by decide +kernel
lemma u25k11t0 : runCase ea25 edgeQ25 11 0 := by
  exact one leaf60
set_option maxRecDepth 100000 in
theorem leaf61 : ec25 11 1 FF 1 = false := by decide +kernel
lemma u25k11t1 : runCase ea25 edgeQ25 11 1 := by
  exact one leaf61
set_option maxRecDepth 100000 in
theorem leaf62 : ec25 11 2 FF 1 = false := by decide +kernel
lemma u25k11t2 : runCase ea25 edgeQ25 11 2 := by
  exact one leaf62
set_option maxRecDepth 100000 in
theorem leaf63 : ec25 11 3 FF 1 = false := by decide +kernel
lemma u25k11t3 : runCase ea25 edgeQ25 11 3 := by
  exact one leaf63
lemma lower25 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea25 edgeQ25 11 t := by
  interval_cases t
  · exact u25k11t0
  · exact u25k11t1
  · exact u25k11t2
  · exact u25k11t3
set_option maxRecDepth 100000 in
theorem leaf64 : ec28 11 0 FF 1 = false := by decide +kernel
lemma u28k11t0 : runCase ea28 edgeQ28 11 0 := by
  exact one leaf64
set_option maxRecDepth 100000 in
theorem leaf65 : ec28 11 1 FF 1 = false := by decide +kernel
lemma u28k11t1 : runCase ea28 edgeQ28 11 1 := by
  exact one leaf65
set_option maxRecDepth 100000 in
theorem leaf66 : ec28 11 2 FF 1 = false := by decide +kernel
lemma u28k11t2 : runCase ea28 edgeQ28 11 2 := by
  exact one leaf66
set_option maxRecDepth 100000 in
theorem leaf67 : ec28 11 3 FF 1 = false := by decide +kernel
lemma u28k11t3 : runCase ea28 edgeQ28 11 3 := by
  exact one leaf67
lemma lower28 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea28 edgeQ28 11 t := by
  interval_cases t
  · exact u28k11t0
  · exact u28k11t1
  · exact u28k11t2
  · exact u28k11t3
set_option maxRecDepth 100000 in
theorem leaf68 : ec29 11 0 FF 1 = false := by decide +kernel
lemma u29k11t0 : runCase ea29 edgeQ29 11 0 := by
  exact one leaf68
set_option maxRecDepth 100000 in
theorem leaf69 : ec29 11 1 FF 1 = false := by decide +kernel
lemma u29k11t1 : runCase ea29 edgeQ29 11 1 := by
  exact one leaf69
set_option maxRecDepth 100000 in
theorem leaf70 : ec29 11 2 FF 1 = false := by decide +kernel
lemma u29k11t2 : runCase ea29 edgeQ29 11 2 := by
  exact one leaf70
set_option maxRecDepth 100000 in
theorem leaf71 : ec29 11 3 FF 1 = false := by decide +kernel
lemma u29k11t3 : runCase ea29 edgeQ29 11 3 := by
  exact one leaf71
lemma lower29 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea29 edgeQ29 11 t := by
  interval_cases t
  · exact u29k11t0
  · exact u29k11t1
  · exact u29k11t2
  · exact u29k11t3
set_option maxRecDepth 100000 in
theorem leaf72 : ec31 11 0 FF 1 = false := by decide +kernel
lemma u31k11t0 : runCase ea31 edgeQ31 11 0 := by
  exact one leaf72
set_option maxRecDepth 100000 in
theorem leaf73 : ec31 11 1 FF 1 = false := by decide +kernel
lemma u31k11t1 : runCase ea31 edgeQ31 11 1 := by
  exact one leaf73
set_option maxRecDepth 100000 in
theorem leaf74 : ec31 11 2 FF 1 = false := by decide +kernel
lemma u31k11t2 : runCase ea31 edgeQ31 11 2 := by
  exact one leaf74
set_option maxRecDepth 100000 in
theorem leaf75 : ec31 11 3 FF 1 = false := by decide +kernel
lemma u31k11t3 : runCase ea31 edgeQ31 11 3 := by
  exact one leaf75
lemma lower31 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea31 edgeQ31 11 t := by
  interval_cases t
  · exact u31k11t0
  · exact u31k11t1
  · exact u31k11t2
  · exact u31k11t3
set_option maxRecDepth 100000 in
theorem leaf76 : ec32 11 0 FF 1 = false := by decide +kernel
lemma u32k11t0 : runCase ea32 edgeQ32 11 0 := by
  exact one leaf76
set_option maxRecDepth 100000 in
theorem leaf77 : ec32 11 1 FF 1 = false := by decide +kernel
lemma u32k11t1 : runCase ea32 edgeQ32 11 1 := by
  exact one leaf77
set_option maxRecDepth 100000 in
theorem leaf78 : ec32 11 2 FF 1 = false := by decide +kernel
lemma u32k11t2 : runCase ea32 edgeQ32 11 2 := by
  exact one leaf78
set_option maxRecDepth 100000 in
theorem leaf79 : ec32 11 3 FF 1 = false := by decide +kernel
lemma u32k11t3 : runCase ea32 edgeQ32 11 3 := by
  exact one leaf79
lemma lower32 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea32 edgeQ32 11 t := by
  interval_cases t
  · exact u32k11t0
  · exact u32k11t1
  · exact u32k11t2
  · exact u32k11t3
set_option maxRecDepth 100000 in
theorem leaf80 : ec34 11 0 FF 1 = false := by decide +kernel
lemma u34k11t0 : runCase ea34 edgeQ34 11 0 := by
  exact one leaf80
set_option maxRecDepth 100000 in
theorem leaf81 : ec34 11 1 FF 1 = false := by decide +kernel
lemma u34k11t1 : runCase ea34 edgeQ34 11 1 := by
  exact one leaf81
set_option maxRecDepth 100000 in
theorem leaf82 : ec34 11 2 FF 1 = false := by decide +kernel
lemma u34k11t2 : runCase ea34 edgeQ34 11 2 := by
  exact one leaf82
set_option maxRecDepth 100000 in
theorem leaf83 : ec34 11 3 FF 1 = false := by decide +kernel
lemma u34k11t3 : runCase ea34 edgeQ34 11 3 := by
  exact one leaf83
lemma lower34 {t : ℕ} (ha : 0 ≤ t) (hb : t ≤ 3) : runCase ea34 edgeQ34 11 t := by
  interval_cases t
  · exact u34k11t0
  · exact u34k11t1
  · exact u34k11t2
  · exact u34k11t3
set_option maxRecDepth 100000 in
theorem leaf84 : ec35 11 0 FF 1 = false := by decide +kernel
lemma u35k11t0 : runCase ea35 edgeQ35 11 0 := by
  exact one leaf84
set_option maxRecDepth 100000 in
theorem leaf85 : ec35 11 1 FF 1 = false := by decide +kernel
lemma u35k11t1 : runCase ea35 edgeQ35 11 1 := by
  exact one leaf85
set_option maxRecDepth 100000 in
theorem leaf86 : ec35 11 2 FF 1 = false := by decide +kernel
lemma u35k11t2 : runCase ea35 edgeQ35 11 2 := by
  exact one leaf86
set_option maxRecDepth 100000 in
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
  · exact mirror1 _ _ (afterEdge (by decide) base (e:=ea6) (by decide +kernel) ready6 (lower6 ha hb))
  · exact mirror2 _ _ (afterEdge (by decide) base (e:=ea5) (by decide +kernel) ready5 (lower5 ha hb))
  · exact afterEdge (by decide) base (e:=ea3) (by decide +kernel) ready3 (lower3 ha hb)
  · exact afterEdge (by decide) base (e:=ea4) (by decide +kernel) ready4 (lower4 ha hb)
  · exact afterEdge (by decide) base (e:=ea5) (by decide +kernel) ready5 (lower5 ha hb)
  · exact afterEdge (by decide) base (e:=ea6) (by decide +kernel) ready6 (lower6 ha hb)
  · exact mirror7 _ _ (afterEdge (by decide) base (e:=ea3) (by decide +kernel) ready3 (lower3 ha hb))
  · exact mirror8 _ _ (afterEdge (by decide) base (e:=ea4) (by decide +kernel) ready4 (lower4 ha hb))
  · exact afterEdge (by decide) base (e:=ea9) (by decide +kernel) ready9 (lower9 ha hb)
  · exact mirror10 _ _ (afterEdge (by decide) base (e:=ea12) (by decide +kernel) ready12 (lower12 ha hb))
  · exact mirror11 _ _ (afterEdge (by decide) base (e:=ea13) (by decide +kernel) ready13 (lower13 ha hb))
  · exact afterEdge (by decide) base (e:=ea12) (by decide +kernel) ready12 (lower12 ha hb)
  · exact afterEdge (by decide) base (e:=ea13) (by decide +kernel) ready13 (lower13 ha hb)
  · exact afterEdge (by decide) base (e:=ea14) (by decide +kernel) ready14 (lower14 ha hb)
  · exact afterEdge (by decide) base (e:=ea15) (by decide +kernel) ready15 (lower15 ha hb)
  · exact mirror16 _ _ (afterEdge (by decide) base (e:=ea21) (by decide +kernel) ready21 (lower21 ha hb))
  · exact mirror17 _ _ (afterEdge (by decide) base (e:=ea20) (by decide +kernel) ready20 (lower20 ha hb))
  · exact mirror18 _ _ (afterEdge (by decide) base (e:=ea22) (by decide +kernel) ready22 (lower22 ha hb))
  · exact mirror19 _ _ (afterEdge (by decide) base (e:=ea23) (by decide +kernel) ready23 (lower23 ha hb))
  · exact afterEdge (by decide) base (e:=ea20) (by decide +kernel) ready20 (lower20 ha hb)
  · exact afterEdge (by decide) base (e:=ea21) (by decide +kernel) ready21 (lower21 ha hb)
  · exact afterEdge (by decide) base (e:=ea22) (by decide +kernel) ready22 (lower22 ha hb)
  · exact afterEdge (by decide) base (e:=ea23) (by decide +kernel) ready23 (lower23 ha hb)
  · exact afterEdge (by decide) base (e:=ea24) (by decide +kernel) ready24 (lower24 ha hb)
  · exact afterEdge (by decide) base (e:=ea25) (by decide +kernel) ready25 (lower25 ha hb)
  · exact mirror26 _ _ (afterEdge (by decide) base (e:=ea28) (by decide +kernel) ready28 (lower28 ha hb))
  · exact mirror27 _ _ (afterEdge (by decide) base (e:=ea25) (by decide +kernel) ready25 (lower25 ha hb))
  · exact afterEdge (by decide) base (e:=ea28) (by decide +kernel) ready28 (lower28 ha hb)
  · exact afterEdge (by decide) base (e:=ea29) (by decide +kernel) ready29 (lower29 ha hb)
  · exact mirror30 _ _ (afterEdge (by decide) base (e:=ea31) (by decide +kernel) ready31 (lower31 ha hb))
  · exact afterEdge (by decide) base (e:=ea31) (by decide +kernel) ready31 (lower31 ha hb)
  · exact afterEdge (by decide) base (e:=ea32) (by decide +kernel) ready32 (lower32 ha hb)
  · exact mirror33 _ _ (afterEdge (by decide) base (e:=ea32) (by decide +kernel) ready32 (lower32 ha hb))
  · exact afterEdge (by decide) base (e:=ea34) (by decide +kernel) ready34 (lower34 ha hb)
  · exact afterEdge (by decide) base (e:=ea35) (by decide +kernel) ready35 (lower35 ha hb)
set_option maxRecDepth 100000 in
theorem leaf88 : ec23 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf89 : ec23 12 1 0x5018010580010000004002020000a100b0400041040005000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf90 : ec23 12 1 0x2202010400000880458108400000080020000d0000a00000484 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf91 : ec23 12 1 0x27000000200002b020088200000001101100800020400094008000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf92 : ec23 12 1 0xc100000010004000000001000084064c4008102008102900a00 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf93 : ec23 12 1 0xc040000c80000100710168024880010008000200000000000041 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf94 : ec23 12 1 0x2000140000a04040002402210140800000004000884020082120 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf95 : ec23 12 1 0x8000200010000080300000000120000000064380c01040824001a 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf96 : ec23 12 1 0x100100000028040204000000008000220020000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf97 : ec23 12 1 0x88020000000000000000000014000001000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf98 : ec23 12 1 0x1000000206000000000000000400000000000000100000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf99 : ec23 12 1 0xc840000100008200814800020c0000100001222001430000 0 = false := by decide +kernel
lemma u23k12t1 : runCase ea23 edgeQ23 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec23 12 1) leaf88 (addMask leaf89 (addMask leaf90 (addMask leaf91 (addMask leaf92 (addMask leaf93 (addMask leaf94 (addMask leaf95 (addMask leaf96 (addMask leaf97 (addMask leaf98 (addMask leaf99 endMasks)))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf100 : ec23 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf101 : ec23 12 2 0xf77ed9a77a8953c4346dab5b898fb4500acbc43c3369894ad1c7 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf102 : ec23 12 2 0x3f088126588576ac3bcb9254a476704baff5343bc3cc9676b52e38 0 = false := by decide +kernel
lemma u23k12t2 : runCase ea23 edgeQ23 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec23 12 2) leaf100 (addMask leaf101 (addMask leaf102 endMasks))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf103 : ec23 12 3 FF 1 = false := by decide +kernel
lemma u23k12t3 : runCase ea23 edgeQ23 12 3 := by
  exact one leaf103
lemma N23 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea23 (remT (unaryE ea23) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea23) (by decide +kernel) ready23 u23k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea23) (by decide +kernel) ready23 u23k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea23) (by decide +kernel) ready23 u23k12t3
set_option maxRecDepth 100000 in
theorem leaf104 : ec4 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf105 : ec4 12 1 0x8000202c0000000000000008030280000141001004002210000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf106 : ec4 12 1 0x404010800000040200a0000400808428800000000000000402800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf107 : ec4 12 1 0x10100050100000000200120040040000028002008028400000040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf108 : ec4 12 1 0x203000002018000100000002104400000202400004000200800100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf109 : ec4 12 1 0x200004000062010041001000200100000000290800800080002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf110 : ec4 12 1 0x800800800420080000020082000000100081000040004802000c 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf111 : ec4 12 1 0x4082300c210804000000c0002002004000000000000001000010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf112 : ec4 12 1 0x80010000000400003508410000080000410020000002030000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf113 : ec4 12 1 0x400000010008012000000000800001000400000000004000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf114 : ec4 12 1 0x100000000000000001042100080100000000108000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf115 : ec4 12 1 0x4000000000028000000c291000000044208040080100001400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf116 : ec4 12 1 0x20020000000000004004000000100000080000000200004000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf117 : ec4 12 1 0x40800000000000000000000802050080040200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf118 : ec4 12 1 0x100004801002809000000800000004010000004020101000000081 0 = false := by decide +kernel
lemma u4k12t1 : runCase ea4 edgeQ4 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec4 12 1) leaf104 (addMask leaf105 (addMask leaf106 (addMask leaf107 (addMask leaf108 (addMask leaf109 (addMask leaf110 (addMask leaf111 (addMask leaf112 (addMask leaf113 (addMask leaf114 (addMask leaf115 (addMask leaf116 (addMask leaf117 (addMask leaf118 endMasks))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf119 : ec4 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf120 : ec4 12 2 0x2e6f2b103064813502c2004487d82085903ee852508020c423b020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf121 : ec4 12 2 0x190d006ca022e8a0c09c5034822cc402bc1122c8050c213d0074f 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf122 : ec4 12 2 0x100004e905995040f1343ab83005133a440005812f2f1d280c4890 0 = false := by decide +kernel
lemma u4k12t2 : runCase ea4 edgeQ4 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec4 12 2) leaf119 (addMask leaf120 (addMask leaf121 (addMask leaf122 endMasks)))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf123 : ec4 12 3 FF 1 = false := by decide +kernel
lemma u4k12t3 : runCase ea4 edgeQ4 12 3 := by
  exact one leaf123
lemma N4 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea4 (remT (unaryE ea4) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea4) (by decide +kernel) ready4 u4k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea4) (by decide +kernel) ready4 u4k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea4) (by decide +kernel) ready4 u4k12t3
set_option maxRecDepth 100000 in
theorem leaf124 : ec0 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf125 : ec0 12 1 0x200212000000800000001042a010000480010002000404 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf126 : ec0 12 1 0x100000008000021200000044200080000000032a000008008008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf127 : ec0 12 1 0x20028010400000000001902004640004100000001800000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf128 : ec0 12 1 0x100000480024040000000401000000200840000000280010060080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf129 : ec0 12 1 0x2884200000602000002000000000000002140010000400090001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf130 : ec0 12 1 0x400008240010000000020080020000001a10004003100001000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf131 : ec0 12 1 0x240001000000000400000010000081100600004000000a01900000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf132 : ec0 12 1 0x8002000000005024000000020800000000000840124040000240 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf133 : ec0 12 1 0x100040000008000000000010000000004000000008000600000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf134 : ec0 12 1 0x10000000018000000000080000002040000000000040000000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf135 : ec0 12 1 0x4000000001000841944000308000000020401000000000000002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf136 : ec0 12 1 0x2500000008000002a0200800004080008022000000024000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf137 : ec0 12 1 0x800000000080000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf138 : ec0 12 1 0x1000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf139 : ec0 12 1 0x40000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf140 : ec0 12 1 0x80000000000080000000000000000000000000000400000000100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf141 : ec0 12 1 0x20800000100410000000100000000080000000080000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf142 : ec0 12 1 0x10510000000800000c001008010080008000000000006810 0 = false := by decide +kernel
lemma u0k12t1 : runCase ea0 edgeQ0 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec0 12 1) leaf124 (addMask leaf125 (addMask leaf126 (addMask leaf127 (addMask leaf128 (addMask leaf129 (addMask leaf130 (addMask leaf131 (addMask leaf132 (addMask leaf133 (addMask leaf134 (addMask leaf135 (addMask leaf136 (addMask leaf137 (addMask leaf138 (addMask leaf139 (addMask leaf140 (addMask leaf141 (addMask leaf142 endMasks))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf143 : ec0 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf144 : ec0 12 2 0x84e80a243921158058635c400a96446ed13515022273b00200906 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf145 : ec0 12 2 0x26112501246c6ea53868023805129388022c020fc400801917b461 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf146 : ec0 12 2 0x11a05a5c98018002c211c803fa44083110c0aca019d844e6c84298 0 = false := by decide +kernel
lemma u0k12t2 : runCase ea0 edgeQ0 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec0 12 2) leaf143 (addMask leaf144 (addMask leaf145 (addMask leaf146 endMasks)))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf147 : ec0 12 3 FF 1 = false := by decide +kernel
lemma u0k12t3 : runCase ea0 edgeQ0 12 3 := by
  exact one leaf147
lemma N0 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea0 (remT (unaryE ea0) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea0) (by decide +kernel) ready0 u0k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea0) (by decide +kernel) ready0 u0k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea0) (by decide +kernel) ready0 u0k12t3
set_option maxRecDepth 100000 in
theorem leaf148 : ec15 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf149 : ec15 12 1 0x100000000000000000001000000000000000000400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf150 : ec15 12 1 0x4000000800000000000000001000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf151 : ec15 12 1 0x2000000000800000000040000000000000080004800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf152 : ec15 12 1 0x180402000000000080008000100006810004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf153 : ec15 12 1 0x20002000000004000004040082002000010020000004000100000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf154 : ec15 12 1 0x100000000080000080010100000081000800300000000010080000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf155 : ec15 12 1 0x40020020040080000020080004014005000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf156 : ec15 12 1 0x400000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf157 : ec15 12 1 0x8000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf158 : ec15 12 1 0x100000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf159 : ec15 12 1 0x200000000000000801000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf160 : ec15 12 1 0x4000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf161 : ec15 12 1 0x400000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf162 : ec15 12 1 0x1000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf163 : ec15 12 1 0x400000000000000000000000100000400000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf164 : ec15 12 1 0x18080800010400000000000000400000080000028000220000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf165 : ec15 12 1 0x1201400000000000000000104000000040080000040040042 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf166 : ec15 12 1 0x1000020010000000620000022040008000300 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf167 : ec15 12 1 0x280000000040000400000400000000000a00000008002000a001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf168 : ec15 12 1 0x8000200040400000801200021000000000200200000008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf169 : ec15 12 1 0xd0600100000000200020000040800000000001000002000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf170 : ec15 12 1 0x4030000000800000000100000014040800200810000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf171 : ec15 12 1 0x200000800228840000008000000008000000000408000000000010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf172 : ec15 12 1 0x1000000000001008001200424000002000000050000000000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf173 : ec15 12 1 0x46000088100002008008000800000002800000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf174 : ec15 12 1 0xa0000110002002200000000000008000000000000100001400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf175 : ec15 12 1 0x40000001100010000010200050000000000100000400000080 0 = false := by decide +kernel
lemma u15k12t1 : runCase ea15 edgeQ15 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec15 12 1) leaf148 (addMask leaf149 (addMask leaf150 (addMask leaf151 (addMask leaf152 (addMask leaf153 (addMask leaf154 (addMask leaf155 (addMask leaf156 (addMask leaf157 (addMask leaf158 (addMask leaf159 (addMask leaf160 (addMask leaf161 (addMask leaf162 (addMask leaf163 (addMask leaf164 (addMask leaf165 (addMask leaf166 (addMask leaf167 (addMask leaf168 (addMask leaf169 (addMask leaf170 (addMask leaf171 (addMask leaf172 (addMask leaf173 (addMask leaf174 (addMask leaf175 endMasks)))))))))))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf176 : ec15 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf177 : ec15 12 2 0x80014002002040484023520040004844ac1000c0288012218800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf178 : ec15 12 2 0x140204a01190818806000001028081041103400000052004102428 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf179 : ec15 12 2 0x2080c20081000930080502020100800899809024241c24040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf180 : ec15 12 2 0x1312004400d400001209c04a5090c018200202400000880000280 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf181 : ec15 12 2 0x24cc80020420400000c0020080402222050040326401420001003 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf182 : ec15 12 2 0x2800101380001227b00040080012508000000240109001080c0114 0 = false := by decide +kernel
lemma u15k12t2 : runCase ea15 edgeQ15 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec15 12 2) leaf176 (addMask leaf177 (addMask leaf178 (addMask leaf179 (addMask leaf180 (addMask leaf181 (addMask leaf182 endMasks))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf183 : ec15 12 3 FF 1 = false := by decide +kernel
lemma u15k12t3 : runCase ea15 edgeQ15 12 3 := by
  exact one leaf183
lemma N15 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea15 (remT (unaryE ea15) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea15) (by decide +kernel) ready15 u15k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea15) (by decide +kernel) ready15 u15k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea15) (by decide +kernel) ready15 u15k12t3
set_option maxRecDepth 100000 in
theorem leaf184 : ec13 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf185 : ec13 12 1 0x41849400000208020000842201040320060100020000100002900 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf186 : ec13 12 1 0x2240002208004090800018000804000010600480c0029810001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf187 : ec13 12 1 0x100989405010300914010000002010080004802011000040010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf188 : ec13 12 1 0x190000010800024012000320010019080400400105002000001282 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf189 : ec13 12 1 0x1220000a1800806000000024008080028182801200402a0004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf190 : ec13 12 1 0x2080000220804020400624840a402000010800240000c404004000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf191 : ec13 12 1 0x80000010000000000000108004044010281000000000000048 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf192 : ec13 12 1 0x22000000040000800001000000200003804000000000200408000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf193 : ec13 12 1 0x4400044100041004008008440900000200000010e00892100420 0 = false := by decide +kernel
lemma u13k12t1 : runCase ea13 edgeQ13 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec13 12 1) leaf184 (addMask leaf185 (addMask leaf186 (addMask leaf187 (addMask leaf188 (addMask leaf189 (addMask leaf190 (addMask leaf191 (addMask leaf192 (addMask leaf193 endMasks)))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf194 : ec13 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf195 : ec13 12 2 0x3feb7a6ea264def4b30d86cd0fb4b84007e20d841620da6b3ebe41 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf196 : ec13 12 2 0x1485915d9b210b4cf27932f04b47bff81df27be9df2594c141be 0 = false := by decide +kernel
lemma u13k12t2 : runCase ea13 edgeQ13 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec13 12 2) leaf194 (addMask leaf195 (addMask leaf196 endMasks))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf197 : ec13 12 3 FF 1 = false := by decide +kernel
lemma u13k12t3 : runCase ea13 edgeQ13 12 3 := by
  exact one leaf197
lemma N13 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea13 (remT (unaryE ea13) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea13) (by decide +kernel) ready13 u13k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea13) (by decide +kernel) ready13 u13k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea13) (by decide +kernel) ready13 u13k12t3
set_option maxRecDepth 100000 in
theorem leaf198 : ec6 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf199 : ec6 12 1 0x30020000000040100022808000060400000100204003002208000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf200 : ec6 12 1 0x3000000010084800c8480130080100100000080040100000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf201 : ec6 12 1 0x1c40040000480010000004008000030020002012000000900050 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf202 : ec6 12 1 0x8000110400020000000000200100a000000000000000000000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf203 : ec6 12 1 0x4000000000000000000000000000000020000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf204 : ec6 12 1 0x202000000000000000000000000000000000000000000000001000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf205 : ec6 12 1 0x400001000010000004000000000000000000080000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf206 : ec6 12 1 0x8012620000000001104000240900200014000000410000040002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf207 : ec6 12 1 0x1a000000082000000002000490012a9000000401000300 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf208 : ec6 12 1 0x88000000004240022000001400024a010800800010400800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf209 : ec6 12 1 0x80d2000000000050080400884080000100000060030004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf210 : ec6 12 1 0x10100110820000000400000002400844000300208004028 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf211 : ec6 12 1 0x44008000008820204001000800001000800400060080004002080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf212 : ec6 12 1 0x10008400202000600080010100200000000000040900c800080400 0 = false := by decide +kernel
lemma u6k12t1 : runCase ea6 edgeQ6 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec6 12 1) leaf198 (addMask leaf199 (addMask leaf200 (addMask leaf201 (addMask leaf202 (addMask leaf203 (addMask leaf204 (addMask leaf205 (addMask leaf206 (addMask leaf207 (addMask leaf208 (addMask leaf209 (addMask leaf210 (addMask leaf211 (addMask leaf212 endMasks))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf213 : ec6 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf214 : ec6 12 2 0xb12a2294a3c2110d08abc42395020084603512d8106110c58e4a2 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf215 : ec6 12 2 0x10e10942b5c2546a210141b006a1c3b009b808823259c422230211 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf216 : ec6 12 2 0x240c549400018a850e74020dc00e1c47b044a6504ca02ad184194c 0 = false := by decide +kernel
lemma u6k12t2 : runCase ea6 edgeQ6 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec6 12 2) leaf213 (addMask leaf214 (addMask leaf215 (addMask leaf216 endMasks)))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf217 : ec6 12 3 FF 1 = false := by decide +kernel
lemma u6k12t3 : runCase ea6 edgeQ6 12 3 := by
  exact one leaf217
lemma N6 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea6 (remT (unaryE ea6) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea6) (by decide +kernel) ready6 u6k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea6) (by decide +kernel) ready6 u6k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea6) (by decide +kernel) ready6 u6k12t3
set_option maxRecDepth 100000 in
theorem leaf218 : ec21 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf219 : ec21 12 1 0x80400080080002000000000000800020001800000000020000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf220 : ec21 12 1 0x20040000014000000000001010020200800000000000200000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf221 : ec21 12 1 0x10000001501014200404001008100401000000100c10020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf222 : ec21 12 1 0x1010058000000408800001008000008100800000050c0000001050 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf223 : ec21 12 1 0x400000100242800080000000260040020004ca20100008000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf224 : ec21 12 1 0x42010400040080202000040000044002400002400022080004100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf225 : ec21 12 1 0xa200000080100104004240000800010000001000008100a2002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf226 : ec21 12 1 0x8204082080000020000838100010000810000000c004000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf227 : ec21 12 1 0x80000000000000a0800000002000020000000600000100000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf228 : ec21 12 1 0x8100208500000000000000000000000010000000801002000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf229 : ec21 12 1 0x210000020000200008049092040008080000210042000000000008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf230 : ec21 12 1 0x106200100064002000008000004042000000000440208204 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf231 : ec21 12 1 0x10040001000000201100400040a0098010001040c80 0 = false := by decide +kernel
lemma u21k12t1 : runCase ea21 edgeQ21 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec21 12 1) leaf218 (addMask leaf219 (addMask leaf220 (addMask leaf221 (addMask leaf222 (addMask leaf223 (addMask leaf224 (addMask leaf225 (addMask leaf226 (addMask leaf227 (addMask leaf228 (addMask leaf229 (addMask leaf230 (addMask leaf231 endMasks)))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf232 : ec21 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf233 : ec21 12 2 0x24302f0006003e302455312c62e2300604aa622a0016a4c6df0304 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf234 : ec21 12 2 0x104510b2418940cac8a88800900dcc98a8549445b7e14828208c12 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf235 : ec21 12 2 0xb8ac04db8768105130246d30d10036153010990480813110070e9 0 = false := by decide +kernel
lemma u21k12t2 : runCase ea21 edgeQ21 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec21 12 2) leaf232 (addMask leaf233 (addMask leaf234 (addMask leaf235 endMasks)))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf236 : ec21 12 3 FF 1 = false := by decide +kernel
lemma u21k12t3 : runCase ea21 edgeQ21 12 3 := by
  exact one leaf236
lemma N21 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea21 (remT (unaryE ea21) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea21) (by decide +kernel) ready21 u21k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea21) (by decide +kernel) ready21 u21k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea21) (by decide +kernel) ready21 u21k12t3
set_option maxRecDepth 100000 in
theorem leaf237 : ec5 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf238 : ec5 12 1 0x1800000a820102020020800040400002000080000000011001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf239 : ec5 12 1 0x2000c0000000000000000000040010000000800100000000040080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf240 : ec5 12 1 0x104004080010000080000000000400000000040001000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf241 : ec5 12 1 0x400000080000004000000000001000000180000100002100000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf242 : ec5 12 1 0x2000000000000000000000000400000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf243 : ec5 12 1 0x1000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf244 : ec5 12 1 0x80000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf245 : ec5 12 1 0x200000000008000000004000000000000000000400000008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf246 : ec5 12 1 0x40000008100008010000204000000800080001000020100c02310 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf247 : ec5 12 1 0x20200400020001400201002004000400c10000074000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf248 : ec5 12 1 0x40000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf249 : ec5 12 1 0x100000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf250 : ec5 12 1 0x104000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf251 : ec5 12 1 0x8000000000101000000000100000000000000000400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf252 : ec5 12 1 0x800000000000000800000000200040000010000054001000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf253 : ec5 12 1 0x80002000040000c00000802400120001024008008000080220000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf254 : ec5 12 1 0x20000000005004000008141002800180000006004009000000002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf255 : ec5 12 1 0x3221505000000000090098008008000000000000000808000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf256 : ec5 12 1 0xc00000000000000000000008800000002282000000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf257 : ec5 12 1 0x20010200000000080004002040000000800000080000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf258 : ec5 12 1 0x1000080000020204000200000000002030802002000000000c460 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf259 : ec5 12 1 0x50000080001640000030000210010200240000200000800 0 = false := by decide +kernel
lemma u5k12t1 : runCase ea5 edgeQ5 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec5 12 1) leaf237 (addMask leaf238 (addMask leaf239 (addMask leaf240 (addMask leaf241 (addMask leaf242 (addMask leaf243 (addMask leaf244 (addMask leaf245 (addMask leaf246 (addMask leaf247 (addMask leaf248 (addMask leaf249 (addMask leaf250 (addMask leaf251 (addMask leaf252 (addMask leaf253 (addMask leaf254 (addMask leaf255 (addMask leaf256 (addMask leaf257 (addMask leaf258 (addMask leaf259 endMasks))))))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf260 : ec5 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf261 : ec5 12 2 0x890a30090019610cd62d01c4e0080b7e0e126002c792e64432841 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf262 : ec5 12 2 0x4508914f4c29a232912c61308c0c081b1499b95200808984d01a 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf263 : ec5 12 2 0x372a546e20b2404d000c038281737340040a4046818651123807a4 0 = false := by decide +kernel
lemma u5k12t2 : runCase ea5 edgeQ5 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec5 12 2) leaf260 (addMask leaf261 (addMask leaf262 (addMask leaf263 endMasks)))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf264 : ec5 12 3 FF 1 = false := by decide +kernel
lemma u5k12t3 : runCase ea5 edgeQ5 12 3 := by
  exact one leaf264
lemma N5 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea5 (remT (unaryE ea5) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea5) (by decide +kernel) ready5 u5k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea5) (by decide +kernel) ready5 u5k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea5) (by decide +kernel) ready5 u5k12t3
set_option maxRecDepth 100000 in
theorem leaf265 : ec28 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf266 : ec28 12 1 0x88008000000000100020201004000040000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf267 : ec28 12 1 0x2010510100000000004000000000000000000000020000000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf268 : ec28 12 1 0x2000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf269 : ec28 12 1 0x200000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf270 : ec28 12 1 0x400000100000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf271 : ec28 12 1 0x80000040000000000000000000000048000000040000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf272 : ec28 12 1 0x40000000020000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf273 : ec28 12 1 0x400000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf274 : ec28 12 1 0x4000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf275 : ec28 12 1 0x100000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf276 : ec28 12 1 0x800000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf277 : ec28 12 1 0x80004080000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf278 : ec28 12 1 0x800020000010000000000020210008000000000000200400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf279 : ec28 12 1 0x22000400000010400000010000001001800000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf280 : ec28 12 1 0x3000400240002000000080000000000000810000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf281 : ec28 12 1 0x80000012000000002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf282 : ec28 12 1 0x8200000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf283 : ec28 12 1 0x10000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf284 : ec28 12 1 0x100000000000000000000000000000000004000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf285 : ec28 12 1 0x800402000000400000820000080100000002000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf286 : ec28 12 1 0x40000000000020100100000002001000000000000004010040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf287 : ec28 12 1 0x1001080000080008000040800020000000800000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf288 : ec28 12 1 0x100000000000b08000000010100000004002000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf289 : ec28 12 1 0x6000000010000000840000000100000100000800000001000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf290 : ec28 12 1 0x20000000000000000020000200020000000102040400040000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf291 : ec28 12 1 0x1000000080000000840104008204000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf292 : ec28 12 1 0x1000000000004008000202000000000002000000000080208 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf293 : ec28 12 1 0x400200000000000000000001000000000000000081102000900 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf294 : ec28 12 1 0x800000000000000000880000080000414004000000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf295 : ec28 12 1 0x1000000000000208000004020000000000220000000001008000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf296 : ec28 12 1 0x40000080000000000400000800000000000000080404090 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf297 : ec28 12 1 0x4200000040000040000080010000000000010008000000000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf298 : ec28 12 1 0x10000000000002000000000000000402000400201008008000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf299 : ec28 12 1 0x41000400000000200000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf300 : ec28 12 1 0x200000000010000000000008008000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf301 : ec28 12 1 0x60800000008024000001000000000000000000000000020000000 0 = false := by decide +kernel
lemma u28k12t1 : runCase ea28 edgeQ28 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec28 12 1) leaf265 (addMask leaf266 (addMask leaf267 (addMask leaf268 (addMask leaf269 (addMask leaf270 (addMask leaf271 (addMask leaf272 (addMask leaf273 (addMask leaf274 (addMask leaf275 (addMask leaf276 (addMask leaf277 (addMask leaf278 (addMask leaf279 (addMask leaf280 (addMask leaf281 (addMask leaf282 (addMask leaf283 (addMask leaf284 (addMask leaf285 (addMask leaf286 (addMask leaf287 (addMask leaf288 (addMask leaf289 (addMask leaf290 (addMask leaf291 (addMask leaf292 (addMask leaf293 (addMask leaf294 (addMask leaf295 (addMask leaf296 (addMask leaf297 (addMask leaf298 (addMask leaf299 (addMask leaf300 (addMask leaf301 endMasks))))))))))))))))))))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf302 : ec28 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf303 : ec28 12 2 0x1811c1ea60101048a0403293812000210205221220004000100000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf304 : ec28 12 2 0x40224001024070016318000004054001000018d40b205b080a182 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf305 : ec28 12 2 0x2081a040081e8a5000c400430078002400a18408c400841080024 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf306 : ec28 12 2 0x1a0001101400010418201000a982918a15004200105800e005609 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf307 : ec28 12 2 0x204400008e0a000208000c68440002c40ca0c00012083200670850 0 = false := by decide +kernel
lemma u28k12t2 : runCase ea28 edgeQ28 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec28 12 2) leaf302 (addMask leaf303 (addMask leaf304 (addMask leaf305 (addMask leaf306 (addMask leaf307 endMasks)))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf308 : ec28 12 3 FF 1 = false := by decide +kernel
lemma u28k12t3 : runCase ea28 edgeQ28 12 3 := by
  exact one leaf308
lemma N28 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea28 (remT (unaryE ea28) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea28) (by decide +kernel) ready28 u28k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea28) (by decide +kernel) ready28 u28k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea28) (by decide +kernel) ready28 u28k12t3
set_option maxRecDepth 100000 in
theorem leaf309 : ec20 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf310 : ec20 12 1 0x800000004000000010000000000080000010000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf311 : ec20 12 1 0x200004200000008000000000000000000000000000000002000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf312 : ec20 12 1 0x80008000022000000000000000000000000000000008000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf313 : ec20 12 1 0x100000000000000100000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf314 : ec20 12 1 0x40000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf315 : ec20 12 1 0x10000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf316 : ec20 12 1 0x20000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf317 : ec20 12 1 0x10000000000000000000000000008000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf318 : ec20 12 1 0x4000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf319 : ec20 12 1 0x4000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf320 : ec20 12 1 0x800000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf321 : ec20 12 1 0x400000000080000000000002000010000000080000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf322 : ec20 12 1 0x44000000000000000000000200001000020000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf323 : ec20 12 1 0x8000000000000000300000000008004000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf324 : ec20 12 1 0x40000040400000000000000000000000004000010000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf325 : ec20 12 1 0x900000000000000000000000880000200000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf326 : ec20 12 1 0x20000000100000000000000000400020000000010000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf327 : ec20 12 1 0x200002000000100000000000000000000040080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf328 : ec20 12 1 0xc00000000000012000100000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf329 : ec20 12 1 0x410020000000000000000000020100000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf330 : ec20 12 1 0x10000000000000000000000000000000000000000008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf331 : ec20 12 1 0x2000008000000000004000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf332 : ec20 12 1 0x200000100080000040000800000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf333 : ec20 12 1 0x80008001000000080000000000200000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf334 : ec20 12 1 0x2002001000000000000000000000200000400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf335 : ec20 12 1 0x4000000000000000000000000000000080001000200020000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf336 : ec20 12 1 0x10000000002000000000001000800400000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf337 : ec20 12 1 0x80000000200800000000000008000000000000400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf338 : ec20 12 1 0x20200004000000080000000000000000040000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf339 : ec20 12 1 0x20000000000000000000000000000040000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf340 : ec20 12 1 0x200000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf341 : ec20 12 1 0x80000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf342 : ec20 12 1 0x1000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf343 : ec20 12 1 0x10000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf344 : ec20 12 1 0x1000000000000000000000000002000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf345 : ec20 12 1 0x200000100000000000400000000000000000000000004000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf346 : ec20 12 1 0x1020081000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf347 : ec20 12 1 0x8000000000000000000080000000008000000100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf348 : ec20 12 1 0x400000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf349 : ec20 12 1 0x400000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf350 : ec20 12 1 0xc00000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf351 : ec20 12 1 0x400000000008000000020000000000800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf352 : ec20 12 1 0x10000020000000000000000020000000000000200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf353 : ec20 12 1 0x14000000002000000000002000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf354 : ec20 12 1 0x800000000000000000000000000000000000000000000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf355 : ec20 12 1 0x4000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf356 : ec20 12 1 0x200000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf357 : ec20 12 1 0x80808000000000000000004000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf358 : ec20 12 1 0x1000000000000020000000000000080100000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf359 : ec20 12 1 0x401000000004000000000000000000000000000000000000002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf360 : ec20 12 1 0x40000000000000000000000040000002000000000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf361 : ec20 12 1 0x80100000000000000000000040000010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf362 : ec20 12 1 0x20000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf363 : ec20 12 1 0x1000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf364 : ec20 12 1 0x101000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf365 : ec20 12 1 0x8000000000000800100000000800000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf366 : ec20 12 1 0x40008000000000004400000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf367 : ec20 12 1 0x1000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf368 : ec20 12 1 0x100000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf369 : ec20 12 1 0x40000000000000000000000000040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf370 : ec20 12 1 0x2000400000000000000000000000040000000000004000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf371 : ec20 12 1 0x2000000000000000002001000000000000040000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf372 : ec20 12 1 0x52000000000000000000200000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf373 : ec20 12 1 0x1000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf374 : ec20 12 1 0x10000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf375 : ec20 12 1 0x100000000000000000000000000000200000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf376 : ec20 12 1 0x10000000000000400808000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf377 : ec20 12 1 0x801000000000000000000000100000800000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf378 : ec20 12 1 0x20000000000000000000000000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf379 : ec20 12 1 0x8000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf380 : ec20 12 1 0x40000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
lemma u20k12t1 : runCase ea20 edgeQ20 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec20 12 1) leaf309 (addMask leaf310 (addMask leaf311 (addMask leaf312 (addMask leaf313 (addMask leaf314 (addMask leaf315 (addMask leaf316 (addMask leaf317 (addMask leaf318 (addMask leaf319 (addMask leaf320 (addMask leaf321 (addMask leaf322 (addMask leaf323 (addMask leaf324 (addMask leaf325 (addMask leaf326 (addMask leaf327 (addMask leaf328 (addMask leaf329 (addMask leaf330 (addMask leaf331 (addMask leaf332 (addMask leaf333 (addMask leaf334 (addMask leaf335 (addMask leaf336 (addMask leaf337 (addMask leaf338 (addMask leaf339 (addMask leaf340 (addMask leaf341 (addMask leaf342 (addMask leaf343 (addMask leaf344 (addMask leaf345 (addMask leaf346 (addMask leaf347 (addMask leaf348 (addMask leaf349 (addMask leaf350 (addMask leaf351 (addMask leaf352 (addMask leaf353 (addMask leaf354 (addMask leaf355 (addMask leaf356 (addMask leaf357 (addMask leaf358 (addMask leaf359 (addMask leaf360 (addMask leaf361 (addMask leaf362 (addMask leaf363 (addMask leaf364 (addMask leaf365 (addMask leaf366 (addMask leaf367 (addMask leaf368 (addMask leaf369 (addMask leaf370 (addMask leaf371 (addMask leaf372 (addMask leaf373 (addMask leaf374 (addMask leaf375 (addMask leaf376 (addMask leaf377 (addMask leaf378 (addMask leaf379 (addMask leaf380 endMasks)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf381 : ec20 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf382 : ec20 12 2 0x310044908881000120008000000290200200000000000004400040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf383 : ec20 12 2 0x80000002050000081008240040802000108021042900100080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf384 : ec20 12 2 0x208260200004048004180081000081040210880000010000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf385 : ec20 12 2 0x2090000000080800a40800822510020400200920000000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf386 : ec20 12 2 0x30000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf387 : ec20 12 2 0x10000000000000400000000000000000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf388 : ec20 12 2 0x4100000000000000000000020000000040000000000400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf389 : ec20 12 2 0x6000000000200000400002002000000001080000080008000200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf390 : ec20 12 2 0x40100000048080004200000104008000814040004401000845000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf391 : ec20 12 2 0x800040000052080000000000840004008800400200408128001a 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf392 : ec20 12 2 0x80000000020003600002005400004000000823508008200000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf393 : ec20 12 2 0x2040100141400801014003000000100410000000000006000a800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf394 : ec20 12 2 0x1800002000800003020400030100008002000010210402030100 0 = false := by decide +kernel
lemma u20k12t2 : runCase ea20 edgeQ20 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec20 12 2) leaf381 (addMask leaf382 (addMask leaf383 (addMask leaf384 (addMask leaf385 (addMask leaf386 (addMask leaf387 (addMask leaf388 (addMask leaf389 (addMask leaf390 (addMask leaf391 (addMask leaf392 (addMask leaf393 (addMask leaf394 endMasks)))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf395 : ec20 12 3 FF 1 = false := by decide +kernel
lemma u20k12t3 : runCase ea20 edgeQ20 12 3 := by
  exact one leaf395
lemma N20 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea20 (remT (unaryE ea20) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea20) (by decide +kernel) ready20 u20k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea20) (by decide +kernel) ready20 u20k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea20) (by decide +kernel) ready20 u20k12t3
def I9 : List ℕ := [ip 0 0, ip 1 0, ip 3 0, ip 5 0]
def P9 : List (ℕ × ℕ) := [(0, 1), (0, 3), (0, 5), (1, 3), (1, 5), (3, 5), (6, 1), (6, 3), (6, 5), (7, 3), (7, 5), (9, 5)]
lemma earlier9 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P9, Excluded 12 p t := by
  intro p hp
  simp only [P9, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
theorem leaf396 : ec9 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf397 : ec9 12 1 0x5000004000400040000400104200200000200000200000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf398 : ec9 12 1 0x4004020000000000004000100000040010080010000200000802 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf399 : ec9 12 1 0x4000000004000002020004000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf400 : ec9 12 1 0x10000000000000002000000000000000000000000000040000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf401 : ec9 12 1 0x10000000000002000000008000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf402 : ec9 12 1 0x2008200000000004000000004112000000004000000000000100c0 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf403 : ec9 12 1 0x800000000021000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf404 : ec9 12 1 0x200000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf405 : ec9 12 1 0x80000010000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf406 : ec9 12 1 0x2000000000000000800000020000000000000010020000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf407 : ec9 12 1 0x1100100000040081000000000001001108100100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf408 : ec9 12 1 0x220000000800020000000000a004000400100040004000008000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf409 : ec9 12 1 0x40040008801000800000080020000000000040080080040000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf410 : ec9 12 1 0x8000180000008200004000000022000000000040400400010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf411 : ec9 12 1 0x20000080000048000000628000040000000800000002080000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf412 : ec9 12 1 0x100044002420200000000000000020000a000008000000004000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf413 : ec9 12 1 0x510000011000000000000100020004000002080028 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf414 : ec9 12 1 0x10001000002080002000000000000408000010200000001021000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf415 : ec9 12 1 0x8000200210020000000100000000080800006000000000000600 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf416 : ec9 12 1 0x400000000828000000900000020001820008010000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf417 : ec9 12 1 0x1000100008000000c0001000000801040000500400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf418 : ec9 12 1 0x480000040000000000002800018010080000000100000002000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf419 : ec9 12 1 0x100000000040000000080000000001000000000000800000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf420 : ec9 12 1 0x80000002000000000000000000000000000000000000800000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf421 : ec9 12 1 0x100000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf422 : ec9 12 1 0x4000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf423 : ec9 12 1 0x800000000000 0 = false := by decide +kernel
lemma u9k12t1 : runCase ea9 edgeQ9 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec9 12 1) leaf396 (addMask leaf397 (addMask leaf398 (addMask leaf399 (addMask leaf400 (addMask leaf401 (addMask leaf402 (addMask leaf403 (addMask leaf404 (addMask leaf405 (addMask leaf406 (addMask leaf407 (addMask leaf408 (addMask leaf409 (addMask leaf410 (addMask leaf411 (addMask leaf412 (addMask leaf413 (addMask leaf414 (addMask leaf415 (addMask leaf416 (addMask leaf417 (addMask leaf418 (addMask leaf419 (addMask leaf420 (addMask leaf421 (addMask leaf422 (addMask leaf423 endMasks)))))))))))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf424 : ec9 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf425 : ec9 12 2 0x2900040054131220302114905209908e91020a895198002a08821 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf426 : ec9 12 2 0x2008411010000288ec30acb0ca106064002cd84422402490487000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf427 : ec9 12 2 0x19479e0d080cc044008942022046041206c10302088010400501c4 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf428 : ec9 12 2 0x42020a2e2b20c1110440004108902811002041140264b2d12061a 0 = false := by decide +kernel
lemma u9k12t2 : runCase ea9 edgeQ9 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec9 12 2) leaf424 (addMask leaf425 (addMask leaf426 (addMask leaf427 (addMask leaf428 endMasks))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem marked9t3 : markedChk (cliqueMark I9) [ea9] edgeQ9 0 12 3 0 1 = false := by decide +kernel
lemma N9 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea9 (remT (unaryE ea9) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea9) (by decide +kernel) ready9 u9k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea9) (by decide +kernel) ready9 u9k12t2
  · exact binaryMarked (firstOp:=true) (x:=2) (y:=3) (inputs:=I9) (prior:=P9) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready9.1 base ready9.2.1 ready9.2.2 (by decide +kernel) (by decide +kernel) (earlier9 base 3 (by decide) (by decide)) marked9t3
set_option maxRecDepth 100000 in
theorem leaf429 : ec24 12 1 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf430 : ec24 12 1 0x8000100000000400000018000080020000010040044000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf431 : ec24 12 1 0x10000000020000010000a0006000080000800020010000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf432 : ec24 12 1 0x100000000020000400500002c04000400000000020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf433 : ec24 12 1 0x100000204000300100040001000000000010400000000400000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf434 : ec24 12 1 0x2000000091000000000000000040000900000004000000001080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf435 : ec24 12 1 0x200040000020000008000000010004010000080004000000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf436 : ec24 12 1 0x1000040000810000000000000000020000108000006008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf437 : ec24 12 1 0x22080800210000204000000100000000000200000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf438 : ec24 12 1 0x100000000000800000002008000000218000040000000002000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf439 : ec24 12 1 0x20000000018020000000008000400002101000000000100 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf440 : ec24 12 1 0x400000000000000000000800000000000000000820400 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf441 : ec24 12 1 0x20001000000000400000000000000000080100000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf442 : ec24 12 1 0x80000000000040000601000080000000000040000021000800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf443 : ec24 12 1 0x40400500040080000000100004000000000000000001000010000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf444 : ec24 12 1 0x1000010000000400000800000000020044000000000200300000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf445 : ec24 12 1 0x2000000000000000002800000000180000a12000080000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf446 : ec24 12 1 0x14000004000000804000080000020000008000020000080000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf447 : ec24 12 1 0x8004021000010200000000001009000000000000002 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf448 : ec24 12 1 0x20050a00000008000000000000000002200000000000000008200 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf449 : ec24 12 1 0x80000080004000000c0000900000000000000008000800000040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf450 : ec24 12 1 0x800000002000082000000040000040000200000000008040010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf451 : ec24 12 1 0x280004000000000000000006000201001000000002000400000000 0 = false := by decide +kernel
lemma u24k12t1 : runCase ea24 edgeQ24 12 1 := by
  refine ⟨_, ?_, addMask (f:=ec24 12 1) leaf429 (addMask leaf430 (addMask leaf431 (addMask leaf432 (addMask leaf433 (addMask leaf434 (addMask leaf435 (addMask leaf436 (addMask leaf437 (addMask leaf438 (addMask leaf439 (addMask leaf440 (addMask leaf441 (addMask leaf442 (addMask leaf443 (addMask leaf444 (addMask leaf445 (addMask leaf446 (addMask leaf447 (addMask leaf448 (addMask leaf449 (addMask leaf450 (addMask leaf451 endMasks))))))))))))))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf452 : ec24 12 2 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf453 : ec24 12 2 0x40000040e042000089200803201040110200954c00c0140800219 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf454 : ec24 12 2 0x284d10000040511282000020000200a8a400402020220400311184 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf455 : ec24 12 2 0x200004880010004012880004190a0100811908816c04a88024000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf456 : ec24 12 2 0xe8202038822844005e18844011000000000300001003080422 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf457 : ec24 12 2 0x100780108008410045004600040006024826000911a024002800 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf458 : ec24 12 2 0x11a20013410204803000210108284a404186000000000010448040 0 = false := by decide +kernel
lemma u24k12t2 : runCase ea24 edgeQ24 12 2 := by
  refine ⟨_, ?_, addMask (f:=ec24 12 2) leaf452 (addMask leaf453 (addMask leaf454 (addMask leaf455 (addMask leaf456 (addMask leaf457 (addMask leaf458 endMasks))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf459 : ec24 12 3 FF 1 = false := by decide +kernel
lemma u24k12t3 : runCase ea24 edgeQ24 12 3 := by
  exact one leaf459
lemma N24 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea24 (remT (unaryE ea24) t) := by
  interval_cases t
  · exact afterEdge (k:=12) (t:=1) (by decide) base (e:=ea24) (by decide +kernel) ready24 u24k12t1
  · exact afterEdge (k:=12) (t:=2) (by decide) base (e:=ea24) (by decide +kernel) ready24 u24k12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea24) (by decide +kernel) ready24 u24k12t3
def I29 : List ℕ := [ip 0 0, ip 1 0, ip 2 0, ip 3 0, ip 5 0]
def P29 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5), (6, 1), (6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (7, 5), (8, 3), (8, 5), (9, 5)]
lemma earlier29 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P29, Excluded 12 p t := by
  intro p hp
  simp only [P29, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc0 := deepEval (lz 0) (mz 0) (pL (edgeQ29.map fun _ => 16)) 12
noncomputable def dc1 := tRoot (cliqueMark I29) [ea29] edgeQ29 0 12 1 0 1
noncomputable def dc2 := dSel dc1 [14,15,9,46]
noncomputable def dc3 := dSel dc1 [8,12,13,1,32]
noncomputable def dc4 := dSel dc1 [10,3,6,4,52]
noncomputable def dc5 := dSel dc1 [11,40,5,7,34,18,36,43,33,39,24,27,51,35,41,47,37,53,42,48]
noncomputable def dc6 := dc2 ++ dc3 ++ dc4 ++ dc5
set_option maxRecDepth 100000 in
theorem dc7 : dGood dc0 dc2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc8 : dGood dc0 dc3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc9 : dGood dc0 dc4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc10 : dGood dc0 dc5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc11 : markedBudgetWith (cliqueMark I29) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ29.map fun _ => 16)) 12 dc6 mode 12) [ea29] edgeQ29 0 12 1 0 1 = false := by decide +kernel
lemma dc12 : ∀ x ∈ dc6, dc0 x = false := dFord (dCat (dCat (dCat dc7 dc8) dc9) dc10)
theorem marked29t1 : markedChk (cliqueMark I29) [ea29] edgeQ29 0 12 1 0 1 = false := markedDeepRootJoin (cliqueMark I29) _ _ _ _ _ _ _ dc6 dc12 dc11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc13 := deepEval (lz 0) (mz 0) (pL (edgeQ29.map fun _ => 16)) 12
noncomputable def dc14 := tRoot (cliqueMark I29) [ea29] edgeQ29 0 12 2 0 1
noncomputable def dc15 := dSel dc14 [15,14,12,13,74,8,10,58,1,4,6,32,90,106,52,68,3,21,84,7,9,11,62,110,95,96]
noncomputable def dc16 := dSel dc14 [113,34,37,26,28,43,50,72,82]
noncomputable def dc17 := dc15 ++ dc16
set_option maxRecDepth 100000 in
theorem dc18 : dGood dc13 dc15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc19 : dGood dc13 dc16 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc20 : markedBudgetWith (cliqueMark I29) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ29.map fun _ => 16)) 12 dc17 mode 12) [ea29] edgeQ29 0 12 2 0 1 = false := by decide +kernel
lemma dc21 : ∀ x ∈ dc17, dc13 x = false := dFord (dCat dc18 dc19)
theorem marked29t2 : markedChk (cliqueMark I29) [ea29] edgeQ29 0 12 2 0 1 = false := markedDeepRootJoin (cliqueMark I29) _ _ _ _ _ _ _ dc17 dc21 dc20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem marked29t3 : markedChk (cliqueMark I29) [ea29] edgeQ29 0 12 3 0 1 = false := by decide +kernel
lemma N29 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea29 (remT (unaryE ea29) t) := by
  interval_cases t
  · exact binaryMarked (firstOp:=false) (x:=4) (y:=5) (inputs:=I29) (prior:=P29) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready29.1 base ready29.2.1 ready29.2.2 (by decide +kernel) (by decide +kernel) (earlier29 base 1 (by decide) (by decide)) marked29t1
  · exact binaryMarked (firstOp:=false) (x:=4) (y:=5) (inputs:=I29) (prior:=P29) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready29.1 base ready29.2.1 ready29.2.2 (by decide +kernel) (by decide +kernel) (earlier29 base 2 (by decide) (by decide)) marked29t2
  · exact binaryMarked (firstOp:=false) (x:=4) (y:=5) (inputs:=I29) (prior:=P29) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready29.1 base ready29.2.1 ready29.2.2 (by decide +kernel) (by decide +kernel) (earlier29 base 3 (by decide) (by decide)) marked29t3
def I12 : List ℕ := [ip 0 0, ip 1 0, ip 2 0, ip 3 0, ip 5 0]
def P12 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5), (6, 1), (6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (7, 5), (8, 3), (8, 5), (9, 5)]
lemma earlier12 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P12, Excluded 12 p t := by
  intro p hp
  simp only [P12, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc22 := deepEval (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12
noncomputable def dc23 := tRoot (cliqueMark I12) [ea12] edgeQ12 0 12 1 0 1
noncomputable def dc24 := dc23.getD 2 default
noncomputable def dc25 := tLeaves (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc24
noncomputable def dc26 := dSel dc25 [12,16,20,26,6,7,24,0,18,22,55,45,57,61,5,13,2,14,34,29,30,32,41,71,51,40]
noncomputable def dc27 := dc26
noncomputable def dc28 := dc23.getD 4 default
noncomputable def dc29 := tLeaves (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc28
noncomputable def dc30 := dSel dc29 [7,8,10,28,18,14,12,20,22,29,26,5,3,2,0,24,19,11,6,46]
noncomputable def dc31 := dSel dc29 [25,89,92,49,51,60,94,65,71,97,106,4,9,16,54,76,47,40,57,41,42,91,44,53,75]
noncomputable def dc32 := dc30 ++ dc31
noncomputable def dc33 := dc23.getD 3 default
noncomputable def dc34 := tLeaves (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc33
noncomputable def dc35 := dSel dc34 [5,8,16,6,4,14,11,13,3]
noncomputable def dc36 := dSel dc34 [1,15,12,0,10,9,27,50,29,52,55,7]
noncomputable def dc37 := dc35 ++ dc36
noncomputable def dc38 := dSel dc23 [10,8]
noncomputable def dc39 := dSel dc23 [1,14]
noncomputable def dc40 := dSel dc23 [13,6]
noncomputable def dc41 := dSel dc23 [11,15,23]
noncomputable def dc42 := dSel dc23 [16,0,12,29,31,32]
noncomputable def dc43 := dSel dc23 [45,5,34,59,26,38,27,28,33,40,42,48,47,56,41,30,54,44]
noncomputable def dc44 := dSel dc23 [58,18,19,17,52]
noncomputable def dc45 := dc38 ++ dc39 ++ dc40 ++ dc41 ++ dc42 ++ dc43 ++ dc44 ++ [dc33] ++ [dc28] ++ [dc24]
set_option maxRecDepth 100000 in
theorem dc46 : dGood dc22 dc26 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc47 : deepOuter (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc27 dc24 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc48 : dGood dc22 dc30 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc49 : dGood dc22 dc31 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc50 : deepOuter (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc32 dc28 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc51 : dGood dc22 dc35 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc52 : dGood dc22 dc36 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc53 : deepOuter (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc37 dc33 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc54 : dGood dc22 dc38 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc55 : dGood dc22 dc39 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc56 : dGood dc22 dc40 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc57 : dGood dc22 dc41 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc58 : dGood dc22 dc42 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc59 : dGood dc22 dc43 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc60 : dGood dc22 dc44 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc61 : markedBudgetWith (cliqueMark I12) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc45 mode 12) [ea12] edgeQ12 0 12 1 0 1 = false := by decide +kernel
lemma dc62 : ∀ x ∈ dc27, dc22 x = false := dFord dc46
lemma dc63 : dc22 dc24 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc27 dc24 dc62 dc47
lemma dc64 : ∀ x ∈ dc32, dc22 x = false := dFord (dCat dc48 dc49)
lemma dc65 : dc22 dc28 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc32 dc28 dc64 dc50
lemma dc66 : ∀ x ∈ dc37, dc22 x = false := dFord (dCat dc51 dc52)
lemma dc67 : dc22 dc33 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc37 dc33 dc66 dc53
lemma dc68 : ∀ x ∈ dc45, dc22 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc54 dc55) dc56) dc57) dc58) dc59) dc60) (dOne dc67)) (dOne dc65)) (dOne dc63))
theorem marked12t1 : markedChk (cliqueMark I12) [ea12] edgeQ12 0 12 1 0 1 = false := markedDeepRootJoin (cliqueMark I12) _ _ _ _ _ _ _ dc45 dc68 dc61
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc69 := deepEval (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12
noncomputable def dc70 := tRoot (cliqueMark I12) [ea12] edgeQ12 0 12 2 0 1
noncomputable def dc71 := dSel dc70 [3,2,13,53,86]
noncomputable def dc72 := dSel dc70 [4,1,8,14,15,6]
noncomputable def dc73 := dSel dc70 [12,0,16,10,11,49,63,55,69,96,9,88,23,73,77,66,40,51,81,56,52,75,84,71,117,108,5,119,57,87,123,124]
noncomputable def dc74 := dSel dc70 [18,27,22,25,20,26,39,17,106,95,41,54]
noncomputable def dc75 := dc71 ++ dc72 ++ dc73 ++ dc74
set_option maxRecDepth 100000 in
theorem dc76 : dGood dc69 dc71 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc77 : dGood dc69 dc72 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc78 : dGood dc69 dc73 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc79 : dGood dc69 dc74 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc80 : markedBudgetWith (cliqueMark I12) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ12.map fun _ => 16)) 12 dc75 mode 12) [ea12] edgeQ12 0 12 2 0 1 = false := by decide +kernel
lemma dc81 : ∀ x ∈ dc75, dc69 x = false := dFord (dCat (dCat (dCat dc76 dc77) dc78) dc79)
theorem marked12t2 : markedChk (cliqueMark I12) [ea12] edgeQ12 0 12 2 0 1 = false := markedDeepRootJoin (cliqueMark I12) _ _ _ _ _ _ _ dc75 dc81 dc80
set_option maxRecDepth 100000 in
theorem leaf460 : ec12 12 3 FF 1 = false := by decide +kernel
lemma u12k12t3 : runCase ea12 edgeQ12 12 3 := by
  exact one leaf460
lemma N12 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea12 (remT (unaryE ea12) t) := by
  interval_cases t
  · exact binaryMarked (firstOp:=true) (x:=3) (y:=4) (inputs:=I12) (prior:=P12) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready12.1 base ready12.2.1 ready12.2.2 (by decide +kernel) (by decide +kernel) (earlier12 base 1 (by decide) (by decide)) marked12t1
  · exact binaryMarked (firstOp:=true) (x:=3) (y:=4) (inputs:=I12) (prior:=P12) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready12.1 base ready12.2.1 ready12.2.2 (by decide +kernel) (by decide +kernel) (earlier12 base 2 (by decide) (by decide)) marked12t2
  · exact afterEdge (k:=12) (t:=3) (by decide) base (e:=ea12) (by decide +kernel) ready12 u12k12t3
def I3 : List ℕ := [ip 0 0, ip 1 0, ip 2 0, ip 3 0, ip 5 0]
def P3 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5), (6, 1), (6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (7, 5), (8, 3), (8, 5), (9, 5)]
lemma earlier3 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P3, Excluded 12 p t := by
  intro p hp
  simp only [P3, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc82 := deepEval (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12
noncomputable def dc83 := tRoot (cliqueMark I3) [ea3] edgeQ3 0 12 1 0 1
noncomputable def dc84 := dc83.getD 11 default
noncomputable def dc85 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc84
noncomputable def dc86 := dSel dc85 [1,2,3,16,26,24,28]
noncomputable def dc87 := dc86
noncomputable def dc88 := dc83.getD 16 default
noncomputable def dc89 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc88
noncomputable def dc90 := dSel dc89 [1,2,19,3,4,29,27,33,31,23,14,25]
noncomputable def dc91 := dc90
noncomputable def dc92 := dc83.getD 2 default
noncomputable def dc93 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc92
noncomputable def dc94 := dSel dc93 [14,11,9,21,26,25,27,8,6,22,19,17,12,23,5,87]
noncomputable def dc95 := dSel dc93 [10,3,0,13,2,15,71,91,73,52,78,98,86,89,76,107,82,106,56,109,102,59,62,16,7,20,28,32,30,92,44,51]
noncomputable def dc96 := dSel dc93 [38,74,41,94,42,40,39]
noncomputable def dc97 := dc94 ++ dc95 ++ dc96
noncomputable def dc98 := dc83.getD 3 default
noncomputable def dc99 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc98
noncomputable def dc100 := dSel dc99 [11,13,24,16,6,18,22,7,0,26,51,46,44,61,5,14,20,29,30,41,70,50,36,40]
noncomputable def dc101 := dc100
noncomputable def dc102 := dc83.getD 4 default
noncomputable def dc103 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc102
noncomputable def dc104 := dSel dc103 [24,18,13,22,16,6,8,0,26,2,20,45,75,63,78,82,5,9,25,23,35,41,48,71]
noncomputable def dc105 := dc104
noncomputable def dc106 := dc83.getD 1 default
noncomputable def dc107 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc106
noncomputable def dc108 := dSel dc107 [15,9,13,6,8,0]
noncomputable def dc109 := dSel dc107 [4,12,16,14,3,1,10,11,5,7,30,51,33]
noncomputable def dc110 := dSel dc107 [23,64,48,36,39,42,55,24,25,44]
noncomputable def dc111 := dc108 ++ dc109 ++ dc110
noncomputable def dc112 := dSel dc83 [9,12,29]
noncomputable def dc113 := dSel dc83 [7,6,44]
noncomputable def dc114 := dSel dc83 [14,10,0,23]
noncomputable def dc115 := dSel dc83 [8,46,34,5,26,58,41,37,54]
noncomputable def dc116 := dSel dc83 [31,32,43,60,48,27,55,36,25,33,40,38,52,57]
noncomputable def dc117 := dSel dc83 [47,15]
noncomputable def dc118 := dc112 ++ dc113 ++ dc114 ++ dc115 ++ dc116 ++ dc117 ++ [dc106] ++ [dc92] ++ [dc88] ++ [dc102] ++ [dc84] ++ [dc98]
set_option maxRecDepth 100000 in
theorem dc119 : dGood dc82 dc86 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc120 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc87 dc84 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc121 : dGood dc82 dc90 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc122 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc91 dc88 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc123 : dGood dc82 dc94 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc124 : dGood dc82 dc95 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc125 : dGood dc82 dc96 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc126 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc97 dc92 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc127 : dGood dc82 dc100 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc128 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc101 dc98 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc129 : dGood dc82 dc104 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc130 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc105 dc102 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc131 : dGood dc82 dc108 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc132 : dGood dc82 dc109 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc133 : dGood dc82 dc110 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc134 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc111 dc106 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc135 : dGood dc82 dc112 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc136 : dGood dc82 dc113 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc137 : dGood dc82 dc114 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc138 : dGood dc82 dc115 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc139 : dGood dc82 dc116 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc140 : dGood dc82 dc117 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc141 : markedBudgetWith (cliqueMark I3) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc118 mode 12) [ea3] edgeQ3 0 12 1 0 1 = false := by decide +kernel
lemma dc142 : ∀ x ∈ dc87, dc82 x = false := dFord dc119
lemma dc143 : dc82 dc84 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc87 dc84 dc142 dc120
lemma dc144 : ∀ x ∈ dc91, dc82 x = false := dFord dc121
lemma dc145 : dc82 dc88 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc91 dc88 dc144 dc122
lemma dc146 : ∀ x ∈ dc97, dc82 x = false := dFord (dCat (dCat dc123 dc124) dc125)
lemma dc147 : dc82 dc92 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc97 dc92 dc146 dc126
lemma dc148 : ∀ x ∈ dc101, dc82 x = false := dFord dc127
lemma dc149 : dc82 dc98 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc101 dc98 dc148 dc128
lemma dc150 : ∀ x ∈ dc105, dc82 x = false := dFord dc129
lemma dc151 : dc82 dc102 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc105 dc102 dc150 dc130
lemma dc152 : ∀ x ∈ dc111, dc82 x = false := dFord (dCat (dCat dc131 dc132) dc133)
lemma dc153 : dc82 dc106 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc111 dc106 dc152 dc134
lemma dc154 : ∀ x ∈ dc118, dc82 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc135 dc136) dc137) dc138) dc139) dc140) (dOne dc153)) (dOne dc147)) (dOne dc145)) (dOne dc151)) (dOne dc143)) (dOne dc149))
theorem marked3t1 : markedChk (cliqueMark I3) [ea3] edgeQ3 0 12 1 0 1 = false := markedDeepRootJoin (cliqueMark I3) _ _ _ _ _ _ _ dc118 dc154 dc141
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc155 := deepEval (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12
noncomputable def dc156 := tRoot (cliqueMark I3) [ea3] edgeQ3 0 12 2 0 1
noncomputable def dc157 := dc156.getD 1 default
noncomputable def dc158 := tLeaves (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc157
noncomputable def dc159 := dSel dc158 [8,15,13,6,9,14,4,83,117,3,5,7,1,10,0,12,16,99,132,67,100,138,102,139,104,78,111,90,80,37,123,47]
noncomputable def dc160 := dSel dc158 [58]
noncomputable def dc161 := dc159 ++ dc160
noncomputable def dc162 := dSel dc156 [2,3,9]
noncomputable def dc163 := dSel dc156 [4,14,11,16,15,10,63]
noncomputable def dc164 := dSel dc156 [12,0,70,102,6,8,69,101,7,95,66,42,65,67,99,71,75,83,115,123,73,105,34,41,77,35,98,40,62,94,80,68]
noncomputable def dc165 := dSel dc156 [112,100,50,64,103,107,5,86,58,88,87,119,120,21,27]
noncomputable def dc166 := dc162 ++ dc163 ++ dc164 ++ dc165 ++ [dc157]
set_option maxRecDepth 100000 in
theorem dc167 : dGood dc155 dc159 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc168 : dGood dc155 dc160 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc169 : deepOuter (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc161 dc157 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc170 : dGood dc155 dc162 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc171 : dGood dc155 dc163 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc172 : dGood dc155 dc164 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc173 : dGood dc155 dc165 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc174 : markedBudgetWith (cliqueMark I3) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc166 mode 12) [ea3] edgeQ3 0 12 2 0 1 = false := by decide +kernel
lemma dc175 : ∀ x ∈ dc161, dc155 x = false := dFord (dCat dc167 dc168)
lemma dc176 : dc155 dc157 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ3.map fun _ => 16)) 12 dc161 dc157 dc175 dc169
lemma dc177 : ∀ x ∈ dc166, dc155 x = false := dFord (dCat (dCat (dCat (dCat dc170 dc171) dc172) dc173) (dOne dc176))
theorem marked3t2 : markedChk (cliqueMark I3) [ea3] edgeQ3 0 12 2 0 1 = false := markedDeepRootJoin (cliqueMark I3) _ _ _ _ _ _ _ dc166 dc177 dc174
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem marked3t3 : markedChk (cliqueMark I3) [ea3] edgeQ3 0 12 3 0 1 = false := by decide +kernel
lemma N3 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea3 (remT (unaryE ea3) t) := by
  interval_cases t
  · exact binaryMarked (firstOp:=true) (x:=0) (y:=4) (inputs:=I3) (prior:=P3) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready3.1 base ready3.2.1 ready3.2.2 (by decide +kernel) (by decide +kernel) (earlier3 base 1 (by decide) (by decide)) marked3t1
  · exact binaryMarked (firstOp:=true) (x:=0) (y:=4) (inputs:=I3) (prior:=P3) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready3.1 base ready3.2.1 ready3.2.2 (by decide +kernel) (by decide +kernel) (earlier3 base 2 (by decide) (by decide)) marked3t2
  · exact binaryMarked (firstOp:=true) (x:=0) (y:=4) (inputs:=I3) (prior:=P3) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready3.1 base ready3.2.1 ready3.2.2 (by decide +kernel) (by decide +kernel) (earlier3 base 3 (by decide) (by decide)) marked3t3
def I22 : List ℕ := [ip 0 0, ip 1 0, ip 2 0, ip 3 0, ip 5 0]
def P22 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5), (6, 1), (6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (7, 5), (8, 3), (8, 5), (9, 5)]
lemma earlier22 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P22, Excluded 12 p t := by
  intro p hp
  simp only [P22, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc178 := deepEval (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12
noncomputable def dc179 := tRoot (cliqueMark I22) [ea22] edgeQ22 0 12 1 0 1
noncomputable def dc180 := dc179.getD 13 default
noncomputable def dc181 := tLeaves (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc180
noncomputable def dc182 := dSel dc181 [3,6,12,9,0,14,19,23,58,16,17,21,56,75,57,18,22,24,4,7,2,11,5,8,15,34,31,25,55,35]
noncomputable def dc183 := dc182
noncomputable def dc184 := dc179.getD 12 default
noncomputable def dc185 := tLeaves (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc184
noncomputable def dc186 := dSel dc185 [2,4,8,16,10,12,6,17,11,14]
noncomputable def dc187 := dSel dc185 [15,1,9,0,13,54,50,56,3,63,41,66,59,69,55,72,75,7,5]
noncomputable def dc188 := dc186 ++ dc187
noncomputable def dc189 := dc179.getD 10 default
noncomputable def dc190 := tLeaves (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc189
noncomputable def dc191 := dSel dc190 [0,19,27,21,22,33,35,23,20,13,17,31,37,39,29,28,5,8,41,1]
noncomputable def dc192 := dc191
noncomputable def dc193 := dc179.getD 14 default
noncomputable def dc194 := tLeaves (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc193
noncomputable def dc195 := dSel dc194 [22,0,11,16,19,18,10,4,2,12,13,7,5,9,21,23,52,47,71,51,56,79,30]
noncomputable def dc196 := dSel dc194 [15,8,24]
noncomputable def dc197 := dc195 ++ dc196
noncomputable def dc198 := dc179.getD 15 default
noncomputable def dc199 := tLeaves (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc198
noncomputable def dc200 := dSel dc199 [12,0,13,14,8,11,7,2,9,10,4]
noncomputable def dc201 := dc200
noncomputable def dc202 := dc179.getD 16 default
noncomputable def dc203 := tLeaves (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc202
noncomputable def dc204 := dSel dc203 [16,0,19,15,5,10,7,22,11,4,6,2,65,8,13,9,21,24,52,3,51]
noncomputable def dc205 := dSel dc203 [1,18,17,46,63,33,62,55,61,59,75]
noncomputable def dc206 := dc204 ++ dc205
noncomputable def dc207 := dSel dc179 [2,0]
noncomputable def dc208 := dSel dc179 [4,5]
noncomputable def dc209 := dSel dc179 [9,85,52]
noncomputable def dc210 := dSel dc179 [11,62,59,71]
noncomputable def dc211 := dSel dc179 [1,41,57,7,83]
noncomputable def dc212 := dSel dc179 [3,63,55,77,74]
noncomputable def dc213 := dSel dc179 [68,26,35,80,44,58,47,50,66,61,38,43,76,21]
noncomputable def dc214 := dSel dc179 [70,73,46,49,54,79,69,82,17,18,23,22,29,67,20,28,32,64,65,33]
noncomputable def dc215 := dc207 ++ dc208 ++ dc209 ++ dc210 ++ dc211 ++ dc212 ++ dc213 ++ dc214 ++ [dc184] ++ [dc180] ++ [dc202] ++ [dc193] ++ [dc189] ++ [dc198]
set_option maxRecDepth 100000 in
theorem dc216 : dGood dc178 dc182 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc217 : deepOuter (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc183 dc180 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc218 : dGood dc178 dc186 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc219 : dGood dc178 dc187 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc220 : deepOuter (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc188 dc184 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc221 : dGood dc178 dc191 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc222 : deepOuter (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc192 dc189 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc223 : dGood dc178 dc195 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc224 : dGood dc178 dc196 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc225 : deepOuter (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc197 dc193 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc226 : dGood dc178 dc200 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc227 : deepOuter (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc201 dc198 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc228 : dGood dc178 dc204 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc229 : dGood dc178 dc205 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc230 : deepOuter (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc206 dc202 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc231 : dGood dc178 dc207 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc232 : dGood dc178 dc208 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc233 : dGood dc178 dc209 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc234 : dGood dc178 dc210 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc235 : dGood dc178 dc211 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc236 : dGood dc178 dc212 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc237 : dGood dc178 dc213 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc238 : dGood dc178 dc214 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc239 : markedBudgetWith (cliqueMark I22) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc215 mode 12) [ea22] edgeQ22 0 12 1 0 1 = false := by decide +kernel
lemma dc240 : ∀ x ∈ dc183, dc178 x = false := dFord dc216
lemma dc241 : dc178 dc180 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc183 dc180 dc240 dc217
lemma dc242 : ∀ x ∈ dc188, dc178 x = false := dFord (dCat dc218 dc219)
lemma dc243 : dc178 dc184 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc188 dc184 dc242 dc220
lemma dc244 : ∀ x ∈ dc192, dc178 x = false := dFord dc221
lemma dc245 : dc178 dc189 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc192 dc189 dc244 dc222
lemma dc246 : ∀ x ∈ dc197, dc178 x = false := dFord (dCat dc223 dc224)
lemma dc247 : dc178 dc193 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc197 dc193 dc246 dc225
lemma dc248 : ∀ x ∈ dc201, dc178 x = false := dFord dc226
lemma dc249 : dc178 dc198 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc201 dc198 dc248 dc227
lemma dc250 : ∀ x ∈ dc206, dc178 x = false := dFord (dCat dc228 dc229)
lemma dc251 : dc178 dc202 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc206 dc202 dc250 dc230
lemma dc252 : ∀ x ∈ dc215, dc178 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc231 dc232) dc233) dc234) dc235) dc236) dc237) dc238) (dOne dc243)) (dOne dc241)) (dOne dc251)) (dOne dc247)) (dOne dc245)) (dOne dc249))
theorem marked22t1 : markedChk (cliqueMark I22) [ea22] edgeQ22 0 12 1 0 1 = false := markedDeepRootJoin (cliqueMark I22) _ _ _ _ _ _ _ dc215 dc252 dc239
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc253 := deepEval (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12
noncomputable def dc254 := tRoot (cliqueMark I22) [ea22] edgeQ22 0 12 2 0 1
noncomputable def dc255 := dSel dc254 [12,15,32]
noncomputable def dc256 := dSel dc254 [13,14,16,98]
noncomputable def dc257 := dSel dc254 [10,2,4,173,1,11,120,3,93,58]
noncomputable def dc258 := dSel dc254 [157,140,9,78,113,5,7,0,152,71,148,49,42,72,21,149,76,75,110,80,165,151,154,155,82,115,108,34,36]
noncomputable def dc259 := dSel dc254 [150,44,84,158,74,87,90,79,88,117,138,96,164,118,121,114,168,153,156,134,170,174,8,175,176,122,142,177,178,123,143,179]
noncomputable def dc260 := dSel dc254 [144,183,185,17,23,20,26,27,18,24,19,25,46,31,45,33,48,35,51,55,60,54,59,83,136,127,160]
noncomputable def dc261 := dc255 ++ dc256 ++ dc257 ++ dc258 ++ dc259 ++ dc260
set_option maxRecDepth 100000 in
theorem dc262 : dGood dc253 dc255 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc263 : dGood dc253 dc256 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc264 : dGood dc253 dc257 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc265 : dGood dc253 dc258 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc266 : dGood dc253 dc259 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc267 : dGood dc253 dc260 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc268 : markedBudgetWith (cliqueMark I22) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ22.map fun _ => 16)) 12 dc261 mode 12) [ea22] edgeQ22 0 12 2 0 1 = false := by decide +kernel
lemma dc269 : ∀ x ∈ dc261, dc253 x = false := dFord (dCat (dCat (dCat (dCat (dCat dc262 dc263) dc264) dc265) dc266) dc267)
theorem marked22t2 : markedChk (cliqueMark I22) [ea22] edgeQ22 0 12 2 0 1 = false := markedDeepRootJoin (cliqueMark I22) _ _ _ _ _ _ _ dc261 dc269 dc268
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem marked22t3 : markedChk (cliqueMark I22) [ea22] edgeQ22 0 12 3 0 1 = false := by decide +kernel
lemma N22 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea22 (remT (unaryE ea22) t) := by
  interval_cases t
  · exact binaryMarked (firstOp:=false) (x:=1) (y:=4) (inputs:=I22) (prior:=P22) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready22.1 base ready22.2.1 ready22.2.2 (by decide +kernel) (by decide +kernel) (earlier22 base 1 (by decide) (by decide)) marked22t1
  · exact binaryMarked (firstOp:=false) (x:=1) (y:=4) (inputs:=I22) (prior:=P22) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready22.1 base ready22.2.1 ready22.2.2 (by decide +kernel) (by decide +kernel) (earlier22 base 2 (by decide) (by decide)) marked22t2
  · exact binaryMarked (firstOp:=false) (x:=1) (y:=4) (inputs:=I22) (prior:=P22) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready22.1 base ready22.2.1 ready22.2.2 (by decide +kernel) (by decide +kernel) (earlier22 base 3 (by decide) (by decide)) marked22t3
def I25 : List ℕ := [ip 0 0, ip 1 0, ip 2 0, ip 3 0, ip 5 0]
def P25 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5), (6, 1), (6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (7, 5), (8, 3), (8, 5), (9, 5)]
lemma earlier25 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P25, Excluded 12 p t := by
  intro p hp
  simp only [P25, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc270 := deepEval (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12
noncomputable def dc271 := tRoot (cliqueMark I25) [ea25] edgeQ25 0 12 1 0 1
noncomputable def dc272 := dc271.getD 18 default
noncomputable def dc273 := tLeaves (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc272
noncomputable def dc274 := dSel dc273 [9,13,11,10,14,7,12,8,6]
noncomputable def dc275 := dc274
noncomputable def dc276 := dc271.getD 13 default
noncomputable def dc277 := tLeaves (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc276
noncomputable def dc278 := dSel dc277 [3,12,6,9,2,22,16,20,0,50,52,19,21,23,4,11,14,5,8,18,15,38,30]
noncomputable def dc279 := dc278
noncomputable def dc280 := dc271.getD 8 default
noncomputable def dc281 := tLeaves (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc280
noncomputable def dc282 := dSel dc281 [2,35,31,0,49,27,30,1,36,25,39,51,18,22,37,46,45,28,82,21,3,7,47,43,4,57,76,78,79,116,84,109]
noncomputable def dc283 := dSel dc281 [98,80,97]
noncomputable def dc284 := dc282 ++ dc283
noncomputable def dc285 := dc271.getD 10 default
noncomputable def dc286 := tLeaves (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc285
noncomputable def dc287 := dSel dc286 [38,2,28,29,32,23,15,0,40,26,42,48,54,31,1,39,44,46,52,25,3,13,20,8,4]
noncomputable def dc288 := dc287
noncomputable def dc289 := dc271.getD 19 default
noncomputable def dc290 := tLeaves (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc289
noncomputable def dc291 := dSel dc290 [12,13,0,11,14,8,9,4,6,10]
noncomputable def dc292 := dc291
noncomputable def dc293 := dc271.getD 22 default
noncomputable def dc294 := tLeaves (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc293
noncomputable def dc295 := dSel dc294 [16,22,0,19,9,5,24,11,4,8,15,6,10,2,13,7,21,23,49]
noncomputable def dc296 := dc295
noncomputable def dc297 := dSel dc271 [2,66]
noncomputable def dc298 := dSel dc271 [16,20]
noncomputable def dc299 := dSel dc271 [21,9,31]
noncomputable def dc300 := dSel dc271 [7,15,38]
noncomputable def dc301 := dSel dc271 [11,17,51]
noncomputable def dc302 := dSel dc271 [1,3]
noncomputable def dc303 := dSel dc271 [23,14,65,57]
noncomputable def dc304 := dSel dc271 [12,68,69,5,91]
noncomputable def dc305 := dSel dc271 [0,67,40,53,50,75,56]
noncomputable def dc306 := dSel dc271 [60,77,64,70,79,52,55,88,71,48,27]
noncomputable def dc307 := dSel dc271 [72,82,85,74,24,26,44,34,96,30,33,78,81,84,87,42]
noncomputable def dc308 := dSel dc271 [76,90,93,25,47,45,62,63,54,28,29,37,59]
noncomputable def dc309 := dc297 ++ dc298 ++ dc299 ++ dc300 ++ dc301 ++ dc302 ++ dc303 ++ dc304 ++ dc305 ++ dc306 ++ dc307 ++ dc308 ++ [dc293] ++ [dc280] ++ [dc285] ++ [dc289] ++ [dc276] ++ [dc272]
set_option maxRecDepth 100000 in
theorem dc310 : dGood dc270 dc274 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc311 : deepOuter (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc275 dc272 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc312 : dGood dc270 dc278 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc313 : deepOuter (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc279 dc276 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc314 : dGood dc270 dc282 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc315 : dGood dc270 dc283 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc316 : deepOuter (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc284 dc280 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc317 : dGood dc270 dc287 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc318 : deepOuter (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc288 dc285 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc319 : dGood dc270 dc291 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc320 : deepOuter (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc292 dc289 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc321 : dGood dc270 dc295 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc322 : deepOuter (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc296 dc293 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc323 : dGood dc270 dc297 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc324 : dGood dc270 dc298 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc325 : dGood dc270 dc299 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc326 : dGood dc270 dc300 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc327 : dGood dc270 dc301 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc328 : dGood dc270 dc302 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc329 : dGood dc270 dc303 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc330 : dGood dc270 dc304 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc331 : dGood dc270 dc305 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc332 : dGood dc270 dc306 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc333 : dGood dc270 dc307 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc334 : dGood dc270 dc308 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc335 : markedBudgetWith (cliqueMark I25) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc309 mode 12) [ea25] edgeQ25 0 12 1 0 1 = false := by decide +kernel
lemma dc336 : ∀ x ∈ dc275, dc270 x = false := dFord dc310
lemma dc337 : dc270 dc272 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc275 dc272 dc336 dc311
lemma dc338 : ∀ x ∈ dc279, dc270 x = false := dFord dc312
lemma dc339 : dc270 dc276 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc279 dc276 dc338 dc313
lemma dc340 : ∀ x ∈ dc284, dc270 x = false := dFord (dCat dc314 dc315)
lemma dc341 : dc270 dc280 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc284 dc280 dc340 dc316
lemma dc342 : ∀ x ∈ dc288, dc270 x = false := dFord dc317
lemma dc343 : dc270 dc285 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc288 dc285 dc342 dc318
lemma dc344 : ∀ x ∈ dc292, dc270 x = false := dFord dc319
lemma dc345 : dc270 dc289 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc292 dc289 dc344 dc320
lemma dc346 : ∀ x ∈ dc296, dc270 x = false := dFord dc321
lemma dc347 : dc270 dc293 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc296 dc293 dc346 dc322
lemma dc348 : ∀ x ∈ dc309, dc270 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc323 dc324) dc325) dc326) dc327) dc328) dc329) dc330) dc331) dc332) dc333) dc334) (dOne dc347)) (dOne dc341)) (dOne dc343)) (dOne dc345)) (dOne dc339)) (dOne dc337))
theorem marked25t1 : markedChk (cliqueMark I25) [ea25] edgeQ25 0 12 1 0 1 = false := markedDeepRootJoin (cliqueMark I25) _ _ _ _ _ _ _ dc309 dc348 dc335
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc349 := deepEval (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12
noncomputable def dc350 := tRoot (cliqueMark I25) [ea25] edgeQ25 0 12 2 0 1
noncomputable def dc351 := dSel dc350 [22,13,19,8,129]
noncomputable def dc352 := dSel dc350 [10,18,21,16,2,125,126,130,15]
noncomputable def dc353 := dSel dc350 [23,1,5,65,146,12,11,128,91,17,114,180,3,84,138,33]
noncomputable def dc354 := dSel dc350 [0,7,81,48,87,14,9,123,88,86,159,161,105,140,166,163,20,50,179,40,111,100,141,133,155,42,54,73,156,83,93,143]
noncomputable def dc355 := dSel dc350 [135,94,173,158,109,117,144,160,148,185,184,6,194,187,95,118,189,150,190,192,27,67,49,85,92,107,106,147,139,162,182,24]
noncomputable def dc356 := dSel dc350 [30,28,34,35,25,31,26,32,56,39,55,58,44,51,69,53,72,43,61,66,168]
noncomputable def dc357 := dc351 ++ dc352 ++ dc353 ++ dc354 ++ dc355 ++ dc356
set_option maxRecDepth 100000 in
theorem dc358 : dGood dc349 dc351 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc359 : dGood dc349 dc352 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc360 : dGood dc349 dc353 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc361 : dGood dc349 dc354 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc362 : dGood dc349 dc355 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc363 : dGood dc349 dc356 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc364 : markedBudgetWith (cliqueMark I25) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ25.map fun _ => 16)) 12 dc357 mode 12) [ea25] edgeQ25 0 12 2 0 1 = false := by decide +kernel
lemma dc365 : ∀ x ∈ dc357, dc349 x = false := dFord (dCat (dCat (dCat (dCat (dCat dc358 dc359) dc360) dc361) dc362) dc363)
theorem marked25t2 : markedChk (cliqueMark I25) [ea25] edgeQ25 0 12 2 0 1 = false := markedDeepRootJoin (cliqueMark I25) _ _ _ _ _ _ _ dc357 dc365 dc364
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem marked25t3 : markedChk (cliqueMark I25) [ea25] edgeQ25 0 12 3 0 1 = false := by decide +kernel
lemma N25 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea25 (remT (unaryE ea25) t) := by
  interval_cases t
  · exact binaryMarked (firstOp:=false) (x:=2) (y:=4) (inputs:=I25) (prior:=P25) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready25.1 base ready25.2.1 ready25.2.2 (by decide +kernel) (by decide +kernel) (earlier25 base 1 (by decide) (by decide)) marked25t1
  · exact binaryMarked (firstOp:=false) (x:=2) (y:=4) (inputs:=I25) (prior:=P25) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready25.1 base ready25.2.1 ready25.2.2 (by decide +kernel) (by decide +kernel) (earlier25 base 2 (by decide) (by decide)) marked25t2
  · exact binaryMarked (firstOp:=false) (x:=2) (y:=4) (inputs:=I25) (prior:=P25) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready25.1 base ready25.2.1 ready25.2.2 (by decide +kernel) (by decide +kernel) (earlier25 base 3 (by decide) (by decide)) marked25t3
def I14 : List ℕ := [ip 0 0, ip 1 0, ip 2 0, ip 3 0, ip 5 0]
def P14 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5), (6, 1), (6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (7, 5), (8, 3), (8, 5), (9, 5)]
lemma earlier14 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ P14, Excluded 12 p t := by
  intro p hp
  simp only [P14, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N13 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact N28 base t ha hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc366 := deepEval (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12
noncomputable def dc367 := tRoot (cliqueMark I14) [ea14] edgeQ14 0 12 1 0 1
noncomputable def dc368 := dc367.getD 16 default
noncomputable def dc369 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc368
noncomputable def dc370 := dSel dc369 [3,6,38,9,30,34,36,20,32,22,61,51,2,5,8,11,31,28,35]
noncomputable def dc371 := dc370
noncomputable def dc372 := dc367.getD 18 default
noncomputable def dc373 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc372
noncomputable def dc374 := dSel dc373 [9,0,34,6,30,38,83,74,32,19,36,43,53,78,90,2,5,8,11,31,28,3,39,22,40,50,41,71]
noncomputable def dc375 := dc374
noncomputable def dc376 := dc367.getD 20 default
noncomputable def dc377 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc376
noncomputable def dc378 := dSel dc377 [9,24,0,3,34,30,38,28,32,36,2,5,8,11,25,31,17,103,20]
noncomputable def dc379 := dSel dc377 [100,6,39,42,66,108,1,22,14,21,13,16,50,41,74,127,46]
noncomputable def dc380 := dc378 ++ dc379
noncomputable def dc381 := dc367.getD 22 default
noncomputable def dc382 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc381
noncomputable def dc383 := dSel dc382 [6,24,3,30,0,38,5,11,28,34,32,16,121,118,2,8,25,35,39,36,45]
noncomputable def dc384 := dSel dc382 [53,129,7,19,40,41,77,42,101,43,120,80]
noncomputable def dc385 := dc383 ++ dc384
noncomputable def dc386 := dc367.getD 0 default
noncomputable def dc387 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc386
noncomputable def dc388 := dSel dc387 [27,11,21,25,29,0,19,23,13,12]
noncomputable def dc389 := dSel dc387 [9,28,2,10,15,22,26,99,7,30,20,24,49,81,55,59,79,40,53,89,94,61,111,117,65,101,102,17,4,14,31,48]
noncomputable def dc390 := dSel dc387 [105,128,47,32,34,51,33,86,35,108,36,131,37,67,69,45,80,104,127,85,107,56,74,76,78,42,75,96,43,77]
noncomputable def dc391 := dc388 ++ dc389 ++ dc390
noncomputable def dc392 := dc367.getD 3 default
noncomputable def dc393 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc392
noncomputable def dc394 := dSel dc393 [23,29,13,21,25,27,6,19,11,31]
noncomputable def dc395 := dSel dc393 [0,14,24,9,2,15,30,73,77,87,7,22,20,26,32,37,43,39,56,59,47,52,79,57,60,132,95,67,83,97,85,135]
noncomputable def dc396 := dSel dc393 [145,17,4,12,16,1,8,28,62,106,105,126,71,44,94,35,75,34,108,36,129,38,40,91,69,104,125,93,128,53,46,51]
noncomputable def dc397 := dSel dc393 [50,54,96]
noncomputable def dc398 := dc394 ++ dc395 ++ dc396 ++ dc397
noncomputable def dc399 := dc367.getD 6 default
noncomputable def dc400 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc399
noncomputable def dc401 := dSel dc400 [25,13,23,31,18,17,27,0,29,19]
noncomputable def dc402 := dSel dc400 [6,21,8,11,14,7,2,24,28,26,15,32,41,49,52,58,63,93,75,80,84,120,96,119,100,99,123,129,20,4,9,12]
noncomputable def dc403 := dSel dc400 [22,10,34,35,87,90,72,117,106,116,74,79,83,78,82,98,101,131,103,86,122,128,102,127,5,3,16,1]
noncomputable def dc404 := dc401 ++ dc402 ++ dc403
noncomputable def dc405 := dc367.getD 9 default
noncomputable def dc406 := tLeaves (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc405
noncomputable def dc407 := dSel dc406 [21,10,27,31,17,18,23,25,6]
noncomputable def dc408 := dSel dc406 [29,8,0,13,28,11,2,24,73,76,82,19,7,9,15,22,32,34,62,86,47,70,50,53,58,92,72,96,95,119,105,122]
noncomputable def dc409 := dSel dc406 [4,14,26,30,64,87,112,67,35,90,36,38,43,61,63,127,110,66,89,113]
noncomputable def dc410 := dc407 ++ dc408 ++ dc409
noncomputable def dc411 := dSel dc367 [10,57]
noncomputable def dc412 := dSel dc367 [1,51,44]
noncomputable def dc413 := dSel dc367 [11,75,61]
noncomputable def dc414 := dSel dc367 [4,43,111]
noncomputable def dc415 := dSel dc367 [8,17]
noncomputable def dc416 := dSel dc367 [7,13]
noncomputable def dc417 := dSel dc367 [2,78,92]
noncomputable def dc418 := dSel dc367 [5,19]
noncomputable def dc419 := dSel dc367 [21,64,112,30]
noncomputable def dc420 := dSel dc367 [23,72,115,45]
noncomputable def dc421 := dSel dc367 [54,15,95,98,118]
noncomputable def dc422 := dSel dc367 [34,35,68,50,53,56,71,82]
noncomputable def dc423 := dSel dc367 [26,27,28,29,47,74,77,97,24]
noncomputable def dc424 := dSel dc367 [117,91,38,94,114,85,105,40,102,36,37,33]
noncomputable def dc425 := dSel dc367 [65,59,63,88,39,60,66,48,69,89,109,42,108,84,80,104,25,81]
noncomputable def dc426 := dSel dc367 [86,106,31,55,73,76,100]
noncomputable def dc427 := dc411 ++ dc412 ++ dc413 ++ dc414 ++ dc415 ++ dc416 ++ dc417 ++ dc418 ++ dc419 ++ dc420 ++ dc421 ++ dc422 ++ dc423 ++ dc424 ++ dc425 ++ dc426 ++ [dc386] ++ [dc392] ++ [dc399] ++ [dc405] ++ [dc376] ++ [dc381] ++ [dc372] ++ [dc368]
set_option maxRecDepth 100000 in
theorem dc428 : dGood dc366 dc370 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc429 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc371 dc368 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc430 : dGood dc366 dc374 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc431 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc375 dc372 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc432 : dGood dc366 dc378 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc433 : dGood dc366 dc379 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc434 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc380 dc376 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc435 : dGood dc366 dc383 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc436 : dGood dc366 dc384 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc437 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc385 dc381 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc438 : dGood dc366 dc388 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc439 : dGood dc366 dc389 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc440 : dGood dc366 dc390 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc441 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc391 dc386 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc442 : dGood dc366 dc394 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc443 : dGood dc366 dc395 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc444 : dGood dc366 dc396 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc445 : dGood dc366 dc397 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc446 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc398 dc392 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc447 : dGood dc366 dc401 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc448 : dGood dc366 dc402 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc449 : dGood dc366 dc403 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc450 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc404 dc399 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc451 : dGood dc366 dc407 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc452 : dGood dc366 dc408 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc453 : dGood dc366 dc409 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc454 : deepOuter (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc410 dc405 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc455 : dGood dc366 dc411 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc456 : dGood dc366 dc412 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc457 : dGood dc366 dc413 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc458 : dGood dc366 dc414 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc459 : dGood dc366 dc415 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc460 : dGood dc366 dc416 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc461 : dGood dc366 dc417 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc462 : dGood dc366 dc418 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc463 : dGood dc366 dc419 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc464 : dGood dc366 dc420 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc465 : dGood dc366 dc421 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc466 : dGood dc366 dc422 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc467 : dGood dc366 dc423 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc468 : dGood dc366 dc424 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc469 : dGood dc366 dc425 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc470 : dGood dc366 dc426 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc471 : markedBudgetWith (cliqueMark I14) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc427 mode 12) [ea14] edgeQ14 0 12 1 0 1 = false := by decide +kernel
lemma dc472 : ∀ x ∈ dc371, dc366 x = false := dFord dc428
lemma dc473 : dc366 dc368 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc371 dc368 dc472 dc429
lemma dc474 : ∀ x ∈ dc375, dc366 x = false := dFord dc430
lemma dc475 : dc366 dc372 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc375 dc372 dc474 dc431
lemma dc476 : ∀ x ∈ dc380, dc366 x = false := dFord (dCat dc432 dc433)
lemma dc477 : dc366 dc376 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc380 dc376 dc476 dc434
lemma dc478 : ∀ x ∈ dc385, dc366 x = false := dFord (dCat dc435 dc436)
lemma dc479 : dc366 dc381 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc385 dc381 dc478 dc437
lemma dc480 : ∀ x ∈ dc391, dc366 x = false := dFord (dCat (dCat dc438 dc439) dc440)
lemma dc481 : dc366 dc386 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc391 dc386 dc480 dc441
lemma dc482 : ∀ x ∈ dc398, dc366 x = false := dFord (dCat (dCat (dCat dc442 dc443) dc444) dc445)
lemma dc483 : dc366 dc392 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc398 dc392 dc482 dc446
lemma dc484 : ∀ x ∈ dc404, dc366 x = false := dFord (dCat (dCat dc447 dc448) dc449)
lemma dc485 : dc366 dc399 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc404 dc399 dc484 dc450
lemma dc486 : ∀ x ∈ dc410, dc366 x = false := dFord (dCat (dCat dc451 dc452) dc453)
lemma dc487 : dc366 dc405 = false := deepJoin (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc410 dc405 dc486 dc454
lemma dc488 : ∀ x ∈ dc427, dc366 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc455 dc456) dc457) dc458) dc459) dc460) dc461) dc462) dc463) dc464) dc465) dc466) dc467) dc468) dc469) dc470) (dOne dc481)) (dOne dc483)) (dOne dc485)) (dOne dc487)) (dOne dc477)) (dOne dc479)) (dOne dc475)) (dOne dc473))
theorem marked14t1 : markedChk (cliqueMark I14) [ea14] edgeQ14 0 12 1 0 1 = false := markedDeepRootJoin (cliqueMark I14) _ _ _ _ _ _ _ dc427 dc488 dc471
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc489 := deepEval (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12
noncomputable def dc490 := tRoot (cliqueMark I14) [ea14] edgeQ14 0 12 2 0 1
noncomputable def dc491 := dSel dc490 [6,20,22,91,107]
noncomputable def dc492 := dSel dc490 [3,2,5,16,21]
noncomputable def dc493 := dSel dc490 [9,8,11,18,29]
noncomputable def dc494 := dSel dc490 [0,13,23,140,17,19,212]
noncomputable def dc495 := dSel dc490 [76,125,1,28,30,31,154,4,7,27,59,99,83,102,85,105,151,132,134,10,25,88,137,186,235,257]
noncomputable def dc496 := dSel dc490 [47,81,148,130,196,245,228,86,199,181,248,135,202,251,232,184,233,15,74,123,221,77,48,79,62,60,128,63,177,57,226,50]
noncomputable def dc497 := dSel dc490 [92,78,95,46,80,98,82,101,104,179,72,147,129,244,150,131,153,133,230,121,247,229,201,182,183,188,170,250,231,237,14,156]
noncomputable def dc498 := dSel dc490 [204,253,109,158,255,160,256,259,161,208,211,260,261,264,265,42,89,73,138,136,122,187,172,220,61,93,142,126,190,175,239,224]
noncomputable def dc499 := dSel dc490 [41,44,45,96,55]
noncomputable def dc500 := dc491 ++ dc492 ++ dc493 ++ dc494 ++ dc495 ++ dc496 ++ dc497 ++ dc498 ++ dc499
set_option maxRecDepth 100000 in
theorem dc501 : dGood dc489 dc491 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc502 : dGood dc489 dc492 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc503 : dGood dc489 dc493 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc504 : dGood dc489 dc494 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc505 : dGood dc489 dc495 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc506 : dGood dc489 dc496 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc507 : dGood dc489 dc497 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc508 : dGood dc489 dc498 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc509 : dGood dc489 dc499 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc510 : markedBudgetWith (cliqueMark I14) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc500 mode 12) [ea14] edgeQ14 0 12 2 0 1 = false := by decide +kernel
lemma dc511 : ∀ x ∈ dc500, dc489 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc501 dc502) dc503) dc504) dc505) dc506) dc507) dc508) dc509)
theorem marked14t2 : markedChk (cliqueMark I14) [ea14] edgeQ14 0 12 2 0 1 = false := markedDeepRootJoin (cliqueMark I14) _ _ _ _ _ _ _ dc500 dc511 dc510
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc512 := deepEval (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12
noncomputable def dc513 := tRoot (cliqueMark I14) [ea14] edgeQ14 0 12 3 0 1
noncomputable def dc514 := dSel dc513 [2,5,8,11,6,9,0,13,3,104,171,204,167,28,31,70,67,137,100,132,199,14,220,287,248,314,77,95,289,249,355,315]
noncomputable def dc515 := dSel dc513 [157,182,185,323,258,361,329,25,27,68,102,134]
noncomputable def dc516 := dc514 ++ dc515
set_option maxRecDepth 100000 in
theorem dc517 : dGood dc512 dc514 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc518 : dGood dc512 dc515 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc519 : markedBudgetWith (cliqueMark I14) (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ14.map fun _ => 16)) 12 dc516 mode 12) [ea14] edgeQ14 0 12 3 0 1 = false := by decide +kernel
lemma dc520 : ∀ x ∈ dc516, dc512 x = false := dFord (dCat dc517 dc518)
theorem marked14t3 : markedChk (cliqueMark I14) [ea14] edgeQ14 0 12 3 0 1 = false := markedDeepRootJoin (cliqueMark I14) _ _ _ _ _ _ _ dc516 dc520 dc519
lemma N14 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea14 (remT (unaryE ea14) t) := by
  interval_cases t
  · exact binaryMarked (firstOp:=true) (x:=4) (y:=5) (inputs:=I14) (prior:=P14) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready14.1 base ready14.2.1 ready14.2.2 (by decide +kernel) (by decide +kernel) (earlier14 base 1 (by decide) (by decide)) marked14t1
  · exact binaryMarked (firstOp:=true) (x:=4) (y:=5) (inputs:=I14) (prior:=P14) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready14.1 base ready14.2.1 ready14.2.2 (by decide +kernel) (by decide +kernel) (earlier14 base 2 (by decide) (by decide)) marked14t2
  · exact binaryMarked (firstOp:=true) (x:=4) (y:=5) (inputs:=I14) (prior:=P14) (by decide +kernel) (by decide +kernel) (by decide +kernel) ready14.1 base ready14.2.1 ready14.2.2 (by decide +kernel) (by decide +kernel) (earlier14 base 3 (by decide) (by decide)) marked14t3
lemma binaryDone (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ p ∈ six, unaryE p = false → Excluded 12 p t := by
  intro p hp
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro h
    exact N0 base t ha hb
  · intro h
    exact mirror1 _ _ (N6 base t ha hb)
  · intro h
    exact mirror2 _ _ (N5 base t ha hb)
  · intro h
    exact N3 base t ha hb
  · intro h
    exact N4 base t ha hb
  · intro h
    exact N5 base t ha hb
  · intro h
    exact N6 base t ha hb
  · intro h
    exact mirror7 _ _ (N3 base t ha hb)
  · intro h
    exact mirror8 _ _ (N4 base t ha hb)
  · intro h
    exact N9 base t ha hb
  · intro h
    exact mirror10 _ _ (N12 base t ha hb)
  · intro h
    exact mirror11 _ _ (N13 base t ha hb)
  · intro h
    exact N12 base t ha hb
  · intro h
    exact N13 base t ha hb
  · intro h
    exact N14 base t ha hb
  · intro h
    exact N15 base t ha hb
  · intro h
    exact mirror16 _ _ (N21 base t ha hb)
  · intro h
    exact mirror17 _ _ (N20 base t ha hb)
  · intro h
    exact mirror18 _ _ (N22 base t ha hb)
  · intro h
    exact mirror19 _ _ (N23 base t ha hb)
  · intro h
    exact N20 base t ha hb
  · intro h
    exact N21 base t ha hb
  · intro h
    exact N22 base t ha hb
  · intro h
    exact N23 base t ha hb
  · intro h
    exact N24 base t ha hb
  · intro h
    exact N25 base t ha hb
  · intro h
    exact mirror26 _ _ (N28 base t ha hb)
  · intro h
    exact mirror27 _ _ (N25 base t ha hb)
  · intro h
    exact N28 base t ha hb
  · intro h
    exact N29 base t ha hb
  · intro h
    contradiction
  · intro h
    contradiction
  · intro h
    contradiction
  · intro h
    contradiction
  · intro h
    contradiction
  · intro h
    contradiction
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc521 := deepEval (lz 0) (mz 0) (pL (edgeQ31.map fun _ => 16)) 12
noncomputable def dc522 := tRoot markRaw [ea31] edgeQ31 0 12 0 0 1
noncomputable def dc523 := dSel dc522 [4,7,10,13,5]
noncomputable def dc524 := dSel dc522 [1,8,14,11,2,3]
noncomputable def dc525 := dc523 ++ dc524
set_option maxRecDepth 100000 in
theorem dc526 : dGood dc521 dc523 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc527 : dGood dc521 dc524 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc528 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ31.map fun _ => 16)) 12 dc525 mode 12) [ea31] edgeQ31 0 12 0 0 1 = false := by decide +kernel
lemma dc529 : ∀ x ∈ dc525, dc521 x = false := dFord (dCat dc526 dc527)
theorem marked31t1 : markedChk markRaw [ea31] edgeQ31 0 12 0 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc525 dc529 dc528
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc530 := deepEval (lz 0) (mz 0) (pL (edgeQ31.map fun _ => 16)) 12
noncomputable def dc531 := tRoot markRaw [ea31] edgeQ31 0 12 1 0 1
noncomputable def dc532 := dSel dc531 [4,1,7,10,5]
noncomputable def dc533 := dSel dc531 [13,60,9,58,3,6,12,39]
noncomputable def dc534 := dSel dc531 [2,0,62,8,11,64,66,25,68,70,14]
noncomputable def dc535 := dSel dc531 [47,45,40,30,46,52,69,22,51,33,27,41,50,71,59,43,49,44,55,48,56,15]
noncomputable def dc536 := dSel dc531 [53,57,63,65,17,21,29,32,35,36]
noncomputable def dc537 := dc532 ++ dc533 ++ dc534 ++ dc535 ++ dc536
set_option maxRecDepth 100000 in
theorem dc538 : dGood dc530 dc532 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc539 : dGood dc530 dc533 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc540 : dGood dc530 dc534 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc541 : dGood dc530 dc535 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc542 : dGood dc530 dc536 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc543 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ31.map fun _ => 16)) 12 dc537 mode 12) [ea31] edgeQ31 0 12 1 0 1 = false := by decide +kernel
lemma dc544 : ∀ x ∈ dc537, dc530 x = false := dFord (dCat (dCat (dCat (dCat dc538 dc539) dc540) dc541) dc542)
theorem marked31t2 : markedChk markRaw [ea31] edgeQ31 0 12 1 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc537 dc544 dc543
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc545 := deepEval (lz 0) (mz 0) (pL (edgeQ31.map fun _ => 16)) 12
noncomputable def dc546 := tRoot markRaw [ea31] edgeQ31 0 12 2 0 1
noncomputable def dc547 := dSel dc546 [127,4,129,1,133,131,128,10,135,81]
noncomputable def dc548 := dSel dc546 [3,7,130,9,132,13,48,126,6,12,134,174,0,99,185,33,31]
noncomputable def dc549 := dSel dc546 [150,161,176,117,5,148,158,72,190,200,195,210,205,186,191,164,201,196,167,211,181,187,192,189,175,202,197,177,2,147,157,151]
noncomputable def dc550 := dSel dc546 [163,153,39,58,169,79,90,80,152,98,56,154,50,116,206,156,170,173,94,188,193,198,112,74,194,213,208,182,96,113,92,199]
noncomputable def dc551 := dSel dc546 [209,183,184,212,110,207,8,11,14,179,86,104,122,124,125,46,159,22,21,28,24,25,136,141,19,26,16,137,23,140,145,138]
noncomputable def dc552 := dSel dc546 [143,139,144,45,30,44,35,52,37,55,166,40,59,61,149,47,160,42,62,49,155,97,115,108,73,36,53,91]
noncomputable def dc553 := dc547 ++ dc548 ++ dc549 ++ dc550 ++ dc551 ++ dc552
set_option maxRecDepth 100000 in
theorem dc554 : dGood dc545 dc547 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc555 : dGood dc545 dc548 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc556 : dGood dc545 dc549 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc557 : dGood dc545 dc550 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc558 : dGood dc545 dc551 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc559 : dGood dc545 dc552 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc560 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ31.map fun _ => 16)) 12 dc553 mode 12) [ea31] edgeQ31 0 12 2 0 1 = false := by decide +kernel
lemma dc561 : ∀ x ∈ dc553, dc545 x = false := dFord (dCat (dCat (dCat (dCat (dCat dc554 dc555) dc556) dc557) dc558) dc559)
theorem marked31t3 : markedChk markRaw [ea31] edgeQ31 0 12 2 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc553 dc561 dc560
lemma N31 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea31 (remT (unaryE ea31) t) := by
  interval_cases t
  · exact unaryMarked (x:=1) (t:=0) (by decide +kernel) (by decide +kernel) ready31.1 base ready31.2.1 ready31.2.2 (binaryDone base 1 (by decide) (by decide)) marked31t1
  · exact unaryMarked (x:=1) (t:=1) (by decide +kernel) (by decide +kernel) ready31.1 base ready31.2.1 ready31.2.2 (binaryDone base 2 (by decide) (by decide)) marked31t2
  · exact unaryMarked (x:=1) (t:=2) (by decide +kernel) (by decide +kernel) ready31.1 base ready31.2.1 ready31.2.2 (binaryDone base 3 (by decide) (by decide)) marked31t3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc562 := deepEval (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12
noncomputable def dc563 := tRoot markRaw [ea32] edgeQ32 0 12 0 0 1
noncomputable def dc564 := dSel dc563 [1,4,10,3]
noncomputable def dc565 := dSel dc563 [13,2,7,11,5]
noncomputable def dc566 := dSel dc563 [8,14,9]
noncomputable def dc567 := dc564 ++ dc565 ++ dc566
set_option maxRecDepth 100000 in
theorem dc568 : dGood dc562 dc564 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc569 : dGood dc562 dc565 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc570 : dGood dc562 dc566 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc571 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 dc567 mode 12) [ea32] edgeQ32 0 12 0 0 1 = false := by decide +kernel
lemma dc572 : ∀ x ∈ dc567, dc562 x = false := dFord (dCat (dCat dc568 dc569) dc570)
theorem marked32t1 : markedChk markRaw [ea32] edgeQ32 0 12 0 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc567 dc572 dc571
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc573 := deepEval (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12
noncomputable def dc574 := tRoot markRaw [ea32] edgeQ32 0 12 1 0 1
noncomputable def dc575 := dSel dc574 [1,4,10,13,30]
noncomputable def dc576 := dSel dc574 [58,7,60,3,2,5,70]
noncomputable def dc577 := dSel dc574 [62,6,9,12,11,64,66,0,14]
noncomputable def dc578 := dSel dc574 [8,39,40,25,59,52,22,46,68,44,71,47,21,29,36,45,51,34,37,43,49]
noncomputable def dc579 := dSel dc574 [55,48,53,57,61,63,65,15,33,27,54]
noncomputable def dc580 := dc575 ++ dc576 ++ dc577 ++ dc578 ++ dc579
set_option maxRecDepth 100000 in
theorem dc581 : dGood dc573 dc575 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc582 : dGood dc573 dc576 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc583 : dGood dc573 dc577 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc584 : dGood dc573 dc578 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc585 : dGood dc573 dc579 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc586 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 dc580 mode 12) [ea32] edgeQ32 0 12 1 0 1 = false := by decide +kernel
lemma dc587 : ∀ x ∈ dc580, dc573 x = false := dFord (dCat (dCat (dCat (dCat dc581 dc582) dc583) dc584) dc585)
theorem marked32t2 : markedChk markRaw [ea32] edgeQ32 0 12 1 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc580 dc587 dc586
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc588 := deepEval (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12
noncomputable def dc589 := tRoot markRaw [ea32] edgeQ32 0 12 2 0 1
noncomputable def dc590 := dSel dc589 [127,129,1,131,4,128,3,210]
noncomputable def dc591 := dSel dc589 [7,133,135,130,132,6,10,13,48,9,12]
noncomputable def dc592 := dSel dc589 [134,185,191,176,126,190,186,0,205,152,33,150,161,174,177,99,117,11,148,158,79,200,195,73,80,164]
noncomputable def dc593 := dSel dc589 [57,116,201,196,211,206,81,198,189,183,202,197,207,2,5,14,122,136,145,138,45,30,44,147,157,163,55,166,155,169,72,97]
noncomputable def dc594 := dSel dc589 [115,108,36,53,50,39,98,91,41,60,109,43,63,167,156,170,173,181,84,188,193,203,194,208,175,113,121,92,212,110,204,8]
noncomputable def dc595 := dSel dc589 [179,86,104,106,124,125,15,22,20,21,28,24,26,141,139,144,140,16,137,142,143,18,25,31,35,52,151,38,58,149,47,160]
noncomputable def dc596 := dSel dc589 [40,59,42,62,49,37,153,171]
noncomputable def dc597 := dc590 ++ dc591 ++ dc592 ++ dc593 ++ dc594 ++ dc595 ++ dc596
set_option maxRecDepth 100000 in
theorem dc598 : dGood dc588 dc590 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc599 : dGood dc588 dc591 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc600 : dGood dc588 dc592 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc601 : dGood dc588 dc593 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc602 : dGood dc588 dc594 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc603 : dGood dc588 dc595 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc604 : dGood dc588 dc596 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc605 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ32.map fun _ => 16)) 12 dc597 mode 12) [ea32] edgeQ32 0 12 2 0 1 = false := by decide +kernel
lemma dc606 : ∀ x ∈ dc597, dc588 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat dc598 dc599) dc600) dc601) dc602) dc603) dc604)
theorem marked32t3 : markedChk markRaw [ea32] edgeQ32 0 12 2 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc597 dc606 dc605
lemma N32 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea32 (remT (unaryE ea32) t) := by
  interval_cases t
  · exact unaryMarked (x:=2) (t:=0) (by decide +kernel) (by decide +kernel) ready32.1 base ready32.2.1 ready32.2.2 (binaryDone base 1 (by decide) (by decide)) marked32t1
  · exact unaryMarked (x:=2) (t:=1) (by decide +kernel) (by decide +kernel) ready32.1 base ready32.2.1 ready32.2.2 (binaryDone base 2 (by decide) (by decide)) marked32t2
  · exact unaryMarked (x:=2) (t:=2) (by decide +kernel) (by decide +kernel) ready32.1 base ready32.2.1 ready32.2.2 (binaryDone base 3 (by decide) (by decide)) marked32t3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc607 := deepEval (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12
noncomputable def dc608 := tRoot markRaw [ea34] edgeQ34 0 12 0 0 1
noncomputable def dc609 := dSel dc608 [19,7]
noncomputable def dc610 := dSel dc608 [11,6,8]
noncomputable def dc611 := dSel dc608 [3,2,16]
noncomputable def dc612 := dSel dc608 [15,14,18,13]
noncomputable def dc613 := dSel dc608 [10,12,4,17,0]
noncomputable def dc614 := dSel dc608 [1]
noncomputable def dc615 := dc609 ++ dc610 ++ dc611 ++ dc612 ++ dc613 ++ dc614
set_option maxRecDepth 100000 in
theorem dc616 : dGood dc607 dc609 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc617 : dGood dc607 dc610 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc618 : dGood dc607 dc611 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc619 : dGood dc607 dc612 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc620 : dGood dc607 dc613 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc621 : dGood dc607 dc614 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc622 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 dc615 mode 12) [ea34] edgeQ34 0 12 0 0 1 = false := by decide +kernel
lemma dc623 : ∀ x ∈ dc615, dc607 x = false := dFord (dCat (dCat (dCat (dCat (dCat dc616 dc617) dc618) dc619) dc620) dc621)
theorem marked34t1 : markedChk markRaw [ea34] edgeQ34 0 12 0 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc615 dc623 dc622
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc624 := deepEval (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12
noncomputable def dc625 := tRoot markRaw [ea34] edgeQ34 0 12 1 0 1
noncomputable def dc626 := dSel dc625 [2,56,6,73]
noncomputable def dc627 := dSel dc625 [3,58,10,14,33]
noncomputable def dc628 := dSel dc625 [8,12,60,4,69]
noncomputable def dc629 := dSel dc625 [11,18,7,16,71]
noncomputable def dc630 := dSel dc625 [15,19,64,62,59,0]
noncomputable def dc631 := dSel dc625 [61,63,57,67,1,27,34,55,47,54,32]
noncomputable def dc632 := dSel dc625 [5,13,40,46,53,9,17,36,30,31,37,38,39,41,66,29,43,68]
noncomputable def dc633 := dSel dc625 [50,44,48,76,78,79,51,45,65,77]
noncomputable def dc634 := dc626 ++ dc627 ++ dc628 ++ dc629 ++ dc630 ++ dc631 ++ dc632 ++ dc633
set_option maxRecDepth 100000 in
theorem dc635 : dGood dc624 dc626 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc636 : dGood dc624 dc627 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc637 : dGood dc624 dc628 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc638 : dGood dc624 dc629 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc639 : dGood dc624 dc630 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc640 : dGood dc624 dc631 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc641 : dGood dc624 dc632 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc642 : dGood dc624 dc633 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc643 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 dc634 mode 12) [ea34] edgeQ34 0 12 1 0 1 = false := by decide +kernel
lemma dc644 : ∀ x ∈ dc634, dc624 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat (dCat dc635 dc636) dc637) dc638) dc639) dc640) dc641) dc642)
theorem marked34t2 : markedChk markRaw [ea34] edgeQ34 0 12 1 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc634 dc644 dc643
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc645 := deepEval (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12
noncomputable def dc646 := tRoot markRaw [ea34] edgeQ34 0 12 2 0 1
noncomputable def dc647 := dSel dc646 [113,2,114,116,8,4,118,112]
noncomputable def dc648 := dSel dc646 [12,120,16,115,117,119,121,6,10,183]
noncomputable def dc649 := dSel dc646 [14,18,107,0,185,50,69,88,181,204,159,170,55,133,144,179,198,201,142,153,34]
noncomputable def dc650 := dSel dc646 [148,61,164,175,99,3,7,11,15,19,36,63,178,138,149,195,56,75,102,94,137,42,80,151,152,163,1,5,9,13,17,44]
noncomputable def dc651 := dSel dc646 [82,74,180,182,184,186,160,155,171,166,51,37,45,70,64,89,83,108,100,39,58,40,41,59,78,60,97,139,150,145,135,140]
noncomputable def dc652 := dSel dc646 [161,156,136,141,172,167,162,157,173,168,158,174,169,90,109,91,110,111,21,29,33,22,31,193,126,26,131,20,28,124,125,130]
noncomputable def dc653 := dSel dc646 [122,127,123,128,101,93,194,38,46,197,192,177,196,57]
noncomputable def dc654 := dc647 ++ dc648 ++ dc649 ++ dc650 ++ dc651 ++ dc652 ++ dc653
set_option maxRecDepth 100000 in
theorem dc655 : dGood dc645 dc647 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc656 : dGood dc645 dc648 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc657 : dGood dc645 dc649 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc658 : dGood dc645 dc650 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc659 : dGood dc645 dc651 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc660 : dGood dc645 dc652 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc661 : dGood dc645 dc653 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc662 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ34.map fun _ => 16)) 12 dc654 mode 12) [ea34] edgeQ34 0 12 2 0 1 = false := by decide +kernel
lemma dc663 : ∀ x ∈ dc654, dc645 x = false := dFord (dCat (dCat (dCat (dCat (dCat (dCat dc655 dc656) dc657) dc658) dc659) dc660) dc661)
theorem marked34t3 : markedChk markRaw [ea34] edgeQ34 0 12 2 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc654 dc663 dc662
lemma N34 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea34 (remT (unaryE ea34) t) := by
  interval_cases t
  · exact unaryMarked (x:=4) (t:=0) (by decide +kernel) (by decide +kernel) ready34.1 base ready34.2.1 ready34.2.2 (binaryDone base 1 (by decide) (by decide)) marked34t1
  · exact unaryMarked (x:=4) (t:=1) (by decide +kernel) (by decide +kernel) ready34.1 base ready34.2.1 ready34.2.2 (binaryDone base 2 (by decide) (by decide)) marked34t2
  · exact unaryMarked (x:=4) (t:=2) (by decide +kernel) (by decide +kernel) ready34.1 base ready34.2.1 ready34.2.2 (binaryDone base 3 (by decide) (by decide)) marked34t3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc664 := deepEval (lz 0) (mz 0) (pL (edgeQ35.map fun _ => 16)) 12
noncomputable def dc665 := tRoot markRaw [ea35] edgeQ35 0 12 0 0 1
noncomputable def dc666 := dSel dc665 [0,3,6,2,9,12]
noncomputable def dc667 := dSel dc665 [11,14]
noncomputable def dc668 := dc666 ++ dc667
set_option maxRecDepth 100000 in
theorem dc669 : dGood dc664 dc666 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc670 : dGood dc664 dc667 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc671 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ35.map fun _ => 16)) 12 dc668 mode 12) [ea35] edgeQ35 0 12 0 0 1 = false := by decide +kernel
lemma dc672 : ∀ x ∈ dc668, dc664 x = false := dFord (dCat dc669 dc670)
theorem marked35t1 : markedChk markRaw [ea35] edgeQ35 0 12 0 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc668 dc672 dc671
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc673 := deepEval (lz 0) (mz 0) (pL (edgeQ35.map fun _ => 16)) 12
noncomputable def dc674 := tRoot markRaw [ea35] edgeQ35 0 12 1 0 1
noncomputable def dc675 := dSel dc674 [0,6,3,9,12,56]
noncomputable def dc676 := dSel dc674 [2,11,5,14,8,58,57,51]
noncomputable def dc677 := dSel dc674 [60,62,64,63,59,65,33,45,61,17,39,20,46,36,47,42,66,26,34,40,35,52]
noncomputable def dc678 := dSel dc674 [41,53,48,54,69,70,67,28,23,37]
noncomputable def dc679 := dc675 ++ dc676 ++ dc677 ++ dc678
set_option maxRecDepth 100000 in
theorem dc680 : dGood dc673 dc675 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc681 : dGood dc673 dc676 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc682 : dGood dc673 dc677 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc683 : dGood dc673 dc678 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc684 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ35.map fun _ => 16)) 12 dc679 mode 12) [ea35] edgeQ35 0 12 1 0 1 = false := by decide +kernel
lemma dc685 : ∀ x ∈ dc679, dc673 x = false := dFord (dCat (dCat (dCat dc680 dc681) dc682) dc683)
theorem marked35t2 : markedChk markRaw [ea35] edgeQ35 0 12 1 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc679 dc685 dc684
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable abbrev dc686 := deepEval (lz 0) (mz 0) (pL (edgeQ35.map fun _ => 16)) 12
noncomputable def dc687 := tRoot markRaw [ea35] edgeQ35 0 12 2 0 1
noncomputable def dc688 := dSel dc687 [135,137,0,133,141,139,12,3]
noncomputable def dc689 := dSel dc687 [6,9,134,142,2,136,140,11,5,138,8,14,64,76,174,185,196,207,219]
noncomputable def dc690 := dSel dc687 [202,213,151,165,45,16,30,104,123,116,47,57,83,121,114,169,144,154,180,146,157,191,148,160,163,173,178,70,89,195,108,127]
noncomputable def dc691 := dSel dc687 [186,181,171,176,172,177,187,182,188,183,209,220,71,109,128,92,130,112,132,27,32,31,33,20,22,24,42,84,77,223,226,216]
noncomputable def dc692 := dSel dc687 [227,217,214,215,59,66,19,155,85,78,21,37,97,23,40,25,43,29,152,166,28,143,153,158,145,156,161,159,164,149,162,102]
noncomputable def dc693 := dSel dc687 [95,150,67,86,79,68,105,62,124,117,63,80,106,99,88]
noncomputable def dc694 := dc688 ++ dc689 ++ dc690 ++ dc691 ++ dc692 ++ dc693
set_option maxRecDepth 100000 in
theorem dc695 : dGood dc686 dc688 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc696 : dGood dc686 dc689 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc697 : dGood dc686 dc690 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc698 : dGood dc686 dc691 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc699 : dGood dc686 dc692 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc700 : dGood dc686 dc693 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem dc701 : markedBudgetWith markRaw (fun mode => deepMemo (lz 0) (mz 0) (pL (edgeQ35.map fun _ => 16)) 12 dc694 mode 12) [ea35] edgeQ35 0 12 2 0 1 = false := by decide +kernel
lemma dc702 : ∀ x ∈ dc694, dc686 x = false := dFord (dCat (dCat (dCat (dCat (dCat dc695 dc696) dc697) dc698) dc699) dc700)
theorem marked35t3 : markedChk markRaw [ea35] edgeQ35 0 12 2 0 1 = false := markedDeepRootJoin markRaw _ _ _ _ _ _ _ dc694 dc702 dc701
lemma N35 (base : Imp [] 0 13) (t : ℕ) (ha : 1 ≤ t) (hb : t ≤ 3) : Excluded 12 ea35 (remT (unaryE ea35) t) := by
  interval_cases t
  · exact unaryMarked (x:=5) (t:=0) (by decide +kernel) (by decide +kernel) ready35.1 base ready35.2.1 ready35.2.2 (binaryDone base 1 (by decide) (by decide)) marked35t1
  · exact unaryMarked (x:=5) (t:=1) (by decide +kernel) (by decide +kernel) ready35.1 base ready35.2.1 ready35.2.2 (binaryDone base 2 (by decide) (by decide)) marked35t2
  · exact unaryMarked (x:=5) (t:=2) (by decide +kernel) (by decide +kernel) ready35.1 base ready35.2.1 ready35.2.2 (binaryDone base 3 (by decide) (by decide)) marked35t3
lemma upperCases (base : Imp [] 0 13) {t : ℕ} (ha : 1 ≤ t) (hb : t ≤ 3) : ∀ e ∈ six, Excluded 12 e (remT (unaryE e) t) := by
  intro p hp
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N0 base t ha hb
  · exact mirror1 _ _ (N6 base t ha hb)
  · exact mirror2 _ _ (N5 base t ha hb)
  · exact N3 base t ha hb
  · exact N4 base t ha hb
  · exact N5 base t ha hb
  · exact N6 base t ha hb
  · exact mirror7 _ _ (N3 base t ha hb)
  · exact mirror8 _ _ (N4 base t ha hb)
  · exact N9 base t ha hb
  · exact mirror10 _ _ (N12 base t ha hb)
  · exact mirror11 _ _ (N13 base t ha hb)
  · exact N12 base t ha hb
  · exact N13 base t ha hb
  · exact N14 base t ha hb
  · exact N15 base t ha hb
  · exact mirror16 _ _ (N21 base t ha hb)
  · exact mirror17 _ _ (N20 base t ha hb)
  · exact mirror18 _ _ (N22 base t ha hb)
  · exact mirror19 _ _ (N23 base t ha hb)
  · exact N20 base t ha hb
  · exact N21 base t ha hb
  · exact N22 base t ha hb
  · exact N23 base t ha hb
  · exact N24 base t ha hb
  · exact N25 base t ha hb
  · exact mirror26 _ _ (N28 base t ha hb)
  · exact mirror27 _ _ (N25 base t ha hb)
  · exact N28 base t ha hb
  · exact N29 base t ha hb
  · exact mirror30 _ _ (N31 base t ha hb)
  · exact N31 base t ha hb
  · exact N32 base t ha hb
  · exact mirror33 _ _ (N32 base t ha hb)
  · exact N34 base t ha hb
  · exact N35 base t ha hb
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
set_option maxRecDepth 100000 in
theorem leaf461 : chk [] rStrong 0 13 4 0x0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf462 : chk [] rStrong 0 13 4 0x40c20000200200401000001a2000820000000020040000202101 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf463 : chk [] rStrong 0 13 4 0x1000004800080600408008004008080400002800808040004010 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf464 : chk [] rStrong 0 13 4 0x4000000a002010000000100001000240128148006080100000004 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf465 : chk [] rStrong 0 13 4 0x800080080144000000400400010011010000000404022040602 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf466 : chk [] rStrong 0 13 4 0x1004000010484000000020602500c0108000800080000000010020 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf467 : chk [] rStrong 0 13 4 0x240010008002000003808023000000280011000000180080 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf468 : chk [] rStrong 0 13 4 0x8008800400200810200004000004004001020500002600400000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf469 : chk [] rStrong 0 13 4 0x12000400000803001060000000200400000401200200888800000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf470 : chk [] rStrong 0 13 4 0x80030110000000000801800000400002804010048010000009040 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf471 : chk [] rStrong 0 13 4 0x20204020105000100000290000900000282004000000010000008 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf472 : chk [] rStrong 0 13 4 0x2001010002000000ac094000000000000040000000121005020800 0 = false := by decide +kernel
lemma rootRun4 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 4 p.1 p.2 = false := by
  refine ⟨_, ?_, addMask (f:=chk [] rStrong 0 13 4) leaf461 (addMask leaf462 (addMask leaf463 (addMask leaf464 (addMask leaf465 (addMask leaf466 (addMask leaf467 (addMask leaf468 (addMask leaf469 (addMask leaf470 (addMask leaf471 (addMask leaf472 endMasks)))))))))))⟩
  decide +kernel
set_option maxRecDepth 100000 in
theorem leaf473 : chk [] rStrong 0 13 5 FF 1 = false := by decide +kernel
lemma rootRun5 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 5 p.1 p.2 = false := by
  exact one leaf473
set_option maxRecDepth 100000 in
theorem leaf474 : chk [] rStrong 0 13 6 FF 1 = false := by decide +kernel
lemma rootRun6 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 6 p.1 p.2 = false := by
  exact one leaf474
set_option maxRecDepth 100000 in
theorem leaf475 : chk [] rStrong 0 13 7 FF 1 = false := by decide +kernel
lemma rootRun7 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 7 p.1 p.2 = false := by
  exact one leaf475
set_option maxRecDepth 100000 in
theorem leaf476 : chk [] rStrong 0 13 8 FF 1 = false := by decide +kernel
lemma rootRun8 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 8 p.1 p.2 = false := by
  exact one leaf476
set_option maxRecDepth 100000 in
theorem leaf477 : chk [] rStrong 0 13 9 FF 1 = false := by decide +kernel
lemma rootRun9 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 9 p.1 p.2 = false := by
  exact one leaf477
set_option maxRecDepth 100000 in
theorem leaf478 : chk [] rStrong 0 13 10 FF 1 = false := by decide +kernel
lemma rootRun10 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 10 p.1 p.2 = false := by
  exact one leaf478
set_option maxRecDepth 100000 in
theorem leaf479 : chk [] rStrong 0 13 11 FF 1 = false := by decide +kernel
lemma rootRun11 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 11 p.1 p.2 = false := by
  exact one leaf479
set_option maxRecDepth 100000 in
theorem leaf480 : chk [] rStrong 0 13 12 FF 1 = false := by decide +kernel
lemma rootRun12 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 12 p.1 p.2 = false := by
  exact one leaf480
set_option maxRecDepth 100000 in
theorem leaf481 : chk [] rStrong 0 13 13 FF 1 = false := by decide +kernel
lemma rootRun13 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rStrong 0 13 13 p.1 p.2 = false := by
  exact one leaf481
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
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1 && x 2 && x 3) || (x 0 && x 1 && x 4) || (x 0 && x 2 && x 4) || (x 1 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 1 && x 3 && x 4) || (x 1 && x 2 && x 5) || (x 0 && x 3 && x 5) || (x 2 && x 3 && x 4 && x 5)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 1 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 3 0 &&& rawP.getD 5 0) ||| (rawP.getD 2 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0)
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

def target : (Fin 6 → Bool) → Bool := fun x => Nat.testBit (4276677312 * 2 ^ 32 + 4008214528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem f_target : ∀ x : Fin 6 → Bool, f x = target x := by
  decide +kernel

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [5, 17]⟩, ⟨.and, [16, 18]⟩], 19⟩

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
end PEqualNP.Outside.L_meta_48075

theorem PEqualNP.Outside.L_meta_48075 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677312 * 2 ^ 32 + 4008214528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677312 * 2 ^ 32 + 4008214528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_48075.solve
