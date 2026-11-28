import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32950
def bigNat_0 : Nat := 0x1fffff7ffffdf7ffffbefbffffef7ffffbef77ffffbdf7bffffdefb7ffffbdf77ddefffdfeb55ffd6d6aabffab7ff5affedffdb555ad5ffd6dab7ff6ffed5aadaabffaffeffed6adaffeffedb7ff0000000000000000
def bigNat_1 : Nat := 0x2014aa0029295540054800a500120024aaa52a002925480090012a55255400500100129525001001248000000000000000000
def bigNat_2 : Nat := 0x2000008000020800004104000010800004108800004208400002104800004208822100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0xfffff80000000000000000000000000001ffffe07c1f07800008801042000000084001090822104600002010820028c211842000000221088420430008284204312421800000000000000010220b40182c141105820b0ed160410258211410158410a0809c2094549b81f07c1e082dfe004000000800000000042000dffc004180400001a3000600004080288002000ffe10a1a000ffedb7ff3e6bebd3c425fb35
def bigNat_4 : Nat := 0x1fffff00000000000000000000000000000000000fffff03e1ffffef001f7000002180420600080240c8c8296106320c0000000206410a0830907000082284189071061089090710630c8500000000000000001040546d515004022a0412001a814014a04224012a0821242d680f8445ad3c007dc00151fe010000006008002300058000c00001040000010c280006ffe102218a0002ffe000c62c2ffe000c30002f0e0c6fab5e5d7e
def bigNat_5 : Nat := 0x1ffffe07c0fffff7801ffffef7dc00000000380000e00008802ca0069280f001c0000084016480a407800e1020902a03c00e00e340b60160163600d00000000000000001084a0406280242450082210640242290084452acc01f0253649e00466c93df700001281fe00000001022000280005affe00000410210001602b7ff0000c182c0abff8000000d02d8000000d8000f3bf6d885c72ab04
def bigNat_6 : Nat := 0x1ffffe03e0000001ffffe03c1ffffef000fffff7bec00000000000000001721009c4100a0168a42f0005c00b861500b01345b4004e009c3500b6802b00ac0ac35a000b40b42485e0000000000000000110801418004464f0080fa208020548e080f05488cbc0026244defb48001801004022005fe8400010c0280002b7ff00000000185402c00016d800000000d402da00000000000d6800000000db7ff668d6478fc4b0c9b
def bigNat_7 : Nat := 0x1ffffef801ffffef7de0000000000000000000000000060000184800a8070000c0001800302400094038000000c0018356a00000a00280282522403803800018000000000000000012110646041884888310424300c458ce33e0058c8f3df7a840700105080e042008444419fe0000016002abff80000000000001b0002d5ffc00000000000d5a80000000000000d6adaffeffe00000d5e71747afa9fdbc
def bigNat_8 : Nat := 0x7ffffc0000001ffffef800000001ffffefbdc0000000000000000000000000000000000542c04905b520094001280025004a06d5540052000001480290254a2480ac02b02b0000002a02a00015000000000000000001be0384800e0060f1c3e02040700508fc3ef7400f00040200780420400f00841108800e1feb000016d68000000000000000001b55580000000000000000d5aadaabffaffeffe0000000000000000aca3d608f772dff2
def bigNat_9 : Nat := 0x1ffffefbefffffbc0000000000000000000000000000000000000000000182510e000000018000300006000c049556211c0126087010e0000000003000c00c0000000c00c00006000000000000000001c01c0700701070fe03efb87f80f60f00100060f00108230780084060f00108221008701feb55ffc0000000000000000000001b555ad5ffd6dab7ff6ffe0000000000000000000000000000000005ff6feb736c766ca
def bigNat_10 : Nat := 0x7ffffdfffff7c000000000000000000000000000000000000000000000000000000000060084700125a02e0009c004380270000000006000000180030000000000c00300300000003003000018000000000000000001ffe007ff801f7f0002083f800087f00020807f00021043f80010827f00021044010f801feb55ffd6d6aabffab7ff5affedffc000000000000000000000000000000000000000000000000000000fe589dfdff9ecaef
def bigNat_11 : Nat := 0x1fffff7ffffdf7ffffbefbffffef7ffffbef77ffffbdf7bffffdefb7ffffbdf77ddefffdfeb55ffd6d6aabffab7ff5affedffdb555ad5ffd6dab7ff6ffed5aadaabffaffeffed6adaffeffedb7ffffffffffffffffff
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
def NN : Nat := 686
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
def segsX : List (ℕ × ℕ) := [(63, 75), (75, 78), (78, 81), (81, 84), (84, 96), (96, 108), (108, 110), (110, 113), (113, 116), (116, 118), (118, 120), (120, 123), (123, 125), (125, 128), (128, 140), (140, 152), (152, 154), (154, 166), (166, 168), (168, 170), (170, 172), (172, 174), (174, 177), (177, 180), (180, 182), (182, 184), (184, 186), (186, 189), (189, 191), (191, 193), (193, 196), (196, 208), (208, 211), (211, 223), (223, 226), (226, 228), (228, 230), (230, 233), (233, 236), (236, 239), (239, 241), (241, 253), (253, 255), (255, 257), (257, 260), (260, 262), (262, 265), (265, 267), (267, 269), (269, 271), (271, 273), (273, 275), (275, 278), (278, 281), (281, 293), (293, 296), (296, 308), (308, 310), (310, 313), (313, 315), (315, 327), (327, 330), (330, 332), (332, 334), (334, 346), (346, 348), (348, 350), (350, 352), (352, 354), (354, 356), (356, 359), (359, 361), (361, 364), (364, 367), (367, 369), (369, 381), (381, 383), (383, 385), (385, 387), (387, 390), (390, 392), (392, 401)]
def segsY : List (ℕ × ℕ) := [(401, 416), (416, 421), (421, 425), (425, 431), (431, 435), (435, 441), (441, 446), (446, 467), (467, 470), (470, 476), (476, 481), (481, 502), (502, 507), (507, 513), (513, 518), (518, 539), (539, 543), (543, 548), (548, 554), (554, 575), (575, 580), (580, 602), (602, 608), (608, 614), (614, 635), (635, 641), (641, 663), (663, 685)]
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
  have : Std.Symm (fun a c : L_meta_32950.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
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
    {go : (L_meta_32950.X → L_meta_32950.X → Bool) → List L_meta_32950.X → Bool}
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
        have : a.s = c.s := congrArg L_meta_32950.X.s e
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_32950.X → L_meta_32950.X → Bool) → List L_meta_32950.X → Bool,
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32950.X.s e))
end sound
def rawP : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8, bigNat_9, bigNat_10]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := bigNat_11
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
def MM : ℕ := 201
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
    have : Std.Symm (fun a b : L_meta_32950.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32950.X.s e)) hpb
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
def acc0 : List (ℕ × ℕ) := []
def c0 : List (ℕ × ℕ) := [(224, 4)]
def acc1 : List (ℕ × ℕ) := c0 ++ acc0
def c1 : List (ℕ × ℕ) := [(88, 5), (152, 5), (104, 6), (168, 6), (200, 5), (112, 5), (176, 4), (208, 5)]
def acc2 : List (ℕ × ℕ) := c1 ++ acc1
def c2 : List (ℕ × ℕ) := [(140, 6), (52, 7), (84, 7), (148, 5), (100, 7), (164, 7), (196, 5), (56, 6)]
def acc3 : List (ℕ × ℕ) := c2 ++ acc2
def c3 : List (ℕ × ℕ) := [(82, 6), (146, 5), (98, 6), (162, 5), (194, 5), (28, 7), (44, 7), (76, 6)]
def acc4 : List (ℕ × ℕ) := c3 ++ acc3
def c4 : List (ℕ × ℕ) := [(50, 8)]
def acc5 : List (ℕ × ℕ) := c4 ++ acc4
def c5 : List (ℕ × ℕ) := [(70, 6), (134, 5), (26, 6), (42, 7), (74, 6), (138, 7)]
def acc6 : List (ℕ × ℕ) := c5 ++ acc5
def c6 : List (ℕ × ℕ) := [(81, 5), (145, 3), (97, 5), (161, 5), (193, 4), (14, 7), (22, 6), (38, 7)]
def acc7 : List (ℕ × ℕ) := c6 ++ acc6
def c7 : List (ℕ × ℕ) := [(37, 7), (69, 5), (133, 5), (25, 6), (41, 7), (73, 7), (137, 6), (49, 6)]
def acc8 : List (ℕ × ℕ) := c7 ++ acc7
def c8 : List (ℕ × ℕ) := [(7, 5), (11, 7), (19, 6), (35, 6), (67, 5), (131, 4), (13, 7), (21, 5)]
def acc9 : List (ℕ × ℕ) := c8 ++ acc8
def c9 : List (ℕ × ℕ) := [(192, 7)]
def acc10 : List (ℕ × ℕ) := c9 ++ acc9
def c10 : List (ℕ × ℕ) := [(160, 8)]
def acc11 : List (ℕ × ℕ) := c10 ++ acc10
def c11 : List (ℕ × ℕ) := [(96, 8)]
def acc12 : List (ℕ × ℕ) := c11 ++ acc11
def c12 : List (ℕ × ℕ) := [(144, 6)]
def acc13 : List (ℕ × ℕ) := c12 ++ acc12
def c13 : List (ℕ × ℕ) := [(80, 8)]
def acc14 : List (ℕ × ℕ) := c13 ++ acc13
def c14 : List (ℕ × ℕ) := [(48, 9)]
def acc15 : List (ℕ × ℕ) := c14 ++ acc14
def c15 : List (ℕ × ℕ) := [(136, 9)]
def acc16 : List (ℕ × ℕ) := c15 ++ acc15
def c16 : List (ℕ × ℕ) := [(72, 9)]
def acc17 : List (ℕ × ℕ) := c16 ++ acc16
def c17 : List (ℕ × ℕ) := [(40, 9)]
def acc18 : List (ℕ × ℕ) := c17 ++ acc17
def c18 : List (ℕ × ℕ) := [(24, 9)]
def acc19 : List (ℕ × ℕ) := c18 ++ acc18
def c19 : List (ℕ × ℕ) := [(132, 8)]
def acc20 : List (ℕ × ℕ) := c19 ++ acc19
def c20 : List (ℕ × ℕ) := [(68, 9)]
def acc21 : List (ℕ × ℕ) := c20 ++ acc20
def c21 : List (ℕ × ℕ) := [(36, 10)]
def acc22 : List (ℕ × ℕ) := c21 ++ acc21
def c22 : List (ℕ × ℕ) := [(20, 9)]
def acc23 : List (ℕ × ℕ) := c22 ++ acc22
def c23 : List (ℕ × ℕ) := [(12, 10)]
def acc24 : List (ℕ × ℕ) := c23 ++ acc23
def c24 : List (ℕ × ℕ) := [(130, 8)]
def acc25 : List (ℕ × ℕ) := c24 ++ acc24
def c25 : List (ℕ × ℕ) := [(66, 7)]
def acc26 : List (ℕ × ℕ) := c25 ++ acc25
def c26 : List (ℕ × ℕ) := [(34, 10)]
def acc27 : List (ℕ × ℕ) := c26 ++ acc26
def c27 : List (ℕ × ℕ) := [(18, 9)]
def acc28 : List (ℕ × ℕ) := c27 ++ acc27
def c28 : List (ℕ × ℕ) := [(10, 10)]
def acc29 : List (ℕ × ℕ) := c28 ++ acc28
def c29 : List (ℕ × ℕ) := [(6, 9)]
def acc30 : List (ℕ × ℕ) := c29 ++ acc29
def c30 : List (ℕ × ℕ) := [(65, 8)]
def acc31 : List (ℕ × ℕ) := c30 ++ acc30
def c31 : List (ℕ × ℕ) := [(33, 9)]
def acc32 : List (ℕ × ℕ) := c31 ++ acc31
def c32 : List (ℕ × ℕ) := [(17, 7)]
def acc33 : List (ℕ × ℕ) := c32 ++ acc32
def c33 : List (ℕ × ℕ) := [(9, 10)]
def acc34 : List (ℕ × ℕ) := c33 ++ acc33
def c34 : List (ℕ × ℕ) := [(5, 8)]
def acc35 : List (ℕ × ℕ) := c34 ++ acc34
def c35 : List (ℕ × ℕ) := [(3, 8)]
def acc36 : List (ℕ × ℕ) := c35 ++ acc35
def c36 : List (ℕ × ℕ) := [(128, 10)]
def acc37 : List (ℕ × ℕ) := c36 ++ acc36
def c37 : List (ℕ × ℕ) := [(64, 10)]
def acc38 : List (ℕ × ℕ) := c37 ++ acc37
def c38 : List (ℕ × ℕ) := [(32, 12)]
def acc39 : List (ℕ × ℕ) := c38 ++ acc38
def c39 : List (ℕ × ℕ) := [(16, 11)]
def acc40 : List (ℕ × ℕ) := c39 ++ acc39
def c40 : List (ℕ × ℕ) := [(8, 12)]
def acc41 : List (ℕ × ℕ) := c40 ++ acc40
def c41 : List (ℕ × ℕ) := [(4, 12)]
def acc42 : List (ℕ × ℕ) := c41 ++ acc41
def c42 : List (ℕ × ℕ) := [(2, 11)]
def acc43 : List (ℕ × ℕ) := c42 ++ acc42
def c43 : List (ℕ × ℕ) := [(1, 11)]
def acc44 : List (ℕ × ℕ) := c43 ++ acc43
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def rt : List (ℕ × ℕ) := acc44


namespace Memo
noncomputable section

structure Key where
  k : Nat
  t : Nat
  z : Nat
  v : List W

def sameWire (a b : W) : Bool :=
  decide (a.s = b.s) && decide (a.a = b.a) && decide (a.b = b.b) &&
    decide (a.c = b.c) && decide (a.r = b.r)

theorem sameWire_iff (a b : W) : sameWire a b = true ↔ a = b := by
  cases a
  cases b
  simp [sameWire, Bool.and_eq_true, and_assoc]

def sameList : List W → List W → Bool
  | [], [] => true
  | a :: v, b :: u => sameWire a b && sameList v u
  | _, _ => false

theorem sameList_iff (v u : List W) : sameList v u = true ↔ v = u := by
  induction v generalizing u with
  | nil => cases u <;> simp [sameList]
  | cons a v ih => cases u <;> simp [sameList, Bool.and_eq_true, sameWire_iff, ih]

def Key.same (a b : Key) : Bool :=
  decide (a.k = b.k) && decide (a.t = b.t) && decide (a.z = b.z) && sameList a.v b.v

theorem Key.same_iff (a b : Key) : a.same b = true ↔ a = b := by
  cases a
  cases b
  simp [Key.same, Bool.and_eq_true, sameList_iff, and_assoc]

def Key.digest (q : Key) : Nat :=
  let a := (q.v.head?.map W.s).getD 0
  let b := ((q.v.drop 1).head?.map W.s).getD 0
  q.z % 65521 + a % 65521 + 7 * (b % 65521) + 13 * q.t

inductive Tree where
  | empty
  | leaf (decode : Nat → Key) (codes : List Nat)
  | fork (left right : Tree)

def wb (d : Bool) (a b : W) : W :=
  if d then ⟨a.s ||| b.s, a.a &&& b.a, a.b ||| b.b, (a.a &&& b.a) ||| (a.b ||| b.b), 0⟩
  else ⟨a.s &&& b.s, a.a ||| b.a, a.b &&& b.b, (a.a ||| b.a) ||| (a.b &&& b.b), 0⟩

def wn (m : Nat) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩

abbrev Replay := Nat × List W

def replayGate (mask code : Nat) (r : Replay) : Replay :=
  let a := r.2.getD ((code / 4) % 16) ⟨0,0,0,0,0⟩
  let ka := code.testBit 10
  if code % 4 = 2 then
    let w := wn mask a
    let v := if ka then r.2 else r.2.filter fun p => p.s != a.s
    (r.1 - a.c - (if ka then a.c else 0), addS w v)
  else
    let b := r.2.getD ((code / 64) % 16) ⟨0,0,0,0,0⟩
    let kb := code.testBit 11
    let w := wb (code.testBit 0) a b
    let v := r.2.filter fun p => (ka || p.s != a.s) && (kb || p.s != b.s)
    (r.1 + (a.c &&& b.c) - w.c - (if ka then a.c else 0) - (if kb then b.c else 0), addS w v)

def replay (mask : Nat) : Nat → Nat → Replay → Replay
  | 0, _, r => r
  | n+1, x, r => replay mask n (x / 4096) (replayGate mask (x % 4096) r)

def traceKey (K mask : Nat) (r : Replay) (x : Nat) : Key :=
  let n := x % 8
  let v := replay mask n (x / 64) r
  ⟨K - n, (x / 8) % 8, v.1, v.2⟩

def fromTrace (K mask : Nat) (r : Replay) (codes : List Nat) : Tree :=
  .leaf (traceKey K mask r) codes

def Tree.query (q : Key) : Tree → Nat → Bool
  | .empty, _ => false
  | .leaf decode codes, h => codes.any fun x =>
    decide (x % 16 = h % 16) && q.same (decode (x / 16))
  | .fork l r, h => if h % 2 = 0 then l.query q (h / 2) else r.query q (h / 2)

def Tree.all (p : Key → Bool) : Tree → Bool
  | .empty => true
  | .leaf decode codes => codes.all fun x => p (decode (x / 16))
  | .fork l r => l.all p && r.all p

theorem Tree.fork_all (p : Key → Bool) {l r : Tree} (hl : l.all p = true)
    (hr : r.all p = true) : (Tree.fork l r).all p = true := by
  simp [Tree.all, hl, hr]

theorem Tree.query_sound {p : Key → Bool} {q : Key} (tree : Tree)
    (h : tree.all p = true) : ∀ n, tree.query q n = true → p q = true := by
  induction tree with
  | empty => simp [Tree.query]
  | leaf decode codes =>
    intro n hn
    obtain ⟨x, hx, hpair⟩ := List.any_eq_true.mp hn
    have both : x % 16 = n % 16 ∧ q.same (decode (x / 16)) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hpair
    rw [(Key.same_iff q _).mp both.2]
    exact List.all_eq_true.mp h x hx
  | fork l r il ir =>
    have hand : l.all p = true ∧ r.all p = true := by
      simpa only [Tree.all, Bool.and_eq_true] using h
    obtain ⟨hl, hr⟩ := hand
    intro n hn
    simp only [Tree.query] at hn
    split at hn
    · exact il hl _ hn
    · exact ir hr _ hn

def Tree.guard (tree : Tree) (q : Key) (otherwise : Unit → Bool) : Bool :=
  if tree.query q q.digest then false else otherwise ()

theorem Tree.guard_eq (tree : Tree) (p : Key → Bool)
    (h : tree.all (fun q => !p q) = true) (q : Key) :
    tree.guard q (fun _ => p q) = p q := by
  unfold Tree.guard
  split
  next hg =>
    have hn := tree.query_sound h q.digest hg
    change (!(p q)) = true at hn
    cases hq : p q <;> simp_all
  next => rfl

abbrev Tables := Nat → Tree
abbrev F := Nat → Nat → Nat → List W → Bool

def baseF : F := fun _ _ _ _ => true

def normalStep (l m g : Nat) (ih : F) : F := fun k t z v =>
  Bool.rec (motive := fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y))
    true (Nat.ble v.length 1)

def rawStep (l m g : Nat) (normal ih : F) : F := fun k t z v =>
  Bool.rec (motive := fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv normal l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
          v.length z v pairsS))) true (Nat.ble v.length 1)

def call (f : F) (q : Key) : Bool := f q.k q.t q.z q.v

def cache (tree : Tree) (f : F) : F := fun k t z v =>
  tree.guard ⟨k,t,z,v⟩ fun _ => f k t z v

theorem cache_eq (tr : Tree) (f : F) (hc : tr.all (fun q => !call f q) = true) :
    cache tr f = f := by
  funext k t z v
  exact tr.guard_eq (call f) hc ⟨k,t,z,v⟩

def run (ts : Tables) (step : F → F) : Nat → F
  | 0 => baseF
  | n+1 => cache (ts (n+1)) (step (run ts step n))

def Cert (ts : Tables) (step : F → F) : Prop :=
  ∀ n, (ts (n+1)).all (fun q => !call (step (run ts step n)) q) = true

theorem run_eq (ts : Tables) (step : F → F) (hc : Cert ts step) :
    ∀ n, run ts step n = Nat.rec baseF (fun _ f => step f) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change cache _ _ = step _
    rw [cache_eq _ _ (hc n), ih]

def normals (c : Tables) (l m g : Nat) : Nat → F := run c (normalStep l m g)

def raws (c d : Tables) (l m g K : Nat) : Nat → F :=
  run d (rawStep l m g (normals c l m g K))

theorem normals_eq (c : Tables) (l m g : Nat) (h : Cert c (normalStep l m g)) (n : Nat) :
    normals c l m g n = look l m g n := by
  exact run_eq c _ h n

theorem raws_eq (c d : Tables) (l m g K : Nat)
    (hc : Cert c (normalStep l m g)) (hd : Cert d (rawStep l m g (normals c l m g K))) (n : Nat) :
    raws c d l m g K n = look1 l m g K n := by
  unfold raws
  rw [run_eq _ _ hd n, normals_eq c l m g hc K] <;> rfl

def topF (c d : Tables) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (normals c l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (raws c d l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startF (c d : Tables) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topF c d l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def chkF (cs ds : Tables) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startF cs ds l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

theorem topF_eq (c d : Tables) (l m g K H ph k t z : Nat) (v : List W)
    (hc : Cert c (normalStep l m g)) (hd : Cert d (rawStep l m g (normals c l m g K))) :
    topF c d l m g K H ph k t z v = topC l m g K H ph k t z v := by
  simp only [topF, topC, normals_eq c l m g hc K, raws_eq c d l m g K hc hd K]

theorem startF_eq (c d : Tables) (l m g B K t p H ph : Nat) (v : List W)
    (hc : Cert c (normalStep l m g)) (hd : Cert d (rawStep l m g (normals c l m g K))) :
    startF c d l m g B K t p H ph v = startv l m g B K t p H ph v := by
  simp only [startF, startv, fun k t z v => topF_eq c d l m g K H ph k t z v hc hd]

theorem chkF_eq (cs ds : Tables) (E Q : List (Nat × Nat)) (Z K t H ph : Nat)
    (hc : Cert cs (normalStep (lz Z) (mz Z) (pL (Q.map fun _ => 16))))
    (hd : Cert ds (rawStep (lz Z) (mz Z) (pL (Q.map fun _ => 16))
      (normals cs (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K))) :
    chkF cs ds E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [chkF, chk, st_eq, fun B p r => startF_eq cs ds _ _ _ B K t p H ph r hc hd]

end
def digitList : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, x =>
    let w := 12 * ((x / 16) % 8 + 1)
    (x &&& ((1 <<< w) - 1)) :: digitList n (x >>> w)

namespace FixedStart
def ls : Nat := 0x1fffff7ffffdf7ffffbefbffffef7ffffbef77ffffbdf7bffffdefb7ffffbdf77ddefffdfeb55ffd6d6aabffab7ff5affedffdb555ad5ffd6dab7ff6ffed5aadaabffaffeffed6adaffeffedb7ff0000000000000000
def ms : Nat := 0x7ffffdfffff7dffffefbefffffbdffffefbddffffef7defffff7bedffffef7ddf77bfff7fad57ff5b5aaaffeadffd6bffb7ff6d556b57ff5b6adffdbffb56ab6aaffebffbffb5ab6bffbffb6dffc0000000000000001fffff7ffffdf7ffffbefbffffef7ffffbef77ffffbdf7bffffdefb7ffffbdf77ddefffdfeb55ffd6d6aabffab7ff5affedffdb555ad5ffd6dab7ff6ffed5aadaabffaffeffed6adaffeffedb7ffffffffffffffffff
def gs : Nat := 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
private def wire (s a : Nat) : W := ⟨s,a,0,a,3⟩
def iv : List W := [wire bigNat_10 0x42100420080010802000400004200800100001000000840100020000200000100000004200800100001000000800000000000000800000000,wire bigNat_8 0x40108021000200840008001000210002000400004000042000400080000800000400000210002000400004000002000001000000002000000,wire bigNat_4 0x4210842108421084210000000000000000000108421080000000000000000000842108400000010000000020,wire bigNat_9 0x42008401004010040100020004010040008000080000802008001000010000008000004010040008000080000040000020000000040000000,wire bigNat_6 0x421084200000000421080000000108420000010000000021084000002000001000000000108420000010000008000004000000008000,wire bigNat_3 0x842108421084210842108421080000000000000000000000000021084210000000001,wire bigNat_7 0x2108000084200002108000080000842000020000200000108400004000040000020000000842000020000200000100000080000000100000,wire bigNat_5 0x10842108421080000000000001084210000000000000210842000000080000000000001084210000000400000200000000400]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eqL : lz 0 = ls := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eqM : mz 0 = ms := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eqG : pL (rt.map fun _ => 16) = gs := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eqV : avl (PZ rt) ms rawP = iv := (sameList_iff _ _).mp (by decide +kernel)
noncomputable def ready (c d : Tables) (B K t H ph : Nat) :=
  anySub (pos t) ls iv 0 (fun v => startF c d ls ms gs B K t 0 H ph v)
theorem prepared (c d : Tables) (B K t H ph : Nat)
    (hb : pL (rt.map fun e => 16 + (K - e.2)) = B) :
    chkF c d [] rt 0 K t H ph = ready c d B K t H ph := by
  simp only [chkF,frc_eq,st_eq,eqL,eqM,eqG,hb,rawL,List.map_nil,List.append_nil,eqV] <;> rfl
end FixedStart

namespace D13
noncomputable section
open FixedStart (ls ms gs iv eqL eqM eqG)
def ns := normalStep ls ms gs
private def budget : Nat := 0x6719c62f7c62f8b5b16b5ef6b6317c5eb6bdaf8bdaf6ce31ac5ef6b5f18b62d9c5ef6c5ab5bd694a5295a4e93ada749d2b4b4eb59ce328c652
def iz : Nat := 0x5ab6ad694ad6959ceb39d2939d6b4ad253a4e95a4e93b56b7ad2939d2b59d676ad293ad273ace5294a53946519d2328ca72a467394a1184231
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem eqB : pL (rt.map fun e => 16 + (13 - e.2)) = budget := by decide +kernel
def a (n x : Nat) := fromTrace 13 ms (iz,iv) (digitList n x)
def j0 : Tree := (a 6 0x7444970536544607363970536544926444860335344807545974036044325654646873004f264448640320444)
def j1 : Tree := (.fork (.fork (a 15 0x36506400b304c2264454400b504402756587300b626570466443924570466443c28470375343d23070375343527266273243027074076043325173076043e27074047576044325173047576044e264448730035262628730033270660720435) (a 11 0x73503400b604c10787404307300c70687404307300c723070466443127470376343528472375343227073076043c27073047576044c08451476476044327066073043b260640720432)) (a 16 0x2644487300b00787504307300c20687504307300c226373466443426272466443c26070466443e24572466443224272466443224070466443b250730760434065515675750446275658730035272628730033074449765730045075658664730045270640720435))
def j2 : Tree := (.fork (.fork (.fork (.fork (a 17 0x3030038008bb27256475243407277673243426267573243407257667573244427456475243426267473243406277673243426267373243426247467373244427374376043a08358774376044a27348674376044a27348574376044a07076472043307456467175044a284764730437) (a 8 0x2407204a308077472043c27064372043c07067464372044c26073042f28174172043308168574172044307466467173044b)) (a 11 0x27066372043f06077672043a28176172043a27177172043c08158777172044c27148677172044c26067173043007057667173044026047567173044026047467173044025076472043e)) (.fork (a 18 0x41049008b92737534ab2727524a92707204aa2607204a728476473243a07077673043526067573043507057667573044526067473043504076472043125177172043c25148677172044c06158577172044c08476467173044927174172043e273643720431270641720430) (a 10 0x1031038008b02727324a226273242127075042a27073042907067575043a27456475043806077673043527466473043b273663720437))) (.fork (a 21 0x410490083f2607304a127375342327275242f27273242227072042108476476043b27056475043627066473043107067656475044626072042b26167172043e07157667172044e26147567172044e240675720437050774720437283763730434240673720437050574673720447271641720433071674641720443) (a 21 0x2040049008b32627324a62707504a82707304a60706757504b807077672043726067572043707057667572044726067372043727077173043b27048677173044b27048577173044b24072042a04077472043228176173043508168676173044524167172043d24147567172044d05157467172044d263643720433270741720435)))
def j3 : Tree := (a 1 0x76675664641720452)
def j4 : Tree := (.fork (a 21 0x7556467375244008768676473244908757576376044007656467175044007556467175044007667566473044f07666467173044c07566467173044c08576467173044508568276173044907667566372044f07666367172044f07566367172044f075643671720445074643671720445176675641720449276664641720449275664641720449264643641720449264673641720449064663641720440) (.fork (a 14 0x765646717504cb0755646717504cb0766646717304c10756646717304c1276475763730444085684763730444075684763730444087686764720440085764673720440176675643720440086674771720442086654771720445086764671720448085764671720448) (a 9 0x8757577175044208667577173044808776367173044a08576367173044a07576367173044a086682741720447085682741720447075672741720444074673641720446)))
def j5 : Tree := (.fork (.fork (.fork (.fork (a 19 0x766757504b50867717204b508576476243427656475243427556475243417467375243416467375243417667573243418774376043a18576376043a17576376043a17467175043a16467175043a287764730437286764730437285764730437075761730436264641720436263641720436) (a 6 0x2534307300be08777175043c08677175043c37556475043517667173043b26467173043b)) (a 8 0x757637304b50756717204b617467373243118574376043d086771730435174671730430085771730435243641720435)) (.fork (.fork (a 14 0x185764762435287764732435286764732435285764732435364673732435287761730431286761730431285761730431282761730431287761720432376641720431286761720432364641720437284761720432) (a 16 0x766757534b50766757524b40877647604bb0877637604ba0867647604bb0867637604ba0857647604bb0766717504ba0756717504ba08577373043136467173043c275643720430174673720430274643720430174671720432243671720432)) (a 18 0x746737324b20867437604be0857437604be0756717304b10746717304b127656475043827556475043817667573043b27666473043b27566473043b17667572043727666372043717667172043b27566372043728674172043028574172043028474172043026367172043b))) (.fork (.fork (.fork (a 17 0x1746717304b928776373043528676373043507567173043828576373043507467173043817576373043b27574373043b27577373043528476373043528776472043437664372043428676472043428576472043436467372043436464372043a364671720436) (a 10 0x867717304bb0857717304bb074673732430086743760436085743760436185773750433175773750433175743750439187771720438274771720438)) (a 20 0x857647624b91766757324b90877717504ba1746717504b51646717504b51766717304b82646717304b80757617304bd2646417204bd07667575343907667575243708776476043508776376043308676476043508676376043308576476043507667175043307567175043318577172043a25477172043a)) (.fork (.fork (a 10 0x2765647504b52755647504b507667575043418777173043e17576173043627577173043e086771720434175761720437254761720437272741720435) (a 17 0x756717305390746717305391766757304b62766647304b62756647304b61766757204b41766717204b618577175043c17577175043c36367173043a16566473003027564172043d27464172043d27574172043827364172043d27474172043828276172043b)) (a 10 0x766717505360857737304b43544307300b318576476043718577173043507576373043307567172043416466372043125474172043a282741720433))))
def j6 : Tree := (.fork (.fork (a 14 0x1747605222767504aa3657300a32757504aa3437304af3717204aa37673242837475242836476242836473242424372042b37175042936173042c36172042e) (a 21 0x16566452c1767605282757304a62757204a23747534ad2747304a63647304a73647204a32737204a23637304a53437504a22717204a607576042c26473002a37473242116475042226473042535273002926372042137173042534172042a)) (.fork (a 14 0x2767534ab2767524a92757534ab2757524a92747534ab3647604a72737524a93637604a52717504a5165664429176760425374730425374720421373730423) (a 17 0x7576052f1647505252647305282757324a21747624a22747324a22737324a23437604ae2717304a10307300a62417204a637673042b37672042717476042e374750428164752421373750426)))
def j7 : Tree := (.fork (a 16 0x2757305282747305280757604ae2647300ac1647504a42647304a72637204a33717304a73417204ac27573242117476242127473242127373242134376042d271730420241720425) (a 17 0x27675052b3767324a93647624a93647324a52437204ac3717504aa3617304ad3617204af276753429276752427275753429275752427274753429364760425273752427363760423271750423))
def j8 : Tree := (.fork (a 13 0x2717305230307301283767304ad3767204a91747604a03747504aa1647524a33737504a827675042836573002127575042834373042d371720428) (a 19 0x27675352c27575352c27475352c2717505261656644aa1767604a63747304a63737304a427573042427572042037475342b274730424364730425364720421362730028273720420363730423343750420271720424))
def j9 : Tree := (.fork j7 j8)
def j10 : Tree := (.fork j6 j9)
def c : Tables
  | 11 => j0
  | 12 => j1
  | 13 => j2
  | _ => .empty
def d : Tables
  | 9 => j3
  | 10 => j4
  | 11 => j5
  | 12 => j10
  | _ => .empty
def rs := rawStep ls ms gs (normals c ls ms gs 13)
def p0_11 (q : Key) := !call (ns (run c ns 10)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj0 : j0.all p0_11 = true := by decide +kernel
def p0_12 (q : Key) := !call (ns (run c ns 11)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj1 : j1.all p0_12 = true := by decide +kernel
def p0_13 (q : Key) := !call (ns (run c ns 12)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj2 : j2.all p0_13 = true := by decide +kernel
def p1_9 (q : Key) := !call (rs (run d rs 8)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj3 : j3.all p1_9 = true := by decide +kernel
def p1_10 (q : Key) := !call (rs (run d rs 9)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj4 : j4.all p1_10 = true := by decide +kernel
def p1_11 (q : Key) := !call (rs (run d rs 10)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj5 : j5.all p1_11 = true := by decide +kernel
def p1_12 (q : Key) := !call (rs (run d rs 11)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj6 : j6.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj7 : j7.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj8 : j8.all p1_12 = true := by decide +kernel
theorem hj9 : j9.all p1_12 = true := Tree.fork_all _ hj7 hj8
theorem hj10 : j10.all p1_12 = true := Tree.fork_all _ hj6 hj9
theorem hc : Cert c ns := by
  intro n
  cases n with
  | zero => exact rfl
  | succ n =>
    cases n with
    | zero => exact rfl
    | succ n =>
      cases n with
      | zero => exact rfl
      | succ n =>
        cases n with
        | zero => exact rfl
        | succ n =>
          cases n with
          | zero => exact rfl
          | succ n =>
            cases n with
            | zero => exact rfl
            | succ n =>
              cases n with
              | zero => exact rfl
              | succ n =>
                cases n with
                | zero => exact rfl
                | succ n =>
                  cases n with
                  | zero => exact rfl
                  | succ n =>
                    cases n with
                    | zero => exact rfl
                    | succ n =>
                      cases n with
                      | zero => exact hj0
                      | succ n =>
                        cases n with
                        | zero => exact hj1
                        | succ n =>
                          cases n with
                          | zero => exact hj2
                          | succ n =>
                            rfl
theorem hd : Cert d rs := by
  intro n
  cases n with
  | zero => exact rfl
  | succ n =>
    cases n with
    | zero => exact rfl
    | succ n =>
      cases n with
      | zero => exact rfl
      | succ n =>
        cases n with
        | zero => exact rfl
        | succ n =>
          cases n with
          | zero => exact rfl
          | succ n =>
            cases n with
            | zero => exact rfl
            | succ n =>
              cases n with
              | zero => exact rfl
              | succ n =>
                cases n with
                | zero => exact rfl
                | succ n =>
                  cases n with
                  | zero => exact hj3
                  | succ n =>
                    cases n with
                    | zero => exact hj4
                    | succ n =>
                      cases n with
                      | zero => exact hj5
                      | succ n =>
                        cases n with
                        | zero => exact hj10
                        | succ n =>
                          rfl
theorem transfer (t H ph : Nat) (h : FixedStart.ready c d budget 13 t H ph = false) :
    chk [] rt 0 13 t H ph = false :=
  (chkF_eq c d [] rt 0 13 t H ph (by rw [eqL,eqM,eqG]; exact hc)
    (by rw [eqL,eqM,eqG]; exact hd)).symm.trans ((FixedStart.prepared c d budget 13 t H ph eqB).trans h)
end
end D13

namespace D14
noncomputable section
open FixedStart (ls ms gs iv eqL eqM eqG)
def ns := normalStep ls ms gs
private def budget : Nat := 0x6b3ace718ce719bdf37be317be738ce2d7c5f19c5f17d673bce317be339be6face317cded6c5ab5ad6b6ad2b4b5e95a56d5bd2d6a525394a73
def iz : Nat := 0x5ed7b5ab5b5ab6a52d4a56b4a5ad5b5674ad2b6ad2b4bdad8b56b4a56d6a5a97b56b4b5694b52739ce749ca72a565394e93aca949ce328c652
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem eqB : pL (rt.map fun e => 16 + (14 - e.2)) = budget := by decide +kernel
def a (n x : Nat) := fromTrace 14 ms (iz,iv) (digitList n x)
def j0 : Tree := (a 4 0x2654565164685503504e20644485507500087630ed0617304074547542644ee0565164684613307504e6)
def j1 : Tree := (.fork (.fork (a 14 0x2464764151502867504eb075465525650106b604660674874143702547304e90564504143702647304e30274634386053757630e20174676037030637630ed0174576037030637630ed0174476037030637630ed2634396433231008550754595197403604d10566614685502717504e31504074547542644d70162867054587630de0467460685503504d1) (.fork (a 15 0x704084386053757630ef0574874153401757604ec0474304153401757604e70464764151502867504ef0374676037030637630e80374576037030637630e80374476037030637630e80784755597403604da0754595397403604da0684755597403604da1504074734523647724eb0405300087434637630ed2765164685503504da0565164685503504d30357350574162867504ed) (a 11 0x464764151502767504e20464505074502757504eb0364505074502757504eb0274142647034637630ee0074634386053757630e00717304087542644d90162687074787630d91164684613307504d60056600685503504dd0357350574503504d30074637630387500d6))) (.fork (a 16 0x2364505074502757504e81504074634387633500eb075465515650106b6046c0674874143702647304e90636396633231008510076644547542644d00675504877500307300e70575304877300607600ed0475504877500607600e50637630386053754df3304074547542644d20634387500087630d40685507500087630d30485507500087630d30637630374161867704e00456600685503504d1) (a 17 0x674875411702717304e40574875411702717304e40574875153400757604e80564504143702547304e20544475074502757504e20504084686053757630ed0504084486053757630ed0474305153400757604ee0464764141601647504e50274142547034637630e427546570464010585526445451464010585c0784812807207304d70367360686053754de2755564685503504dc1564684613307504d50074367360687500da)))
def j2 : Tree := (.fork (.fork (.fork (.fork (a 9 0x2617174787630c42385186053754cb0595607603604c70537530387620c40196813507304cd0786517104307300d90686517104307300d90267260687300cc0657650587300c8) (.fork (a 12 0x2487074787500c120967036010384e0785186033534cc0695407403604c90685186033534cc0585186033534cc0512717407604ce0485186033534cc0385186033534cc0285186033534cc0086647434637630df0086637434637630df) (a 13 0x2487074787620cf0806097233634ce0785186053654ce0685186053654ce0585186053654ce0485186053654ce0385186053654ce0285186053654ce0674407400307300db0574407400307300db0574307300507500db0374307300507500db0574877300607600db))) (a 17 0x26252160110284c2606086403604cf2484607603704c52406316101058472406086723324c523060866010384e0736397053654cd0706097733534c30676407403504c80786717104307300dc0686717304607600d30686717104307300dc0486717304607600d317168031010384c0386647034637630dc0654587504507500dc0812917707304cf)) (.fork (.fork (a 18 0x2474047042644cd2406066603304cd2406066601068420897686053754c90896343037534cf24062161010684f26063161010384f2685586053754c90784386053757630d90584686053757630d90584486053757630d90284686053757630d90284386053757630d90634386053757630d90286033534637630df0074677030637630d70074577030637630d70074477030637630d7) (a 6 0x2606076713314cc2565466687300c70677066353654c40185086403204ca260604640106848075465500a7075045a)) (.fork (a 18 0x2477264687500cb2414197603604c723570464010584420967033010384b1464685587300c11464685287300c10785465687300c10677670787500ce0084237233634c20474507500507500d30364507500607600d30686724603737504dc0504877500507500d3085525650106b60453085565650106b60453065525650106b60453040065500950350452010015500950350452) (a 22 0x2606086423624ce2527316101038472206076731008492206046401058442064637633634c10797605503504c10736397253654c90684407403204c90357350587620c72404487104607600d10686617304507500d90586617304507500d90564507500307300de0474307300607600de0274037030637630de0784706803417104d90684706803417104d90504877500307300de27555464010584d27455464010584d0687374502757504d80637630387500c7)))) (.fork (.fork (.fork (.fork (a 11 0x2386833631008442074547542644c60395197403604c30295197403604c30416401058187620540736823237534c70895197403604c30795197403604c30695197403604c30595197403604c30784707703304c4) (a 15 0x2467054587620c92406086563764cf2206076701058402084737733534c00946497703704cd0896357053754c10796357053754c10736397053754c10696357053754c10602917307504ca0596357053754c10496357053754c10296357053754c1074671102848750055075465401b7075045d)) (a 12 0x2606086233634c72606076733434cd2406086733534cd0866687604307300d90574432626837324dd1464687304607600d60674143702547304d90574143702547304d90684143702547304d90484143702547304d90284143702547304d90567560687300ce)) (.fork (a 14 0x2614197403604ca2567054587630c224060866010384c2306076731008432216803101038490686645487300cb0602517307504c12644485287300cb0786645487300cb0586645487300cb26964332310084b0386547034637630dd0546621256757314d020666400095035045d) (a 20 0x2606076731008472406086703504cf2245146401058400786147042644c70785186403204c50756587042644ca0686147042644c70685186403204c50636703037734c60586147042644c70585186403204c50485186403204c50386147042644c70285186403204c50686407104607600db0486407104607600db260606473100a644570486147042644c70186037030637630d90074734523647724d0))) (.fork (.fork (a 17 0x2606086733734cb2565464687320c62507316101038452406086723724ca2406086703704c00897655587300c30797655587300c30786047042644c40686047042644c40586047042644c40486047042644c40402517307504c506167031010384b0152857046644cd0607602087630cc0607602074637630dc0504143702647304d8) (.fork (a 12 0x24161866010384c23967031010384a2206076701038410696813207304ca0596813207304ca0496813207304ca0396813207304ca090670104a087620520374877500607600d52474151502867504d32464151502867504d30896813207304ca) (a 12 0x2606086733534c12426266631008412406076731008400706803407704cd0374644487641507500e70786404803717304d8073100a636387620510606084787633500d40606084687633500d40606084487633500d40606084387633500d4078434100a62732458))) (.fork (a 21 0x2467054587630c62084257253654c32044347342644ce1577364687500c60785186033634cf0685186033634cf0585186033634cf0506097733534c80485186033634cf0462867357754c40402817307304cf0385186033634cf0285186033634cf0504084687623500d00504084487623500d00686745601647504dc27570464310084b0685263404757604d50485263404757604d50357350574507500d00274141544747743404ee) (a 14 0x2606086363764cb2306066631008452306046401068480896857253654c20706077353654cd0702817607304c70696857253654c20156347342644cf2704787404307300d82646475174307300d7087671102a787500530374624287623300d6074641102a8576545b0257250574507500d5)))))
def j3 : Tree := (.fork (.fork (.fork (.fork (a 6 0x2526276701038482526246401068482306046401058400474047042644c40507500087630c00507500074637630d0) (a 22 0x2606516101068470584407403604c92654587504507500d81304087434637630d90684407401607600dd0674607601307300dd0584407401607600dd0574607601307300dd0484407401607600dd0474607601307300dd097670107a8072045a0604987601307300dd0546613146644cf0186647034637630d20386037030637630dd0676037030637630dd0576037030637630dd0476037030637630dd0384163401767604d60674163401767604d60574163401767604d60274163401767604d6)) (.fork (a 10 0x2606086723524cc2606066353654c424060363010584c0976797403704c30086803101038430686617204507500d60586617204507500d6098681102a83753456093630107a837534563300047042644ce) (a 15 0x2477064687300c60896863357754ce0596863357754ce0484607603604cb0746711028487300500504084687633500de0504084487633500de0286647434637630d20286637434637630d20186767054657650d40584153401757604d80384153401757604d80674153401757604d80574153401757604d80274153401757604d8))) (.fork (.fork (a 10 0x2587274787600c32407054587300cc2207034387600cb0706803307504c10196237033534c90785207200307300dd0685207200307300dd2806616101038491410187034637630d71307300074637630d0) (.fork (a 5 0x6467334310084b03767334310084b0342457246644c70784253706547304dc0684253706547304dc) (a 20 0x2506416101068420895697403604cd0895397403604cd0895297403604cd0795597403604cd0795297403604cd0695397403604cd0695297403604cd0595297403604cd0395297403604cd2074677030637630dc2074577030637630dc2074477030637630dc0895797403604cd0895597403604cd0795697403604cd0795397403604cd0755597403604cd0695597403604cd0595397403604cd))) (a 18 0x2606086723324cf2516176731008472467054587600ca24262767010584824262666010684823062161010584e0896837233534ce0696837233534ce0586833631008470186747542644cb098683100a83753452074643100a857654520545146401058400486833631008470766833631008470505500097757630d10505500087654637630e10057050587620c2))) (.fork (a 22 0x24262767010384824161767010384c1577064687500c70895707703304c80754597403604c70676957353654c20784987401607600d70684987401607600d70274877030637630dc05868031010384c0037030387650cc0274677030637630dc0274577030637630dc0274477030637630dc0037030387620c50037030374627620d50684263405757604d10484263405757604d10476145150757604d201463400095035045d2046340009503504540686705503504c2) (.fork (.fork (a 12 0x24161767310084b0896713407204ca0796757587300c00795613407504c10696757587300c00196757053754cd0574207200507500d40474207200507500d42756585487300c02756585287300c00896757587300c00304163401767604d2) (a 12 0x2507316101068480606703407604cb0585086403204ca0485086403204ca0285086403204ca0196857053654c30786607104307300dd0686607104307300dd0504084687323500d70504084487323500d70785086403204ca0685086403204ca)) (a 15 0x2616416011028462587074787630ce2434307303704c32407064687300c42406216101038462406086753754c024060862310084726063161010684b0074547542644cf0704096053757630d70084737733534c40304153401757604d82340008685503504580474151502867504db0464151502867504db))))
def j4 : Tree := (.fork (.fork (.fork (a 15 0x2527316101068432484707703704c92207064687300cd0676357353654c00636703037634cd0142467057654c62764687504307300df0084686053757630d20084486053757630d20084386053757630d20086033534637630d80186547034637630dc086476500b6076045a0602817307504c3074000a68550350457) (.fork (a 17 0x26065161010384f25063161010684f0785686403204c80785586403204c80785486403204c80785286403204c80685586403204c80685486403204c80585486403204c80585286403204c80485286403204c82574877300607600d60586403500757604df0286403500757604df0366403500757604df0467460685507500de0685286403204c8) (a 15 0x2487074787600ce2424313137634c10506097233634cc0196837033534cd1104087134637630d30876601038787600520826601038287600520546401058487600520074734522867647724e50676601503504cc0476601503504cc0376601503504cc0276601503504cc06550086855035045c0586601503504cc))) (.fork (.fork (a 22 0x26060464310084c2306076701058450896357253754c70785686053754c70785586053754c70785486053754c70785286053754c70685486053754c70685386053754c70685286053754c70585386053754c70585286053754c70485386053754c70485286053754c70385286053754c70257046401058420657046401058420785386053754c70685586053754c70585486053754c70464151502767504dd0474151502767504dd) (a 4 0x26060464110284425161464310084a23161666310084b0196837733534c7)) (a 16 0x2565464687300cc23060767010384c22060666310084e0976797253754c80896757253754c80754597603604ce0736803037534cc0584707703504c70402517307604cd0096703101038410876601038787620520546401058487620522206046401068462687074787630c70142647034637630df0377370787500cf))) (.fork (.fork (.fork (a 6 0x896813507304c70696813507304c70396813507304c7024643323100843089643323100843039643323100843) (a 17 0x2487074787650ca0357350587600c80785687104307300d00785587104307300d00785487104307300d00785387104307300d00785287104307300d00685587104307300d00685487104307300d00685387104307300d00685287104307300d00585487104307300d00585287104307300d00485387104307300d00385287104307300d02375074502757504da0706803607304c2)) (a 21 0x2467054587300c22406036303604c32385286053654c52206066601068460897386053654c50706097233534c10702917607304c00697386053654c50597386053654c50217210187300c40186653346644c22856756587320cb0797386053654c50507500087620c00201048603607604560147400485607600d71507500574607600d81307300374607600d90684613307504c10307300500756717504ec1464687404307300dd)) (.fork (a 11 0x2406087242644cf2406036303304ca1674797587300c60897565687300c60527520287300ce0196813207304c30174644487641507500ee2604687104307300d10374624287623500d00307300087620c40505074502757504df) (a 16 0x2606086703204cd2606036303604c02084237233534ce0896837733534c40696837733534c40596837733534c40496837733534c40402817307504c60296837733534c40162967057654c42474307300607600d32374877500607600da080103a866687500590074357350657650d92074734523647724dc282741610105847))))
def j5 : Tree := (.fork j3 j4)
def j6 : Tree := (.fork j2 j5)
def j7 : Tree := (.fork (.fork (.fork (.fork (a 9 0x2606086263764c924161767010584e0142847037534c20096837733534ce0386507034637630d20686704603617204d50086747542644c90674403404307300d20574403404307300d2) (a 18 0x2606086703304c72414147303604c62406316101038482406066613314c00866697403604c00597086403604c50397086403604c50297086403604c52646475374307300d02646475274307300d00786647474307300d00574324287323500df0086737434637630d228262666310084c0897086403604c50797086403604c50697086403604c51610687504307300d8)) (.fork (.fork (a 22 0x2516146401068480896703301038490636703301038490577066687300cc0512817407704c10296703301038490785687404307300d30785587404307300d30785487404307300d30785387404307300d30785287404307300d30685587404307300d30685487404307300d30685387404307300d30685287404307300d30585487404307300d30585287404307300d30485387404307300d30386747034637630d50385287404307300d32057050587630c80674877500307300df) (a 8 0x23062161010384d0896513207604cd0796513207604cd0696513207604cd0596513207604cd0396513207604cd2867054587630cf1404087534637630db)) (a 10 0x2614147303604c30686707504607600de0486707504607600de020106a70608732058260621610103849085515650106b60450065515650106b604500327320287500cc0074634387633500d40647640485507500db))) (.fork (a 17 0x2606057342644cd2506316101038402406086603704c42406036303704c923060464310084a0737732837534c70617610187300ca0484707703204ce0357352857654c30132347037534ce0464765402544507500e50086647134637630d8089670104a8072045e1610687504607600db2376601503504c30076601503504c101550086855035045b) (.fork (.fork (a 18 0x2385286053754c70797386053754c70785686403604c80785586403604c80785486403604c80785286403604c80697386053754c70685586403604c80685486403604c80597386053754c70585486403604c80585286403604c80512817407504cf0485286403604c82654587204507500dd0897386053754c70685286403604c80684613207504cd) (.fork (a 16 0x2316146431008480785686033534c80785586033534c80785486033534c80785286033534c80685486033534c80685286033534c80585386033534c80585286033534c80485386033534c80485286033534c80385286033534c80785386033534c80685586033534c80685386033534c80585486033534c8) (a 7 0x786617404307300d90686617404307300d9057670360103840047670360103840089670360103840069670360103840029670360103840))) (.fork (a 15 0x2426286601038490896057053654ca0846497603604c70796057053654ca0696057053654ca0657246401058490596057053654ca0496057053654ca03967031010384a0396057053654ca0296057053654ca0686717304507500d10586717304507500d108967031010384a0684613407504cc) (a 8 0x2584407403604c32306066601068460586813407104ce0402517307704cb0074537530637630d12856756587300cf2716146431008461410487304607600d9))))) (.fork (.fork (.fork (a 21 0x2487274787500cf2477064687500c12425216011028402406086703304c10946497603704cd0896407403604c30796407403604c30696407403604c30656407403104cf0596407403604c30406503307504c80396407403604c30046403101038442604687604607600da0785407400307300db0685407400307300db0474877500507500d90304084787653300d20304084687653300d2280661610106841239663323100840) (.fork (a 9 0x2406086603604ca0706803407504cb0346403046644cb0284037033634c70386207034637630d30307300087650c20307300074657650d2070606663100a644561507500574307300d7) (a 19 0x2484607603604cb2407104087630c40976797603704c30896857053654cf0896807603204c20796857053654cf0696857053654cf0577066687500cd0496857053654cf0396857053654cf0346423246644c40296857053654cf0716803101038400286033434637630db0674143702647304d30574143702647304d30684143702647304d30484143702647304d30284143702647304d3))) (.fork (a 14 0x2606076711028492406086263764cb2344503057754c11577064687300ce0736813137534c20706803507304c90196507403604cf0037032837534c52606416101068441404087434637630de0485507500607600d20475507500607600d21504877500607600d20567504574507500d6) (.fork (a 13 0x896037033534c20796037033534c20696037033534c20596037033534c20545146403104cf0496037033534c20396037033534c20296037033534c20705500097757630d7068491105b607604530575474502757504dc0575374502757504dc0545474502757504dc) (a 12 0x25161767010384c2406087542644c30746497703504ce0057052857654c20416401058187600522756585187300cb0674875602615307300e50574875602615307300e50152657046644cd0585307300607600d60575307300607600d61304877300607600d6)))) (.fork (.fork (a 14 0x2626276701038492626246401068492477064687320c92467054587320cd07468334310084e05868334310084e0506077633634c703868334310084e0086547134637630db0174744631757837504e80546603046644c01507500087630cd1507500074637630dd0267260687500ce) (a 11 0x744497053654c60674207200307300d60574207200307300d60574027020327320d60304084787623300de0304084687623300de0186467054657650d00074654587653300d00367360687500c81504084687633500da1504084387633500da)) (.fork (a 13 0x2616176701038402606086723724cc2307074787500c20517510187300c80402917307304c8064400a6855035045f0086737534637630db0162677067764ce0684503403504c20454503403504c20685507500307300d20675507500307300d21504877500307300d2) (a 21 0x26064161010384b25060767010384d2406086703204c00785186403604c60785186053754ca0706097253654c50685186403604c60685186053754ca0585186403604c60585186053754ca0537530387600c60485186403604c60485186053754ca0385186053754ca0285186403604c60285186053754ca0086653346644cf07467010584873005b070105a6444873005b0507500087320cb0167600685307300d7)))))
def j8 : Tree := (.fork (.fork (.fork (.fork (a 20 0x2416166601068420785686033634c80785586033634c80785486033634c80785286033634c80685486033634c80685286033634c80585486033634c80585386033634c80585286033634c80485386033634c80485286033634c80385286033634c80196513207604ca0186747034637630d90785386033634c80685586033634c80685386033634c81304087030637630dc0237230387500c1) (a 20 0x26161464310084c2606086253654c024060767110284324060767010584524060363010384e2385186053654cd2316146401058440896507403604c00784607603104cb0696507403604c00606703207304cb0396507403604c00286737434637630d90086033434637630d00585153400757604d60385153400757604d60675153400757604d60575153400757604d60275153400757604d62647304374607600d1)) (.fork (a 17 0x2616146401068452427216101058452206046431008432084237233634ce0676857353754c30686417204507500dd0586417204507500dd2806606087630c00142547034637630d80784253706647304df0684253706647304df0675411702717304d00575411702717304d00475411702717304d00685411702717304d00585411702717304d00485411702717304d0) (.fork (a 9 0x2617104087630c71464685187300cc0896713307704ce0577064687500c80746487504607600de0186507034637630d0089623100a8375345d0176601503504ca2574403404307300d6) (a 16 0x2416166631008440976797053754c60896757053754c60796757053754c60696757053754c60657146401058490496757053754c60396757053754c60296757053754c60277270787500ce2654587304507500d80274634387633500d527451464010584d026663323100847089663323100847059663323100847)))) (.fork (.fork (.fork (a 10 0x2617404087630c12606086231008422434307303604c82206057342644c70897686033534c60686717104607600dd0486717104607600dd2836636387620c12685386033534c60504143702547304d5) (a 14 0x2507104087630c624272161010384b22868031010384c0896237033534cd0796237033534cd0596237033534cd0496237033534cd0356413146644ca0122247037534c10386647134637630d50686755502767504d30575074502757504da0475074502757504da0375074502757504da)) (.fork (a 6 0x24060666110284b2304603207504c10686747542644c60386747542644c62644547542644c60684037033534cc) (a 22 0x2606036301068460785686053654ca0785586053654ca0785486053654ca0785386053654ca0785286053654ca0784237233534c20685486053654ca0685286053654ca0585386053654ca0585286053654ca0485386053654ca0485286053654ca0385286053654ca0196357053754c724062161010584c2844503057654c60685586053654ca0685386053654ca0585486053654ca0142947037534ca0627620287300c5))) (.fork (a 15 0x2606036301038422527216101038402507316101058482406086723524ca0656807403104c52534375274307300db0784987601307300da0676535374307300db0584987601307300da0476535374307300db010007a6855035045d203440106a827624540376624722737524d00057050587320c60706803307304c4) (a 12 0x26262464310084e2487074787520cc2207046401058440756833357754ce0185086403604cf2074634387633500d0053100a6363876205e0274537530637630da2836636387600c40577064687320c80484273405767604db0305153400757604dd)))) (.fork (.fork (.fork (a 6 0x24060666310084d0402717307604ce0086767354657650d12857646411028430142457046644c90057050587630c4) (a 22 0x2426276731008442406086233634c42244123257754cf2206086601038460786653346644c30686653346644c30402817307704cd0286653346644c30142747037734ce0785687504307300df0785587504307300df0785487504307300df0785387504307300df0785287504307300df0685587504307300df0685487504307300df0685387504307300df0685287504307300df0585487504307300df0585287504307300df0485387504307300df0385287504307300df)) (.fork (.fork (a 13 0x25062161010684e25060464010684b0706087542644c30577366687500c30316403101038410184057053754ce0786707404307300d70686707404307300d727464972310084f0701048603607604530686605503504cc0464141601647504d70474141601647504d7) (a 10 0x2316186601038452257046401058430285086403604c40186207034637630da2857046401058472606076701038460785086403604c40685086403604c40585086403604c40485086403604c4)) (a 12 0x2606056343644c125273161010584b2486147042644c70452857346644c10406503307704cf0196407403604c10184727723524ca075274554400b504560746701038487500500544008597703504560504096053757630da0627620287500c8))) (.fork (.fork (a 14 0x25272161010684825062161010384b2486047042644c42406086603104cd2406076701038412234603037534c320367033010384d0795613307504cb0706803307704cf0602717307704cd0257250587300c80386547134637630d22684503403504cd2654503403504cd) (a 15 0x2536376731008402406316101068442406086613614ca0896037033634ca0796037033634ca0696037033634ca0596037033634ca0496037033634ca0396037033634ca0356403057654c80574427420327320d42644485187300c2260621610106848270661610103846070661610103a64456)) (a 21 0x2616176731008422607074787630cf25262767310084025262464310084b2406066633634c32406036301068432064357353654c12056347342644cc0896837033534c80796837033534c80696837033534c80596837033534c80577064687300ca0496837033534c80296837033534c80686617104607600d0050650106a087620580486617104607600d00286737534637630d42644487304607600d60812807207304ca))))
def j9 : Tree := (.fork j7 j8)
def j10 : Tree := (.fork j6 j9)
def j11 : Tree := (.fork (.fork (.fork (a 19 0x262624500b60444241102b5466444223010681875004d094754100b6044e093100b5376344b0407401647504c9031105b507604492477067764bd0786747544307300d80686747544307300d8053100a8375344c2606087630b13054722767524c02816617414b9074401b607604472617407604bb23440095035044e27110281875004d2407207304b9) (a 17 0x253401a08763045250620405b6544c250106b0466444e2406086727620c80846497607500c0053100b637634420506097737620c80307302847304c4221106a407204472826527324b4230603400b604421607603604bb1607600757604cb2316187500be0457450756717304d92517104307300c40157152757204cf)) (.fork (a 21 0x250406b3576544f0897705607600c00797705607600c00697705607600c00687624327320c60597705607600c0012105b307304490084187623300c4270104a82762443083100a857654492467057654b62807046644b82627246644b22467055656644c62087534637630c71407403604b91407400757604c90253205747604c80613306767504c60611407737504c60523606717304cd) (.fork (a 11 0x230106b3466444c0627623324b9210104a827624460896607307300c50796607307300c50696607307300c5060107a8173144a0596607307300c50396607307300c52357146644b4074774000b50442) (a 14 0x64101b0375344c073100a85765445040106a7072044f210105a733734460037030537530cd2826727424b4263001a08732049080120104b604470587300607600cd0387300607600cd2736387500b20307300507500cd0147142747304c20407400307300cd)))) (.fork (.fork (a 16 0x2367055656644c6084514500b604490687204607600cc0487204607600cc030310104b604432367057654b63055641656644c62647034637630cb0687424327320cc043000b40360447262624400b504472407403504be0687504507500c30587504507500c31504746544507500d32717104307300c7) (a 15 0x2356611767614cb2345541656644cc2036402647304cd081105b6076044d0754597433604c10317312717304c82937537634bc0757753754be0464764327320507500eb0574877320507500db0474877320507500db070630505b654492517307604b62517304757604c62726287500b5)) (.fork (.fork (a 16 0x26110287873004e26110286873004e26110284873004e261003a2873004e23010587873004e23010586873004e23010584873004e230006a5873004e071102a5873004e040106a2873004e220106a8076044e2637346644b1034100a267530442626527324bd0687504607600c70487504607600c7) (a 11 0x243401a08763042080106b746644480707701847704c80407402767504c12907037634b20027023524b82806706757504c7210104a6273244e2426287600bd0253306647304cc2806407104b9)) (a 22 0x261621402b32441254101a0876504f2357541656644c12347541656644c1223401a08763046083100b3466444a060103b74664445053100b346644420087254657650c32856767530b52377067764bc2285187300bb0057053754b72457146644b82644487320b6054101b403604480a4101b40360448054101b40075760458094101b400757604582717304607600c80747741647504c72787404307300c2))))
def j12 : Tree := (.fork (.fork (.fork (a 19 0x2036401747604c60976797727500ca060108b23753442052541502b3244a0084187653300c42967157654bc0896827627500ca0796827627500ca0596827627500ca0496827627500ca2457046644b70853536747534c9210105a7233244b21010587227573245b2355161867704c50307303604b80307300757604c80747741747604c00747742647304c4) (.fork (a 13 0x787304307300cc0687304307300cc040120104b204460047041656644c70796053757630ce0596053757630ce0296053757630ce0286053654637630de0853436747534c4270614500b6044d0273805767604c2027401b2073044e2806407204bb) (a 13 0x23161010583e2405401647504cd2087154657650cd2907037534bb2717137734b4015500a8667675045c220107a6073044c0087030637630c92343037534bb020106a087320413534501747604c30723306717504cd080104a10271730454))) (.fork (a 15 0x271601102838250106b146644402235008187630410097635637630c12526287600b9050107a60730449221104a6073044c210106b3426444a0637633634b52616517214b3094401b807604450687304607600cb0487304607600cb035401b30750441025401b2075044c) (a 14 0x24350081876304f212403b0273244e0946497727500c40806097637320ca060107a4072044f0287634637630ce3054732767534cc040106a8276244c2826727324bb2907207604bc0897587300ba0797587300ba2585487300ba2585287300ba))) (.fork (.fork (a 11 0x906097763734c50466697433304ca026726000b304422567057654b40786534437433304da0686534437433304da020107a60720441060107a0133144206310085027575045d2724603737504c62707207304b2) (a 20 0x261641402b3244a260106818730041252103b04664446020104a0876504f2247037734b6060107a80710445070640505b6544c2467054657650cb0057050657650c9223100b746644480287534637630c43434521747624cb2816517314ba0507500607600c90273306767504cd0507500507500c9067401b607304420501068613617304522701058187300410657652757204c1)) (.fork (a 17 0x534397533600c50184787523300c42747237634b42747137634b52617307704b0280310005b754412317146644b80037030637630c7284484500b6044f1263704757604c92856587600ba2536387600b90307300607600c70307303504b60501602867504cd0607602717304ce0507500307300c7) (.fork (a 8 0x30730005b6544d0096787633500c32577067764b53605503504b82617304507500ca2817507304b90407403204be0706803417104c6) (a 15 0x253500818763047090320104b604470897106307300c50797106307300c5063763000b604480617612717304cc0397106307300c52917407504b10407403704bb0184987633500c92606087320bc2487604607600c43054702767504ca050108b6033044c0657652757304c7)))))
def j13 : Tree := (.fork j11 j12)
def j14 : Tree := (.fork (.fork (.fork (.fork (a 12 0x2614197433604c0093373100b6344a083343100b6544e053100b537634430305203527304c8080620505b6544b2907607304ba0707703304ba0675174307300ca0575174307300ca0475174307300ca0275174307300ca) (a 15 0x2614197743104c52545541656644c324310087876204e24310084876204e242623400b6044f0846522757724ca0607602767504c00476797433304c20257253754bb080650505b654462767354657650c82836637434bf24310085876204e053100a3876204e2806507104b8)) (.fork (a 8 0x806067877530c30307302717504c60846816646417204dc240006b7577544d241102a053754430087654657650c42636387620be0657650757604ce) (a 16 0x23010687875004a23010684875004a23010683875004a230007a6875004a2046502757304cf040107a2875004a053100a8374344f0196827627500c02357053754b02806087630bc0853636747534c227110287875004a081102a6875004a27110284875004a27110283875004a271003a2875004a))) (.fork (.fork (a 9 0x947456757724c60411107417204c3084100894764772453071102a7375344c060107a8072044c060107a607104452847137534b9041403b6273244a2826737200bc) (a 14 0x261613400b6044a243100818762044083100b5466444a230106b7466444e2657146644b12607046644b7090105b30760448065501b4076044c034734100b6044c230614500b6044403473410087576045c3654702767504cd0253505647504c92806507304b8)) (a 21 0x253636400b3044f240406b85765443084100b1466444b020106a087630432836387650bb2647037534bc0674877420307300d0083100a8476444c0547542644b12206087630b52087434637630ca0734523647724ce0432626837324ce2816717414b4094401b3077044a3654701767604cd1263604757604cd2626287600b50143702547304cc2687604307300cc2046502757204cd))) (.fork (.fork (.fork (a 15 0x387234637630c50184787323500c70184687323500c70184487323500c70184387323500c70184287323500c72917137534be2807507304b00084837536727620df051106a407104430096837537620cf3654732767534c13534521747624cc075501b507604420253505747604ca) (a 11 0x210105878732048210105848732048210105818732048210006a587320480a57047647724c12404703617304c6012103a707304482101058687320480607602757604c80787400307300ca0687400307300ca)) (.fork (a 13 0x2306074637630cd0976797633704c10897505307300c20797505307300c20697505307300c20597505307300c20247241656644c4064500b1466444f2306087630bd2547034637630c7084674500b604410501602767504c60655156757504ca) (a 22 0x210106a387620480786846647300c20785686647300c20785586647300c20785286647300c20686846647300c20685586647300c20685286647300c2065400b303504490586846647300c20585286647300c20286846647300c22567357754b40196857657300c52826287650bd053323100b5344e2755162767504cd0897687300b22685587300b22685487300b22685287300b22645487300b2))) (.fork (a 17 0x78660103839251621402b3244c250107a187500412306102617404c10946497707500ce0946497633704cd071104a8075044a2677067764b7250106b3466444f0273405867704ca034401b30760441024401b207604420687104607600cf0487104607600cf057401b507304462817307304bc2716187300bc) (a 11 0x220604400b5044a0407402747304c32147042644bb210105a423724432826627424be0407402757604ce2636387600b52407104607600cd0305303534607600d12826287300bf2626437200b8))))
def j15 : Tree := (.fork (.fork (.fork (a 16 0x2605502757504ca215401b30750449090310104b6244b0605603767304cf024724000b504450107102717304c42937637634b9240106a0537544f270103a0537544f2047042644ba0584161867743704d00284161867743704d0095501b8076044a2617207604bf3434501747604cb264447500b3044c) (a 18 0x2387034637630c02305601867704ce0906097757320cd0866697617300ca0754597607300cb0706097537620c20466877643304cf0305303837304c72427257754bb221104a407204422467257754bb2857046644bb0057052757734c8210106a41361448275154400b504480195503743504c62544474507500c12807607304b0)) (.fork (.fork (a 15 0x574503504be091102b6376344a080310104b5244d043743000b60444053100a73675753451260620405b65448240601402b3244f3034722747324c20047042647314c32816617214ba2687604607600c22813207304bd0607603304bc0813206747304cd0811307727304cd) (a 10 0x806097767320cf073100a587320400456641767644cf2631008787320402631008687320402631008487320400577500607600c20377500607600c21501610766717504da2706507204b3)) (a 22 0x2827257754b02617167764ba0707703104bc0784987641507500d7212103a80760448083100a8376344e2867257754b02457246644b72427246644b7273100a38762041034100a62732448080106b403604422646487600b3076565500b504410606097633500c40384687641507500d70384487641507500d70644487641507500d7284447500b3044a2404803717304c83604702717304c02644487300b0))) (.fork (.fork (a 21 0x2414197733704c11507500757604cb0966697743704c00806097657320c50787274307300c80687274307300c80587274307300c80487274307300c80307302817304cd280103a84754447240107a84754447080104a8076044f070107a60730441034100a827624480287434637630c82717507604bd0253705747604c70385303534607600d62745601647504ce0504097623500c0281417500b30447) (a 20 0x213401a087630442087234637630cc0897035637630c0080106b2466444c0607601767604cb060108b837534460397035637630c00184787623300c70184687623300c70184587623300c70184487623300c70184287623300c72347037534be2207037534b52907607604b91263404757604ca2807604757604c92705601647504c80787204307300c40687204307300c4)) (.fork (.fork (a 9 0x246522757524c30087154657650ca2317137534b00057052757724cc2856587320b0065401b507504480273306867504cf0271404977837504df0405402544507500d1) (.fork (a 7 0x184987623300cd060406b457654482857253654b82757251656644c80855363767724c82416187600bd0253206847304c8) (.fork (a 22 0x784687623300c50784587623300c50784487623300c50784287623300c50584787623300c50584687623300c50584487623300c50584287623300c50484787623300c50484687623300c50484587623300c50484287623300c50384587623300c50384487623300c52967257654b30784987623300c50584987623300c50484987623300c50384787623300c50384687623300c50384287623300c50624287623300c5) (a 2 0x93100b637634422506087630bb)))) (.fork (a 11 0x61107b407604420347342747304c40184987323500c32647137634b4270441502b3244f2826627324b02517307704b8085401b7075044f0687300507500c40487300507500c40347342647304c8) (a 18 0x2464697507300cb223500878765044223500848765044223500838765044084101b0466444c083100b63763444080108b237534440467462767504c00411307437304cf034500a2876504408410189078672045704010489278676245a274101a80720447220106a807204471856806757204ca241102a8576544a271102a7875004c0253606547304c5)))))
def j16 : Tree := (.fork j14 j15)
def j17 : Tree := (.fork j13 j16)
def j18 : Tree := (.fork (.fork (.fork (.fork (a 10 0x2584787623300c32584687623300c32584487623300c32584287623300c30696587623300c30396587623300c32747537734b52737537734b52584987623300c30047042644ba) (a 13 0x2076731008322605601767604c025350087876304c25350085876304c25350082876304c0897606307300c50797606307300c50706086647520cc063500a4876304c0417412717504cb0397606307300c52706087520bc0253705647504c9)) (a 19 0x2457246647304c9056756000b3044b0896707413104cb0796707413104cb070107a607204450696707413104cb0596707413104cb0396707413104cb2037030637630cd0407403604b90163401767604c60407400757604c90407401607600cd0167162767504cd3504702717504c42687504507500c82316187300bc0607601307300cd270107a8072044a)) (.fork (a 20 0x90107b80760441031105b40760442030107b2076044b0196587623300c20785287300b00096857657320c80057051877754cd050106b3466444f230107a83753446281102a837534462617204507500c60785687300b00785587300b00785487300b00685587300b00685487300b00685287300b00585487300b00585287300b00485287300b0) (.fork (a 21 0x2587274307300c9230106878730040230106858730040230106848730040230007a687300400963355877754cf040107a287300400186897713304cb2863357754bf2207046644bb2647434637630c12637434637630c1210105a423624450153401757604cc2655162867504c90504097633500cf271102878730040081102a68730040271102858730040271102848730040271003a28730040) (a 6 0x251614400b5044b0197346647320ca0136947407200c40474877530507500d80607603604b50607600757604c5)))) (.fork (.fork (a 20 0x2056601767604c30897305507500ce0866697607300c60797305507500ce0706097743534c10697305507500ce0597305507500ce010710005b654482846487630ba2207037634b3073100a857656644510701088947647724592804403717204c6045501b30760441035501b207604422517307504b92507307504b10523606817304c01207200307300cd2606407104b8) (a 19 0x685503504b9240610405b6544e231614400b504472307500757604c3093500a787630410783355877754c9073153100b53446060107a287300430146512757514c20087234637630c62717407704be2733431008360347342644ba2087030637630c90687604507500cf0587604507500cf0253206747304c40253706547304c82606507204b7)) (.fork (.fork (a 11 0x2257500757604c422350087876304d22350085876304d22350084876304d034500a2876304d1607603304b9070107a627324462042403104be0283405877704c2240414500b6044a24041450087576045a) (a 18 0x260631402b324450946497763704c20756586647300c50744497657300c50205203627604cc09310089378775345c0531008937877534502867057754b6243100a85765440283100a8375344c2837233534bb0263705757604c50457450757604c22716187500bc2756587300b50787604307300cb0687604307300cb2706407204b0)) (a 16 0x243500878763048243500858763048243500848763048243500828763048095754500b6044c060108b037534462816187630bb07110487067575045d071104a7075044d283363100833083173100b65443083363100a644430037032867534c0001002b023324480273305767604c62417207504b9))))
def j19 : Tree := (.fork (.fork (.fork (a 16 0x242624400b5044b0906097757630c40706097547630cf0706097537320ca2823017314b82347037734b5243100a8475444a28031010383b271102a0537544c2082403604b62826287630bc0287030637630c7065401b407504430407402717504c41707703304be2806707104bd) (a 15 0x897046647320c60797046647320c60697046647320c6063100b837534490297046647320c60145008947647704591256406757104c42957353654b42816617314be2717207604ba2145150757604c02636374607600ca2705503504b80707702647304ce2475174307300ce)) (.fork (a 21 0x2606086647320cf250630405b6544b2457245647504cd0706097657320cf0466697743304c0031105b607604452907507304bb2817507704b62577267764ba283100a847544472716617314b50263405757604c8031105b60475760455220415500b50449087401b707304412417207304bd0897605307300c10797605307300c10697605307300c10597605307300c13204602617104c0) (.fork (.fork (.fork (a 22 0x2057541656644c80784687653300c40784587653300c40784487653300c40784287653300c40484787653300c40484687653300c40484587653300c40484287653300c40384587653300c40384487653300c40384287653300c40284787653300c40284687653300c40284587653300c40284487653300c40784987653300c40484987653300c40284987653300c40384787653300c40384687653300c40654587653300c4) (a 3 0x897635637630c00297635637630c02917607304bf)) (a 3 0x60108890786720454250310005b75441260603400b6044e)) (a 14 0x262623400b604410307302767504c5060107a6072044e0797401607600c00697401607600c00597401607600c00497401607600c0065401b207504410787200307300cd2687404307300c10687200307300cd0787406534307300d10687406534307300d12806607104bb)))) (.fork (.fork (.fork (.fork (.fork (a 19 0x896957657300c40895797657300c40895697657300c40895497657300c40895297657300c40796957657300c40795697657300c40795497657300c40795297657300c40696957657300c40695497657300c40695297657300c40496957657300c40495297657300c40296957657300c40273305867704ca0523216717304cb2797587300b42757587300b4) (a 7 0x230604400b504450507500207200cc0027020527520cc2516417214b92516187600b20611907743504cb0207200507500cc)) (a 6 0x251641402b324422507067764bd020105b3036044d020105b3007576045d0523806717304c52713407204b2)) (a 6 0x2407067764b9280441502b3244b1613407504b80795503743504c70595503743504c70395503743504c7)) (a 18 0x2076711028342287534637630c40784187623500c70605502757504c40584187623500c70484187623500c70384187623500c7023104b607604460205203427604c7020106a0876204e2867157754bc060107a627324440087434637630c4023104b604757604560504097323500c7231417500b3044a2607104307300cd0327300207200cd)) (.fork (.fork (a 15 0x2406102717304c10966697727300c50926297757300c50896787633500c50596787633500c50296787633500c52577367764bd2537367764bd2784987633500c5270640405b6544a2606087620b93534722747324cc060107a0135144e2340009503504460253206647304c0) (a 8 0x213401a087650470501068187300472027023524bb032403b1273244f3034501747604c93304702717504c03034702747304c52756574307300c6)) (a 18 0x2087254657650c9073100a403504480407402647304c80307301847704c92747237734bb2647237534b7053100a7375344c040107a6072044a0237233634ba2626287630b10160905867743704d3090105b8076044e043100a403504480151502867504cd0613306717504c6037401b307304460823806717204cc2406307104be))))
def j20 : Tree := (.fork j18 j19)
def j21 : Tree := (.fork (.fork (.fork (a 20 0x220106a0876304a0687404607600c2065734400b50443050108b237534440487404607600c2040740005b65441020107a067530430686714617613204d00586714617613204d00486714617613204d02357353654b02357351656644c00096053757630c90086053654637630d93354722767524c12866687520b90a5501b80760445284475500b504472806607404b42806607204b3) (.fork (a 9 0x50065500b504422187054657650cb0807801847704ca0246502757204c7280660405b6544f210105a6873204b091107b407604490603102717504cf2687400307300cd) (a 14 0x230004b8375344c220610405b6544f0966697743714c4060107a41351447051102b8375344c080104a70720448071771002b3244f2816517214bd054401b4076044c220603400b60444095401b807504402640009503504413104702717504c22787504307300c7))) (.fork (a 18 0x2536421747624ce210105878763047210105848763047210105828763047210105818763047210006a58763047063100b7466444c0346502757304c00197746647320ca2807207504b50956857657724c4070610505b654462707037634b90087634637630cb2403500757604cf2587300607600c6241616400b3044d2506407204be) (.fork (a 22 0x27464010583f26866010383f083100b73753442040104a023324442677267764bb09410089577577245e0157150757604cd240105878760049240006a58760049240105848760049050106a38760049240105828760049260103878760049070103a58760049260103848760049260004a387600492601038287600490655009503504462601503504be1400600867426717504ea0457452757304cc0147142647304c5) (a 9 0x243001a087650441307300757604cb0487624627620cd1307303604bb220104a707204440196837537600cc2836387520b9050106a43720042070104a63720042)))) (.fork (.fork (a 16 0x2355361867724c7031107b407604472816187500b22417207704b4020107a407204432357253754b72817146644b70087534637630c10734522867647724d4040601502b324402817307704b30201069503504450151502767504cd2917707304b30915807877304c32806307104b1) (a 11 0x231616400b3044a061104b046644402917707504b32816167530b4040406b25765442030406b157654412401058187620452601038187620453300500756717504da2826287500b42606307104b5)) (.fork (.fork (a 9 0x253643400b6044d241102a7875004a0346532757534c0034100b237534432757253754be240620405b6544a2187034637630cf095501b307604460263205757604ce) (.fork (a 16 0x243100b54664447230610405b654460756586647320c80744497657320c82507207704ba020104890786720451240105878762046240006a58762046240105848762046050106a38762046260103878762046070103a58762046260103848762046260004a387620462756587320b82575174307300ce) (a 9 0x230620405b654440197046647320c12807407504b60896707307300c50796707307300c50696707307300c50596707307300c50396707307300c5020106b4036044d))) (.fork (a 15 0x243500818765044210103878762041210103858762041210103848762041210103818762041210004a38762041064100b2375344a0136847607200c02677367764bb2637367764bb283100a8374344e243100a847644423354711767614c80253806547304c22746487300b7) (a 11 0x2605402647304ca2947737534b12937737534b1254100b146644410707703504bd0417412717304c80523706717304c40521706756717304d40417410756717304d82616187300be0523206417204ce)))))
def j22 : Tree := (.fork (.fork (.fork (a 17 0x254101b04664442243401a087650400906097737620c30707702547304c20197035637630c80247242644be0896407713104c80696407713104c80596407713104c80496407713104c80396407713104c82433231008332735141647504ce242626400b304462813507304b70157152757304c90813506747304c7) (.fork (.fork (a 15 0x242624500b6044e2947537534bf2937537534bf2907307304b42807057754bd2407057754b90784416417413104d00684416417413104d00273805867704c71787104307300c01687104307300c01587104307300c01487104307300c01387104307300c01287104307300c0) (a 8 0x2431008187650482346522757524c1081570505b6544d0307301767604cc080104a827624432087654657650cb2856587630b1060107a02352448)) (a 2 0x906097747630cb020104a70720444))) (.fork (a 9 0x754597607500c02207037734be02410089476477245d0946927647624c60657652757734c62816717314b12617307604bd1411102717304c80502102617104cc) (a 22 0x252626400b3044b230601402b3244f0976797757320c50956597767320c5081102b737534450367362767504ce0357350757604c82677467764b42647467764b42607037634b80896857657320c50796857657320c5070104a8275244d0696857657320c5060107a817514440496857657320c5040104a8072044f2854957657320c52716517314b8084654500b6044d0613307504b02726287300b0))) (.fork (.fork (.fork (.fork (.fork (.fork (a 22 0x784687623500c40784487623500c40784387623500c40784287623500c40584787623500c40584387623500c40584287623500c40484787623500c40484687623500c40484387623500c40484287623500c40384787623500c40384487623500c40374874627623500d40784987623500c40484987623500c40384987623500c40584687623500c40584487623500c40384687623500c40384287623500c40624287623500c4) (a 5 0x213500878763046213500858763046213500848763046213500828763046024500a18763046)) (a 2 0x47041647524cf060107a0233244b)) (a 6 0x251616400b3044e0857652757724c50657652757724c5240614500b6044c075665500b504430823406717204c7)) (a 5 0x2907057654bf051106a707304420607603704b80184687641507500df0184487641507500df)) (a 8 0x2474797607300cb0607602757304cd0607602747304cd0547541656644c10487024627620ce2307046644b9085501b60760446260606400b30448)) (.fork (.fork (a 14 0x2067134537530cb0711407647304cc0184787623500c60184687623500c60184487623500c60184387623500c60184287623500c6054400859750730056060107a80730441053100a737434402837733534b52745742747534c52717407604bb2717404757604cb) (a 14 0x966877643704c7073100a587630430507500757604c5050107b3076044f0897187300b60797187300b60727723324b50697187300b60597187300b60397187300b62631008787630432526287630b22377500607600c20147141647504ca)) (a 9 0x240106a7875004c030107b30760447030105b807604402947037634b40087350657650cc3434722747324cb2806707504b90407403504bd270103a7875004c))))
def j23 : Tree := (.fork j21 j22)
def j24 : Tree := (.fork j20 j23)
def j25 : Tree := (.fork j17 j24)
def j26 : Tree := (.fork (.fork (.fork (a 14 0x2606086727620c7250601402b32448241102b7466444c230103b7466444c0976797707300cf0706097757620c7013104b4075044b2507034637630c9081403b7273244b0257052757314c52616417214b32507307604b10273706767504c9061107a40710447) (a 15 0x231613400b604460966697743724c60926297757630c6080108b8375344e241102b0426444a2647037634be271451502b3244a270120104b604442707507604bc0084503743504ce0687304507500c30587304507500c32516187300b32704603617204ca2706407104b0)) (.fork (a 19 0x2205102717304cb0687104507500c40587104507500c40107102717504c92647037734b30357353754b4024100895775772456034100a8275244d0196857657320c42827246644bc0583036877634c72087634637630c12947037534b30263305757604c92426287500b00805703877304c32687474307300c82647474307300c82706507104b4) (.fork (a 9 0x50108b0375344c0407401747604c72404403417204ca012103a06753045090107b2076044b0253805747604c1045401b407504492817307504b40817306757504c4) (.fork (a 1 0x457502757304ca) (.fork (a 1 0x251613400b60441) (a 22 0x784687323500c70784487323500c70784387323500c70784287323500c70684787323500c70684487323500c70584787323500c70584387323500c70584287323500c70484787323500c70484687323500c70484387323500c70484287323500c70574874327323500d70784987323500c70684987323500c70484987323500c70684387323500c70684287323500c70584687323500c70584487323500c70324287323500c7)))))) (.fork (.fork (a 21 0x897205307300c2084101b037534440797205307300c20697205307300c20597205307300c2034100b246644442646487630b00486737534607600df040106a807204412703301038392747034637630c52401058187600422601038187600421787404307300c30677500307300cf0577500307300cf1687404307300c31587404307300c31487404307300c31387404307300c31287404307300c3) (a 22 0x210105878762041210105848762041210105838762041210105818762041210006a58762041084100b2466444a0805603867604cf0617612817304cf0605603867304c3020106b046644400084187323500c92917157654bf0617613314b30845102646817304d42403101038322406087650bd2736387520b42513207604bd2513204757604cd0613205747604cd0511307427604cd0511304867427604dd)) (.fork (.fork (.fork (a 7 0x2607037734bf2857346644bb2837346644bb2826267530b0275465500b5044c097401b807304482606407204bf) (a 16 0x51102b7375344e0084287633500c00896807613204c30796807613204c3073100a837534490596807613204c30496807613204c30296807613204c32816717514be0084787633500c00084687633500c00084487633500c00084387633500c00074674637633500d00074474637633500d00074734637633500d0)) (a 10 0x260614500b6044b0846497633604cf074774100b6044a0487324627620cb020107b207604442827237534bf2847237534bf2707504607600cb215401b7075044b064734000b50448)) (a 16 0x686053754b60386053754b62356602867504cc0745543756644c1063100b346644470674877540307300d8090406b8576544c0537532757534cd3344722757324cb021505b207604400046502757504c30713305647504c00723706717504c60687200507500cc0587200507500cc0717712817304cb))))
def j27 : Tree := (.fork (.fork (.fork (a 12 0x2487404607600c2061102b3466444b0506097763734c20347341656644c5020105b3076044b0146512757314c10107102817304cd2707507304b8210103b2426444f0147141747604ce27440095035044506400095027575045c) (a 20 0x210103a687520450966697747630c42847037734ba0801048907867204570286747544637630d4212103a6073044d0896847547630c4071104a607204420696847547630c40296847547630c4054500b237534492806067530b7250106a0876204c270104a0876204c054100b4036044a054100b4007576045a250415500b50445241614400b50449270104a807204470707703204bf)) (.fork (.fork (a 18 0x2346502757304c00186504747743104d20196507743104c2240105b042644493054701767604c4261614400b504450675574307300cc0675474307300cc0675374307300cc0675274307300cc0787404307300cf0575474307300cc0575374307300cc0575274307300cc0687404307300cf0475374307300cc0475274307300cc0375274307300cc) (a 5 0x253634400b504470307301877704cf2807307304bd0475402544507500da2826637200b6)) (a 17 0x240106b74664443070108b837534460184787633500cc0184687633500cc0184487633500cc0184387633500cc0184287633500cc2817507504b42677167764b6040107a4072044c073100a587620412631008387620410657652757324c10283206877604c4274475500b5044101550095035044a065401970675750455))) (.fork (.fork (a 13 0x2406102617104c8230107a5873004b210106a28763047083343100b7544b082103b03753445030105b307604432087354657650ca0087050657650c8050107a403504460613207504bd0201069601647504552687204507500cd0611107617204c7) (a 15 0x261651402b32448240120104b6044c2036402747304c8065714400b5044d070104a7275244e050106a7173144f2703601038310387034637630c0060107a023724422707307604b32707304757604c3065401b707504420253305647504c70523706817304cc2617404307300c3)) (.fork (.fork (a 12 0x93363100b7644c2607067764bd2347037634b80186704747743504d50196807743504c527031010383d2057053654b52346532757534c0080370104b60446091105b2076044a0613407504be0523606417204c8) (a 13 0x65704400b504400647642747304c10476797537320c02847637734b82847537534be2837637734b82837537534be010005b0536544e2947137534b82717304507500c03534702747304cf0253206547304cc0251304657527304dc)) (a 19 0x976797757300cf0956597767300cf065724400b5044c0534397533620cb0407401767604c30896857657300cf0796857657300cf0696857657300cf0496857657300cf0296857657300cf2854957657300cf0087530637630c12856587620b02406087620b32917507604b12407207604bb0184503743504c80307303304bf2813407104be))))
def j28 : Tree := (.fork j26 j27)
def j29 : Tree := (.fork (.fork (.fork (a 12 0x976797433704c50806097637520c90637632767534cb0307302717304c60176797507300ce2817607704ba2517207704b50901048927867624592616187630b20387134637630cb073323100b534480304097653300c1) (.fork (a 16 0x784187653300ce0484187653300ce0384187653300ce0284187653300ce0084587623300c40084487623300c40084287623300c42086526327320ca2516187630bf2836387620b3064401b507604420587500507500c60487500507500c60084787623300c40084687623300c42706607104b8) (a 15 0x2207067764b60427423524bf040104a8276244d020406b0576544c0853036747534c82406087520bc2407403604b42407400757604c40507501747604c40787174307300c20687174307300c20587174307300c20387174307300c21407400307300ca2407403104bf))) (.fork (a 16 0x24310087875204a241621402b3244e083100b7466444f063100b54664442053100a3875204a050107a5873004e040108b2375344f2655500766717504d404010489078672045a2857146644bd0037033634b72207034637630c32716167530bf2716417214bf2907307604b92807304757604c9) (.fork (a 13 0x2414197763704cd2046500757604c9020104a087520412907707304be2807407704bc0017013314bb2847546644b32817137534b12347137534b62706087320bd0706086647320cd0307056757314cb2807603204b9) (a 14 0x2207055656644c20707701747604c5054754100b604450487524627620c82207057654b20607603204be0184505747743104dd0196407743104cd2857053654b7084500b403604450283606877604c92826287600bf0273706867504c40143702647304c1)))) (.fork (.fork (.fork (a 21 0x250640405b6544021010387876504c21010384876504c21010382876504c21010381876504c210004a3876504c070108b23753441061102b6376344a0084787323500c90084387323500c90084287323500c90897287300b00797287300b00697287300b00597287300b03034521747624c20057052757314cf2616187600b32866687500b50084687323500c90084487323500c9) (a 10 0x184787653300c80184687653300c80184587653300c80184487653300c80184287653300c80811028937877534572806087650b22806087320b91507500607600cc0253606747304c3)) (a 12 0x2206102717304c6073100b546644470367361767604c7001701002b32440060107a807504452967057654ba2347342644ba2867055656644ca012103b6036044a0501401647504c62706607304b60253706847304c0)) (.fork (a 15 0x93100b73753442063100b7375344a0507502757304cc0476797537300cb254100a71741441060107a607304492037033534b2071403b6273244d091105b60760443025501b2076044f2457450757604c50613306867504c50611407837504c50611404977837504d50823606717204c1) (.fork (a 13 0x2236402647304c4220606400b30446220601402b32445283100a63743449243100a7475444d0257253654be0257251656644ce020107b303604420845147647604c21307300607600cb2836387500b22826437200b90146502757104c7) (a 21 0x2407055656644cd0895197657300cd0795197657300cd0695197657300cd0495197657300cd0295197657300cd0196957657300cd2407057654bd2836387600bf0687604607600c40487604607600c40685410717713304da0585410717713304da0485410717713304da0875602615307300da0675602615307300da0575602615307300da0475602615307300da0787104307300c50687104307300c53304602617104c5)))))
def j30 : Tree := (.fork (.fork (.fork (a 12 0x261616400b30446243001a0876204a083343100a6444f083153100b6344f0474877520507500dc065500a8667675045a28334310083f080610505b6544f2767054657650c0254447500b304492806607304ba2806507204b6) (a 12 0x2416186647500cf2356632767534cd2146500757604c42807307504b82617407504b32607037534bb060107a61731447050107a62732444020106a7071044b2206087650b82807307704bf030105a4032044e)) (.fork (a 19 0x210103a5876204d053100b83753445020108b0375344a0084487653300c80084287653300c8054400a96776750457070103a857654432617146644bd0687024327320c70027020327320c3091105b407604402717207304b10084787653300c80084687653300c80084587653300c80304097623300c72787104307300c00207200307300c30307300207200c3) (a 17 0x241613400b6044e210105a7876304b0746497713504c7012105b607304420084187633500c92846487600bd0027023324b30086714747743514de034100a827324420096817743514ce243100b5426444c2616517314be2716617214bc0253805847704c6250106950350441060106960164750451262626400b3044e))) (.fork (.fork (a 19 0x2536422747324c9252623400b604410784187323500c70684187323500c70584187323500c70484187323500c72607307304b80717713314bc0896407413104c80796407413104c80696407413104c80596407413104c80396407413104c8050406b3576544f260414500b604440503403504b90501501647504c92706507304b61507500307300c1) (.fork (a 18 0x684787523300cc0584787523300cc0524297523300cc0484787523300cc040106b2466444c0284787523300cc2816187600b42507307704b60784987523300cc073100a73675753456221104a60720448250614500b6044d282623400b604480283406877604c00546502757504c50744631757837504d80523206717304c52506407104b8) (a 15 0x897705307300ce0897405507500cc0797705307300ce0797405507500cc0697705307300ce0697405507500cc0597705307300ce0597405507500cc2807037734b62747037734bf0037032767534c00037032757534c00047042747534c026440095035044f2644487500b2))) (.fork (a 18 0x260610405b6544b253634500b60442251102b3466444723010681873004c230104b34664447090107b307604430746497733504ce031105b207604462617407704bf040104a7072044e2806087520b7051621502b3244e012403b02732448290614500b6044d2907507604b52907407604b2215401b4075044a27110281873004c) (.fork (a 9 0x505501757604c42837537734ba253100a7375344e2747037634b53044722757324cd3434702747304c10253606647304c93404702717304cc1712102717304c6) (.fork (a 17 0x2606054537530c0260106878730045260106848730045260106828730045260007a687300452455256757314c40706066747530c0070107a58730045220107a6072044b210105a3637644b2706067530b02617307304ba270105878730045080105a68730045270006a58730045270105848730045270105828730045) (a 7 0x785187300be0285187300be074645500b5044f2917207304b00685187300be0585187300be0485187300be))))))
def j31 : Tree := (.fork j29 j30)
def j32 : Tree := (.fork j28 j31)
def j33 : Tree := (.fork (.fork (.fork (a 21 0x2505102717304c8240310103a64448081102b83753445050310104b624480305303437604cd2867457754bf2507057654b2210107a6273244e080106a707104472467057754b80357353654b00357351656644c02087530637630c80273705767604c90684503743504c20484503743504c20284503743504c2274447500b30449271417500b3044a2606507304be0705703877304c6) (a 14 0x2356601867704c82157500757604c20946497707600c90605403647604cc0305303737304c5023104b407604430674877520307300d30184987653300cc053100a637434450087134637630c70727723524bf0707703704b42585187300b6060107a40310443)) (.fork (a 19 0x2431008787650422431008487650422431008287650420726636757200ce0637632867534cf053100a38765042223100b34664444073500a58763043091403b827324402917607604be2707207604b02507403604b01153400757604cb2707204757604c02505501747604c0054724000b5044b2917307504b50273406767504c92726637200be) (a 21 0x2607500757604c50976797707500c3030107b807604450097346647320c90084187623500c407310089378775345b2604403417204c2083100a74754442020107a6073044c280006b3577544f2737434637630cc0687020327320c3064500a717414490467461767604ca275554400b50444274554400b504442305502757504ce2706607404bc2607207304ba0801049102717204590607603104b5))) (.fork (.fork (a 12 0x204640105832250604400b504472405401747604cc0946497733704c02807607704b02707407704b02804907743504c82062403504b92717307704b40167161767604cb0723406717504c71411702717304c8) (a 20 0x250603400b604472036401647504cd093343100b654490846497627500c5060106b046644460186897613304cb2967457654b92947457654b908410089278676245b274100a8276244b2857353754b91263304757604cb0897405607600c10797405607600c10697405607600c10597405607600c12144009503504482417204507500c60253706647304cf3504602617104cb)) (.fork (a 22 0x2505102717204c9240630405b6544e0411107717204ce0407403104bf0784505747743104d40384505747743104d403410089476477245d0896407743104c40696407743104c40396407743104c4020104a807604472846747544b4050106a03353448223100a8375344d2713307704be2707407604b62707404757604c62487504607600ce20440095035044c020108b6033044d2866687300b50523806417204c9) (.fork (a 7 0x253100b346644410607602847304ce2757053754b30583536877634cf2306067530bd210105a713314422687304507500cc) (.fork (.fork .empty (.fork (.fork (.fork (a 1 0x2626287300bf) (a 22 0x784687633500cf0784487633500cf0784387633500cf0784287633500cf0584287633500cf0484787633500cf0484687633500cf0484387633500cf0484287633500cf0284787633500cf0284487633500cf0274874637633500df0784987633500cf0484987633500cf0284987633500cf0584787633500cf0584687633500cf0584487633500cf0584387633500cf0284687633500cf0284387633500cf0634387633500cf)) (a 1 0x2706406757104ca)) (a 1 0x210105b2426444b))) (a 10 0x2401068187500470897746647320c20797746647320c206410089476477245e2633231008390067062867534c5230414500b60442230414500875760452224400950350445270103818750047))))))
def j34 : Tree := (.fork (.fork (.fork (.fork (a 10 0x26110281873004c23010581873004c0786614417413104d30686614417413104d30586614417413104d30187034637630cc260601402b324400307301747604cc0805503877504cf2846487300b7) (a 19 0x230606400b30444091105b507604430736397757620c00687524327320cb0305303637604c50096587623300c12707037734b20684837536727620d00484837536727620d00896837537620c00696837537620c00596837537620c00496837537620c02834937537620c02867357754b82806087620b12717104607600c6240604400b5044a0823506717204ca)) (.fork (a 11 0x24350087876504c24350084876504c24350082876504c0707702847304cc0505403547604c10176797613304c20136847407200c9220106a70720447053500a3876504c0057052757534c72084503743504c2) (a 12 0x2205402747304cb0805403847604c2063100b6376344f0347341747604ca220104a8076044b053500b542644432657046644b02647134637630c22237033534be061761002b32442095501b207604472755502767504c9))) (.fork (.fork (a 10 0x966697727600cd0926297757600cd0475177877304c22747542644bb0745643756644cb0651547756644cb2645641656644cb0037033534be2826727524b33104702717304c3) (a 16 0x252624400b5044c2487304607600cd241102818750043230103818750043093500a78765048060104b246644402467157754b32407207704bb0184837536727620d6073100a737534430196837537620c62726267530b02726527324b23654711767614ca0307302757304c20307302747304c2)) (a 12 0x2417204757604ca2356632867534c12355751877754c9083100a737534440237233534b2284101a0675304f023723000b604452417207604ba2687104607600c90011049503504450253706747304c32506307104b1))) (.fork (.fork (.fork (a 12 0x73100b5677644e050105b3076044f2527023524bf034100a727524470187054657650c82087134637630cf2847037534b22247037534b82624722737524c02816717214b02416187500b52706307104be) (a 11 0x2307055656644cc2816187300b62307057654bc2347341656644ca090310104b604402917407604bd065401b8075044f0787601307300ca0687601307300ca0587601307300ca0487601307300ca)) (.fork (a 15 0x250606400b3044f2407500757604c91505501757604c40897605607600ca0797605607600ca0697605607600ca0597605607600ca2697287300bd2864837767200c92864737767200c90966937767200c9060107a82732447282103a0675304e0101069503504432807403104b1) (a 12 0x2614197743404c7210105a7873204a2967357654bd2937357654bd050107a40720447040107a627324482816417214b30787574307300ce2575474307300ce2575374307300ce2575274307300ce2535374307300ce))) (.fork (.fork (.fork (a 7 0x2084287633500ca2084187633500ca060106b1466444a2084787633500ca2084687633500ca2084487633500ca2084387633500ca) (a 18 0x897506307300c70897305607600c80797506307300c70797305607600c80736397757600c60697305607600c80597305607600c80397506307300c70307301647504c90896837537600c60696837537600c60596837537600c60496837537600c60296837537600c60086526327320c32834937537600c62836737534b10457500756717304d2)) (a 19 0x20767010583f2356621867724cf0897605507500cc0797605507500cc0697605507500cc0597605507500cc2844737647200c62844537647200c6210106a8276244d0946937647200c60956907757204c90357350657650c20287530637630c20537530637630c20657630537530c20637630537530c2243100a5876204b3654722767524ca1654722766837524da)) (a 18 0x906067877530cc083100b83753443080106b3466444c060107a187300400317312717504c62646487300b3220107a4072044f053100a837634462307037534b9050107a42352443010104a0233244b061403b527324402716617414ba2607407604b52607307604b60273405767604c50501102717504cd2706607204b3))))
def j35 : Tree := (.fork j33 j34)
def j36 : Tree := (.fork (.fork (.fork (.fork (a 14 0x866697433604c6080106b046644460786526327320ce0686526327320ce0057052757324ca0747742647314c8210105a4036044d293634500b6044a084664500b604480273205767604cd0273406867504c53604702717504c8210105a703304490811407747304ca) (a 15 0x2467255656644cb0897305307300c50797305307300c50697305307300c50597305307300c52467257654bb2427257654bb0386704747743504d10086747544637630d00896807743504c10696807743504c10396807743504c10096847547630c0050106a0537544f3355641656644c3)) (a 11 0x2356612867514cc0906097767320c80706097757630c50505503757304c4251102a737534412206067530b22401058503504442601038503504442807207304ba2856587300ba2806707204b9)) (.fork (.fork (a 7 0x22350081876504d0976797737500c50936397767500c50836397767500c5053100b7375344b0097746647320cf020104b60360449) (a 16 0x2506102717304cc0967156757724c6084100b2375344f075515500b504480707702817304c8047517500b3044f0084787623500ce0084387623500ce0084287623500ce2907207304b62917207604bf0701048603717504570084687623500ce0084487623500ce3504702717304ca2687104307300c8)) (a 22 0x260630405b6544e252624500b604412207500757604c60957656757724c60437432747534c50317312817304c70784416717307300df0684416717307300df034100a727324432653346644b12316167530b72726627324b12717307604b90687204507500c70587204507500c72917307304b81787504307300cf1687504307300cf1587504307300cf1487504307300cf1387504307300cf1287504307300cf))) (.fork (a 20 0x210104a287650402101038787520402056602767504cb080108b0375344d0784187623300ce0711107617304cd0584187623300ce0484187623300ce0384187623300ce034734000b50442030310104b614442817207504b0220104a807204460946907647204c52306087650bb0843636767534c60255160867427604d32605503504b80141601647504ce2707404307300ce) (.fork (.fork (a 21 0x240106878750044240106848750044240106828750044240007a687500440945347647724cf050107a387500442947237534bf2407207504bd220107a807204442927237534bf2755161867704c50684162867743504d40284162867743504d40274162764747743504e4270103878750044080103a68750044270103848750044270004a387500442701038287500442817607304b82707307304bb) (a 13 0x243100b746644432406102817304c52526287300b4241102b542644402866687320b5043100a40360442093100a403604422487104607600cf054400b703504412817407504bb0817406757504cb0160906867743504da2606507104b6)) (a 20 0x2275174307300c3213500878765047213500848765047213500838765047213500828765047024500a187650472027023324b90184987623500c30386504747743104dc0896507743104cc0696507743104cc0396507743104cc0966907767204cf0737733534b50657652757314cb2716517214b50307303704b90263805757604c61263204757604ce0253806647304cb))))
def j37 : Tree := (.fork (.fork (.fork (a 13 0x2606102717504c22287434637630c8217401b60730445063100b537634432567357654b52537357654b5060107a827524490087354657650c42547134637630c90185544747743404d12717507304be0253806747304c00523706417204cd) (a 12 0x2267055656644c70906097737520c70607602817304c5013104b7077044e2747537634b22737537634b22267057654b72416187650b72407046644b8210103a7235244c1613307504b50523206817304cd)) (.fork (.fork (a 19 0x250610405b65440060104b146644410327320527520c90237230537530c90057051656644c22277067764bf0057053654b205440085977135045e0386714747743514d10896817743514c1083100a7374344c0696817743514c10396817743514c1083100a7675304a2082403204b60687420327320c90427420327320c90253306547304c90811107717304cd) (a 18 0x897346647320c30797346647320c30785186647300c00784187633500ce0697346647320c30685186647300c00585186647300c00584187633500ce0484187633500ce0285186647300c00284187633500ce0186846647300c02417146644b52037033634be0583636877634cd3354701767604c4270415500b504432685187300b0)) (.fork (a 8 0x906097767520c6040310104b5244f2017013314be3354702767504cb0787474307300c90687474307300c92475374307300c92475274307300c9) (a 20 0x260640405b65448241102878750047241102868750047241102848750047241003a28750047230103878750047230103868750047230103848750047230004a387500470956597727600ce0926297747600ce080106b14664446051102a387500470405403647604c1040104a287500472736637434bf065515500b504471400610766717504da050106a403204422726437200b9)))) (.fork (.fork (a 16 0x2205401747604c0040107a26753041023104b80760442013104b407604412807037534b4070104890786720454060107a837534492426287650b72737534637630c92837033534b2081102a76753041080104b6036044a2507207604b02507204757604c02617104607600c83304702717304c2) (.fork (a 7 0x20105b807604442907707504bf2907407504b72817407704b32917507304b82806707304b10811207727304cb) (a 16 0x897205607600c20797205607600c20697205607600c20597205607600c2050106878730049050106858730049050106828730049050007a687300493354732767534ce2726627424bf263100818732047280603400b604462687304607600ca1404837534607600da054400b4035044f2806707404b2))) (.fork (a 12 0x223401a087650410967056757724cb076776000b304450746502757704c00506097537620ce2816187650b30057030537530c2240105808762046260103808762046095501b4076044b065401b307504470523506717304c7) (a 16 0x70108b037534460205203727304c7020104a0876204f2747137734b11307303304b9020104a8072044a040005b353654462836737434b93054711767614cf240603400b6044a2607207604b3034000b4035044d012103b603304440253606847304c30787504307300ca0687504307300ca))))
def j38 : Tree := (.fork j36 j37)
def j39 : Tree := (.fork j35 j38)
def j40 : Tree := (.fork j32 j39)
def j41 : Tree := (.fork j25 j40)
def j42 : Tree := (.fork (a 14 0x3500757604b7210104a644343407504a62587300a62856756527314c40706765647504c12957757314b42857657304be0617867414b92645547414b82705647504b10607547204b32817517304ba2747544307300c8) (a 14 0x286400b304312406756727104c90965867837604c40905987817104c52907517304be2847647614b62807817104b50947547724b42825547424b40527857324b40907877204b52806757204b52937537604b42307104a9))
def j43 : Tree := (.fork (a 6 0x3704757604bc3807604ac0956757636817304d22837637404b12617417204bf2507104a7) (a 20 0x162867504b23300607600bb3603304a12704757617304c12917767614bb2857657204bf2807617304b12807317104bd2747547304b80617857314b00957757724b92826757424b90727877424b92616717204bb0715766717204cb2614756717204cb2506617104b40605656617104c42744746717304ca2607307300ba))
def j44 : Tree := (.fork j42 j43)
def j45 : Tree := (.fork (a 12 0x1601767604b2060107b754352033734a1210107b5343e2815766757214c10975877817604c00917866757214c12957757304b82927527304b42917767214b12707527204b52406317104b4) (a 16 0x3204757604b10787630a70587630a73207604a12804867717304c62645546527314c42405866837204c60947646837214ce2947647214be2747547314b42507547204b52407867204b62907717304b60906987717304c62817417204b50816857417204c5))
def j46 : Tree := (.fork (a 15 0x2703204ae2736766647434c50905987847304c20707876757504cf2927327404b72857657634b52837767434b52837757534b52817317104b22807847304b22727324a70527657324ba2856757414b72807504ad0407847104b3) (a 10 0x240005b65438060103b654380926947527204c52927527204b52817747414bb2635537414b70607757304b02816717304b30816846717304c32714746717304c3))
def j47 : Tree := (.fork j45 j46)
def j48 : Tree := (.fork j44 j47)
def j49 : Tree := (.fork (a 19 0x2023324a83707704a52834867437604cd2726756627104c42705766757304c20936987437604cd0917856417204c82907727404b12807747404b42807427404bc2707767304b22707647104b92607847304b02937437604bd2707717404b62827627500b42847647304b00407847204bd2927327304bc) (a 22 0x2717717504b92707647304b70846756646817304da2604757637304cb2907767504ba2807517104bc2607637304bb0927877324b72826757324b70947747724b70927847624b72825747624b72727424aa0727877324b72836737324b72734746737324c72817614a70817877314b92617314ae0517657214b62967767504b50967766817304ca))
def j50 : Tree := (a 16 0x2074637630b42363764ac2087630a43033534ab204101b6043b0805977827304ce2927427304bc2707827304be2507767104be2817514a92817214a20517857314b52805547404b32706757304b60847547604b02534437433304c4)
def j51 : Tree := (.fork (a 16 0x412717304b2240104a64431043100b634352767530a12023524aa294500b6043f0806867717104ce0975877727704c12907437104bd2827627704b12737434a52816757414b72617414aa0807767104bc2807717104be2706627104bc) (a 9 0x2517817304b82734757637304cf2907417204b52837637304bf2807737404b92807327404b50807757504be2817417104b20407837104bd))
def j52 : Tree := (.fork j50 j51)
def j53 : Tree := (.fork j49 j52)
def j54 : Tree := (.fork j48 j53)
def j55 : Tree := (.fork (.fork (a 14 0x87620af0925987427704c72907617304be2847547614ba2726427214b52707437104b20637867434bf2827427704b72706427104b20507857104b12406757204bd0507747204bd2406737204bd0505746737204cd) (a 14 0x1150757604bf3404757604bd3837534ae202103b604353407604ad0956756947637304d90816866646417204d82956757637304c92705646617104cf2707404a42837437304b52527327304b10917866417204c82816646417204c8)) (a 13 0x3567764ad3542644a3040106b634312013514a80926977327504c82927327504b82907417104b22847647714b22847647504bc2707737104be2727524a30717877414b90507857304b2))
def j56 : Tree := (.fork (a 13 0x142547304b124010682a27010382a3357654a7254101b6043d0816867717204cb0907876757504c82837637504be0817737314b82715637514b22715437314b80716745437314c82817717204bb) (a 11 0x201102a644302723524ab274500b604322517717304bc2866766757504cd2726756427104c72917757214b42717517304b10847647604bc2607204a52707747304b6))
def j57 : Tree := (.fork (a 20 0x240105829260103829243100a644322603304a82854757427504c42846765647504c80947875647504c80905987817304c12927427504b42807817304b12617717204bf2607437304bb2616837214bb2807717504bd0806867717504cd2707747104b72506637204bd2716417204bf0716746417204cf2816617104b8) (a 17 0x2101038222806765647504c22806755647504c22804757427504ce0907875647504c20906987747504c22967767404b52907427504be2827327704b60927857524be2737534a10927867424be0957657724be0627867424be2826637424be2806757604b12907747504b2))
def j58 : Tree := (.fork j56 j57)
def j59 : Tree := (.fork j55 j58)
def j60 : Tree := (a 22 0x97757630b63604757604b12301038232411028232423624a63607604a12703504a32866766647304c92846756647304c90947876647304c92707627204b32507647204b40617537314b82416837214bb0947547704bc0857657604b52907717404bc2606837204b42967767304b92847547304b72927627304b12717417104b9)
def j61 : Tree := (.fork (a 13 0x3500607600b50955756947637504dd0835976947437504dd2955757637504cd2736947437504cd0a57757837504cd0837977437504cd2847547204b52707547304bf2717414a60617867214b42706647304b80507757204b7) (a 12 0x3707304a72687300a00837766757534c12837767534b10957756817304c00806877617104c52917717104b62907637604b62807617104b52717747314b42747544af2745547414b2))
def j62 : Tree := (.fork j60 j61)
def j63 : Tree := (a 12 0x2705038250787500a00687500a00387500a00287500a0010106b204330806867617204c92947647314b62807617204b92807517304b42735537414b52407104ad)
def j64 : Tree := (.fork (a 11 0x2733534a82287300ab2846756647314c00947876647314c02967767314b02847647514bf2837537304b32807817504b42807767404b42627327304bf2517214a2) (a 15 0x162767504b12402757204b20141747604b82087320a9254100b6043e2834867637604c00975877837604c00947647724b02825647524b00627867324b02626837324b02816757314b12937637604b00936987637604c02764766717504c8))
def j65 : Tree := (.fork j63 j64)
def j66 : Tree := (.fork j62 j65)
def j67 : Tree := (.fork j59 j66)
def j68 : Tree := (.fork j54 j67)
def j69 : Tree := (a 20 0x513717304b124310082a060103b754352865766717504c72646546417204cc2524867327604c72505846817104c80747546717504c52947747434b42837847434b42747547324b52727547324b52516637214ba2807604a92805647504bb2837437604bf2527327604b72845647504b62856657404b12707413104b7)
def j70 : Tree := (.fork (a 14 0x23050382920110282b27310082a3507604a42714756746717304d90816756846717304d92816756717304c92816746717304c90806867737504c62807757304b12807737504b62607727304b22866767504b82726427104b2) (a 17 0x2414756727417104d22745646617104cf2705766717304c12416757417104c22416727417104c20967766837524c00937866737524c02907647304b42827867524b02827627504bf0937637714b32726757324bc2967767524b00907877504b22806757504b20846746817304c20847646717304c0))
def j71 : Tree := (.fork j69 j70)
def j72 : Tree := (.fork (a 16 0x23010682e27110282e210005b7543a3342644a51503504a32857654207200c92846746717304c02705866837204c90956757817304cc2907317104b22707867204b92707547204b72507437104bd0607757104b90507657204bf0407647104b0) (.fork (a 12 0x3450757604b52587620ac0706766755647504d62837534207200c72706765647504c62706755647504c62847647414bd2807517204b02616527314bd2807747504b60806867747504c60407747204b1) (a 18 0x87320a32835766757534c02605646617104c40957756837324c90946867547724c92967767534b02957757324b92947547624b92937767534b02927757324b92927547624b92847547724b92837867534b02716657414b02306727104be0817767414b02716627414b02306757104be)))
def j73 : Tree := (.fork j71 j72)
def j74 : Tree := (.fork (a 12 0x3030637630b72605038242733734ae001104b104322707617304b52947547614b92706657404bf2816757514b22846647314bb0807767404bf0707877104bd2406837204bc) (a 15 0x402437204bd2805038293357754ab2403204ad0947646817104c40906967527204cf2907527204bf2847647214bf2737437704ba2507627204b32817314ac0617867314be2847547604b52927627604b22627427604b1))
def j75 : Tree := (a 9 0x2435008232807747304b30605957817104c22937437104b12807757504b42507817104b20617767314b50717637314bf2816427214b1)
def j76 : Tree := (a 7 0x2855756717304c42846546717304c42917517304b92817647514b62736757434b52827524a02817647314b1)
def j77 : Tree := (a 14 0x3400757604b61501747604b63401607600b03346644a33403604a62706756627104c80807766757104c82907717104bc2837637704b72807767104b82717317104b12607847104bd0917837614bd0607867104bb)
def j78 : Tree := (.fork j76 j77)
def j79 : Tree := (.fork j75 j78)
def j80 : Tree := (.fork j74 j79)
def j81 : Tree := (.fork (a 16 0x387650ae3246644af2233634a03037534ad202001b5143d2646546717304cd0857656717304cd0817876757514c80806867737304c62817877514b82807737304b62726757424b50417547214b82606547304be2846647304be2726527104b0) (a 21 0x1256757314b30787300a60687300a60587300a60287300a60955757817504c30906977627604c02917317104b12907627604b02717547214b90907857504b62717214ac2837537604ba2627327604b22855657504b12606527104bf2517717204b72514867717204c70615857717204c72536437204bf0307437104bd))
def j82 : Tree := (.fork j80 j81)
def j83 : Tree := (.fork j73 j82)
def j84 : Tree := (.fork (a 21 0x712717204b32855656717504c72824867327604c82724867427604ce0906977627204cc0906957427604ce0846867647604c22907627204bc2907427604be2817414a22847647604b22927327604b82727427604be0707767204bb0607867404b42606757204bb0705766757204cb0607867204b32606737204bb2714617613204c02846747304ba) (a 9 0x250106875760449250106b60439270104b604390946987647614c52947647614b52707517304b50517857214bb2835437314b00707867104b6))
def j85 : Tree := (.fork (.fork (a 15 0x210103a644342033634aa3307504a52866766617104ca0957756837524c20956867657724c20855987657724c22967767424b22957757524b22957657624b22927657624b22907547304bc2857657724b20407547204bf0847546717304c2) (a 9 0x2764766646717304d22744756646717304d20846876646717304d22865766717304c22846646717304c22804867727604c92907727604b92507847104b92736757534b3)) (a 12 0x240105a6443e271402b3243a2603704ad240105b600320807766757504c02807767504b00917876617104cd2817617404b62507767204b22707304ad0707867304b52836737204bb))
def j86 : Tree := (.fork j84 j85)
def j87 : Tree := (.fork (a 18 0x2423524a73607304a62187300a12824867427604c02705856837204c02705646617404c42707857204b02607437104be2726757524be2705547404b92927427604b02707717304bb0805877717304cb2704867717304cb2704857717304cb0307837104b20307637104bb2726627104b9) (.fork (a 21 0x240105b62039260103b620393603604a72706756427104c70956977757534c42967767434b42957757534b42957657634b42937767434b42937757534b42927727604bd2857657734b42807747104b72717647214b12637877434b42827324a60747547504bc2707717104be2654656617404c42707307300b72636437204bc) (a 8 0x2724867327604cd0836867637604c12907327604bd2817847414ba0607857304bf2837637604b12727327604bd0846646817304c7)))
def j88 : Tree := (.fork j86 j87)
def j89 : Tree := (.fork (a 17 0x74637630b43057654a63242644ae0087630a42033534a02087620a52744765646717504d90846875646717504d92907637404b42847547214b32707647204b02807204a02927527604b62845646717504c92406757104b42406727104b42407713104b8) (a 12 0x846646836417204d42845646617404c30916947437514cc0906987747304cf2917437514bc2907747304bf2517647214b32517317104b62826527314be2646547304b80416417413104c02846646417204c4))
def j90 : Tree := (.fork (.fork (a 21 0x3746644a62387500a02437200a72764766756717504df0837764746737324d32825766757324c32824857647624c30967766837324c30946867647724c30937866737324c30927875747624c32967767324b32927767324b32847647724b32817547314b32827424a22927647624b32947647624b30917867614bb2866766717504cf2636537204bd) (a 6 0x2705746717304c32405757617104ce2847547324b22807757104ba0717877314b02856757404b5)) (a 7 0x3042644aa254500b6043d2947647104bb2857657320b50617757214b70517757314b82507204a2))
def j91 : Tree := (.fork j89 j90)
def j92 : Tree := (.fork (.fork (a 7 0x2423724a42287500a02403104ab0906977647404c42907647404b42907437304ba2746757544b5) (a 16 0x2623724a4252103b604310706766756647304dd2706766647304cd2706756647304cd0807766757304cd0805977817304c42807767304bd2707817304b42707317104bd0917867214bb2816637214bb2716757414bb2416717204bd2414756717204cd0515746717204cd)) (.fork (a 15 0x3737534af3723324ab0687320a10587320a1010107b104340864767836617404d30946987747534c62947747534b62937747534b62847847534b62837434a42507304ab2817617304b50816867617304c52714757617304c5) (a 14 0x241102a644362387620a12727647324b62804967837404c80847646717504ce2907527604bb2807837404b82707417204bc0707877504b92857657604bf2645547404bb2517617304bf2816417204bd0816846417204cd)))
def j93 : Tree := (.fork j91 j92)
def j94 : Tree := (.fork j88 j93)
def j95 : Tree := (.fork j83 j94)
def j96 : Tree := (.fork j68 j95)
def j97 : Tree := (.fork (.fork (a 21 0x574607600b00374607600b0210105a644370855756836717204da2855756717204ca2835977437704c50a57757637704c50826867427604c90805877757204c92937437404b62847647434b02837647434b02747747434b02717847314b42707757204b92507737104b42847544af2845547414b20417647214b32707104a22827427604b9) (a 9 0x574307300b3010107b5043b2917767514bc2917417104b82737537304b82717517204b82706617104bf0706766617104cf0407747104b0)) (a 22 0x502757504b40500766757504c40867867656644cc2867867654bc2506766617104c40966867837404c60957756837204c30806867727504cf0717866757314c20715987867314c22957757624be2937737404b62927757624be2917647514be2907717204b02807727504bf2617877314b22717514a42717314a00507757104b82947547304b52957757204b3))
def j98 : Tree := (a 22 0x3500307300be0412417204bb2343644a0234000b50432010104b2043a0746756646717304dc0916967517204cb2947647514bd2937537304b52917517204bb2717847414be2517817204b62507747104b80907847204b02806437204b02737534607600ce2607404ad0707767304bd2606757304bd0705766757304cd2606747304bd2746646717304cc)
def j99 : Tree := (a 21 0x501747604ba201002b724322403604aa2703304a20506865846817104d12406756817104c12405876817104c10916977647614c62957757634bf2917647614b62837877434bf2817437414b62747547204ba2617877414b40717877514ba2606757104b72606727104b72807613204be0407647204bc2517417204b62736437204b7)
def j100 : Tree := (a 17 0x2053754a62587600a52717647314b92755656717504c70957656817304c50825877757324cf2967767514b32857657324bf2847547524bf2827647424bf2827547524bf2747547624bf2737437404bb2727757324bf2716637214b02527767324bf2835537414b1)
def j101 : Tree := (.fork j99 j100)
def j102 : Tree := (.fork j98 j101)
def j103 : Tree := (.fork j97 j102)
def j104 : Tree := (.fork (.fork (a 14 0x3537634a82406756527104c20976877647704c00956757427704cc0946867647704c02947747304ba2907327404bb2747547614bf2407757104b22307647104b42837534a12815547414b20907857204be2865767604b1) (a 9 0x3857654ab3307304a12837637104bc2807437404b42707637304bb2847547630b42747544637630c42746547304b32737437304ba)) (.fork (a 13 0x3300757604bb3303604ab2847747534b70a67867647724c40976877817504c70967766757704c52816757614b12737437104b72857654a62917417204b40916957417204c42736537204b52706417204b3) (a 10 0x2603204aa2826756427104c62505546527104cc2947747104b62907637504b72707847304b52607647104b12507547104bc2616757314b42616727314b4)))
def j105 : Tree := (.fork (a 22 0x2716766647314c02716756647314c02626756427104c90846867647624ce0817766757314c00805977837304cb0716757417204ce2937737104bd2907427404b62847647624be2847647104b92827767324be2817767314b02807757204b42807527204bc2707837304bb2507877104b22816757214bd2517314a82807304a42937437304b92717417204be) (.fork (a 4 0x2957757614be2947647504bd2726527314bf0807877104b6) (.fork (a 6 0x3757754a80816867817604c40907867604bb2817817604b42827527604b32745547404b3) (a 20 0x2267530ad030104b5243e241002b5243e0746765646717504dc2834857737304c42745646717504cc0967766817104cc0936957737304c42937737304b42907647504bb2847647324b02827647324b02727327704bd2517517204b52527324af0917837414b02616757414bf0907867104b30947646817304cb2857657300b7))))
def j106 : Tree := (.fork j104 j105)
def j107 : Tree := (.fork j103 j106)
def j108 : Tree := (.fork (.fork (a 6 0x3046644a7210003b634312417214a92826727314b62706757404ba2746647304b0) (a 19 0x210107b754323637634a42706766617404c72405766757104ce0916977617204c20506877647104ce0506867647104ce2917617204b22807417204b92607737104bc2635437314b60907867204ba0907847604bc2805747604bc2806637204ba2806427104bd0607767104b02947647404b02407767104be)) (a 15 0x2103b60438001106b304390947746817304c52967767644b32947767644b32847877544b32817877414b02817747514bf2737437504b12827624a70417747214be2806757104b52755657504b32507647104b22736637204b3))
def j109 : Tree := (.fork (.fork (a 8 0x142647304b80685507500b20187300a70976877837504c80936977737504c82957657304bd2937737504b82707437304b1) (a 16 0x1601647504b92253654a72406756827104c80807766757204ce0607756427104cc0506867847104c80505987847104c82907737504b22807767204be2807627204ba2607747104bc2407877104b82807404a92845747604b60607767304b62746546717304c9)) (.fork (a 11 0x161867704ba2615546527314cd0966767837404c00826867627604c30607546427104c72907437504bd2717547314bd2627324ac2856657414bc2827627604b32706317104b7) (a 13 0x1412717304b12865766757614ca0957656837204ce0955757837504c20816877647414c02967767614ba2957657204be2937437504b22817647414b02807627504bc2837634ab2506647304b52607717304b7)))
def j110 : Tree := (.fork j108 j109)
def j111 : Tree := (a 14 0x2053654ac2033434a22834757637304ce2917747514b42907767404b32836637214bd2807647404be2855757604b92727527604b80607867304b40507857204bc2937637304be0956757837304ce2637437304bc)
def j112 : Tree := (.fork (a 17 0x142747304bc26010682c27010582c3053654ab2043644a83546644a22725766757324cc0936977737514c92937737514b92847647524bc2827647524bc2727767324bc2717437314bf2627424aa0637437414bd0807877304b22756657404b1) (a 17 0x3146644a82847747434ba2764766756747534db2866766757534cb2866766747534cb2865766757634cb0965767837504c00937876757534cb0837876757534cb2967767634bb2937767634bb2837877534bb2847644a92617214a60617767214bc0517657314be2745647504b3))
def j113 : Tree := (.fork j111 j112)
def j114 : Tree := (.fork (a 13 0x2713314a50806867717304ca2517517304ba0967766837204c60937866737204c62967767104b12807847404b92707867304b02807717304ba0507757304b62947647304bf2407413104b82967767204b6) (a 15 0x74657650be0087650ae202001b314302687500a53703304ab2825766757624cb0967766757724cb0927866757624cb2967767624bb2927767624bb2907427304bb2847547624ba2817757314bb2707204ae0407547104b0))
def j115 : Tree := (.fork (a 15 0x201002b324322737747534bc0865766836717204d62865766717204c62705766757204c50947546817304cb0907865647504cb2947747514b92807877404be2716427214b62707767204b52517617204bb2637434aa0917867414bc0917837314bc) (a 16 0x141647504bb2603604a3054400b504322866766617404c82746546417204c82415766757214c80947646837204c00916867837514c10806877637404ce2917737514b12807637404be2737437514b92417767214b82707504a00706757504b02947647204b0))
def j116 : Tree := (.fork j114 j115)
def j117 : Tree := (.fork j113 j116)
def j118 : Tree := (.fork j110 j117)
def j119 : Tree := (.fork j107 j118)
def j120 : Tree := (a 19 0x151757604ba2023724a5024100b52437274400b504392403504ac2737847534b70957756837214cf0805877727304c02957757214bf2917717404b72707727304b02507517104b62865767614bb0947747704bb2606757404b80507657304bc2407204af2827427304be2306427104b3)
def j121 : Tree := (.fork (a 15 0x722757324bb22310082e2723324ab2403704ad0966867837414c70906987727504c42937737414b72907727504b42727327504ba2406827104b32706637204b90607547104b72506427104b70507847104b30746546717304c4) (a 9 0x161767604ba2353654aa3703504ae2787500a42874877727504c92845746717304ca2707427304b22607737304b00607767404bc))
def j122 : Tree := (.fork j120 j121)
def j123 : Tree := (.fork (a 17 0x210106b6343e201002b524312613614a73207304a12504867717104c62917647314be2747547214b02717817204b22707327304b52716757514bf2716757314bb2957657604be2706617404b40706766617404c42604656617404c40507647104b22507717104b6) (.fork (a 16 0x2067530a72815766757314cc2725866837324cb0947646837524cb2947747414b72947647524bb2917767314bc2727867324bb0947867644b40747877544b42846757544b42927647524bb2807104ad2706757104b72407743104b40505747743104c4) (a 10 0x2013314a90706766756617104d42706766617104c42706756617104c40406867747104c52827327304b62807547304bb2737437414b72716857414ba2607747304b0)))
def j124 : Tree := (.fork j122 j123)
def j125 : Tree := (.fork (.fork (a 12 0x485607600b60574507500bc201002b6243d0907866637204c52706857404b92837537620b10837536727620c12637437604b02717717204b20815877717204c22714867717204c22614417413104c6) (a 11 0x685307300b92745546527314cf2725546527314cf0905987847104c62847547314bf2807847104b60917837514bc0617757314b10907877304bf2806757304bf2754656617404c3)) (.fork (.fork (a 12 0x2805766757604ce0907866757604ce2907767604be2827427404bc2817817204b90927877524b30967767724b30927867624b32826757524b30727877524b32836737524b32417417104b4) (a 13 0x43100b534390587600ad0387600ad2745547424b22407617104be2725547424b20627757324b20527757324b22606717304b30705766717304c32604756717304c32604746717304c30846546817304cd)) (a 9 0x201102b534350807876757104cb2817847514b62807877104bb2807437304bd2836637204b00307537104b12826627104bb2526427104ba)))
def j126 : Tree := (.fork (.fork (a 17 0x3601307300b527350082b2874877647604c12844867647604c10946987647604c10907856437204ce0906967547204ce2907547204be2707417104b02617417104b40717877214b00907867404b42947647604b12917717304ba0916957717304ca2814857717304ca0307737104bc) (a 9 0x26350082d2235008242827527204b62807867204bd2707527304b02857656644bb0417847214b72627427304bf2967767200b2)) (.fork (a 18 0x3304757604be210106b604393307604ae2865766757604c60906967757204c30806877647104cc2807647104bc2507317104ba0937877534b62836757534b60737877534b62866767534b60957757704b32907757204b32967767604b62837537600ba2517417104bd2947647200bd) (a 11 0x28350082b0587620a10387620a12303304ae2827527304b42817617204b32807867504bf0617767414ba2835637514b32807717404b00607767204b3)))
def j127 : Tree := (.fork j125 j126)
def j128 : Tree := (.fork j124 j127)
def j129 : Tree := (.fork (.fork (a 16 0x702717304b72587630a2242001b514322947747604bc2947647434bf2937647434bf2847647314bc2817517204b72737847434bf2607647304b62526327320bc2806757404bf2807743504b32704747743504c30645546617404cf2727327304bc) (a 12 0x2101068232135008222734857437604cc0605757617104c22507617104b22947647414bc0707877204b92737437604bc0835877437604cc2734867437604cc0745646717504c42927727304bb)) (.fork (a 12 0x24100b324390874876927717504df2874877717504cf2814867717204c62506766647304cb0916987717204c60806867637504cb2836757634b12807637504bb2507767304bb2917717204b62626427104b7) (.fork (a 6 0x2087650aa2413614ac0807876757504c52907737104b92807877504b52716647314b1) (a 17 0x2631008200906987717504c42967767414b02907737604b02407517104b60607857104bd2725647524b00727767324b02626757324b00725766757324c02745647524b02626747324b00627767324b02626737324b02624746737324c02907717504b40416717307300cf))))
def j130 : Tree := (.fork (a 15 0x276400b3043f2715766717204cc0907866437204c50906977647204c52707627304ba0607657104b32826757624b20947647704b52907647204b50707647204bb2506627104b32607717104b72727427304b82406527104b92826727104bd) (.fork (a 17 0x1702717304bc210104b6043e2815646617104c82746756647304c50916977717504c80806867647504cb2917717504b82807727404bb2807647504bb2607647204bd2507877304b52416727214be2416757214be0507657104bd2827627304b12836437204b62826427104b1) (.fork (a 15 0x500756717504c73033634ab2845646617104c72806756427104c92725856837324cf0957656837324cf0947546837524cf2957657324bf2947647424bf2947547524bf2907747104b92747547724bf2727857324bf2507743104be2504747743104ce) (a 17 0x3733534a22834867737604cd2805766757204c72804867747604c02404867717104ca0907866757204c70906867847604c02907747604b02807437104b82727427204b62707767104b00517757214ba0967767704b72907767204b72937737604bd0407637104b12407717104ba))))
def j131 : Tree := (.fork j129 j130)
def j132 : Tree := (.fork (a 15 0x210105823010104b6043d3707504ab0916977647414c92917647414b92907657204b12907617204b22817617104b42727527304b42606537204b70957657704b12706757204b82747547604b52846547304b52816317104b5) (.fork (a 11 0x10106b6043e2807647304b82727327404bd2817743514b22714747743514c22715547414b62756657414bd2706757504b60607757204b82836537204b42826527104bf) (a 17 0x2301058222611028222063764a0284400b504390874877836717504d82917767414b12907757604bf2727527204bb2527327504bf0837637614b02636757434bf0637767434bf2736647434bf0717867314b30807747204be2706437204be0706746437204ce)))
def j133 : Tree := (.fork (a 22 0x4101b604343807304a82603104a12756857644be2746765647504c22724757427504ca0807876757304cf2807877304bf2715537414bc2616727214b82626757424bf0627767424bf2726637424bf2616757214b82516647314bd0707877404bb2947547604b90707877304b52607304a22827427504ba0746646717304c12626527104ba) (.fork (a 9 0x202001b614392717617204b90854756927617304d82854757617304c80617547214b22516427214b22737537604ba0755656717504c22616317104bd) (.fork (a 7 0x947646837324c02947647324b02927647324b02835737614b52607317104b92507527204bb2407817104b6) (a 17 0x3237534ac2814757617304c02756656527314c40967766837214c92967767214b92957757604bc2857657314b42807547104b72736857434b42836757434b40737877434b42856757434b42607104a02845547404b22917617304b02406817104b50505846817104c5))))
def j134 : Tree := (.fork j132 j133)
def j135 : Tree := (.fork j131 j134)
def j136 : Tree := (.fork j128 j135)
def j137 : Tree := (.fork j119 j136)
def j138 : Tree := (.fork j96 j137)
def j139 : Tree := (a 1 0x874866947436717504e1)
def j140 : Tree := (.fork (.fork (.fork (a 18 0x986877836717504d60986867836717504d60976867836717504d60876867836717504d62874867736717504d60985947826717504d60976937426717504d80876957426717504d80876937426717504d80986947326717504d60876947326717504d61874767836617404de0876866757727304df1766754846817304d50866756646817304d51874857826717304db2874857626717304db2755646626617104d5) (a 9 0x876866756727514dd1874856847437704df0876756746817304d20654637632717304d70644637632717304d70986857646817104df0876867436617104dc0856847436617104dc2755646426617104de)) (.fork (a 20 0x875766756837524dc0875757726717504d70876867426717504d70876837426717504d72764757426717504d70866837426717504d71874957726817304db0976837626817304db0956837626817304db0876756846717304d20764757636717304da0866857626717304da0866837626717304da0856837626717304da0986946827617204d30876946827617204d30876866857647104d30876867646727104d30766756426617104dc2654646426617104dc) (a 8 0x766756646727314d61874866947437604d11874856947437604d10986876867837504da0876866756717504d50876866646717304d40754647642717304d40644437432717304db))) (.fork (.fork (.fork (a 14 0x985857836717504d80985957836717504d80975957836717504d82874867436717504d80976947436717504d80876947436717504d80866947436717504d80856947436717504d80875957836617404dc0766947436617404dc0766756646717304d10865756836717204d00766756726617104d90856736827417104d8) (a 13 0x987864857647624d21877754746737324d20766755646717504df0985767836717504d70764757426717504df0986757836717304d91874867836717304d91874857836717304d91874957836717304d90764756827617304db0766756646417204db0766756646427104d52876755646617104d2)) (a 9 0x876866756747534dd0985877836717504d60976947636717504d60876947636717504d60876756837627304df1764756836717204d70876756726817104dc2754846426817104d80876536827617104d1)) (.fork (a 14 0x875547426717504df0865547426717504df0865757426717504d10876537326717504df0875757326717504df0866537326717504df0654747742617404db1874857736817304d30744637632817304da0864956927717304d10864957836717304da0856847436627104db0876867746617104d42766755646617104d4) (a 11 0x876866757427604d80986975957837504d40976866947437504d40976856947437504d40876866947437504d42874856847437504d40874867836717504dd0876757426717504d71876864957837304d70987656836717204d80856847436527104d3))))
def j141 : Tree := (.fork (.fork (.fork (a 16 0x876867647614cd0876857647614cd1876846527314c82756846527314c80975867837604c92977426717504c50877526717504c80767526717504c82957426717504c51857826717504c51757826717504c52937426717504c52744617613304cc1767644307300c01766536717204c01967746817104cb) (.fork (a 9 0x876867637404c11977636817304c22757636817304c22986857647104c12976857647104c12877646827104c12857646827104c11987846627104c12987746627104c1) (a 14 0x1754747743704c30865757737504c30876867437504c30856847437504c30987857727504ca2875757727504ca2865757727504ca2876867427504ca2876837427504ca2866837427504ca0876846717304ca0756846717304ca2744717713304ce0877756637204cf))) (.fork (a 6 0x2655546527314c90644437433604c32657314507500c70327320507500c70a67757837304ce2756947437304ce) (.fork (a 19 0x877756747534c52766756647434c50655546637424ca0a87877637704ca1976847637704ca1987836717504ce2987736717504ce2987326717504ca2977736717504ce2977326717504ca2877836717504ce2867836717504ce1947826717504ca2947326717504ca2766655547404c10966947327404c70876747717204c80866747717204c80646426617104ca) (a 8 0x645536627414c71975757837504c01875957837504c01766947437504c01987836617404c82977736617404c82877836617404c80966947527204c5)))) (.fork (.fork (a 21 0x876836727214c30975957837604cd0986947437604cd0866947437604cd0856947437604cd0977547627604cc0967547627604cc1875547427604cc1876537327604cc0977757327604cc0767426617404c10757426617404c11966757837304ca3764957837304ca3864757637304ca0956947327304cc1766436717204c40867646717204c40857646717204c40846836417204c41766756727104c4) (a 21 0x876746837324c70877726717504c60867726717504c62766756617404c31876646817304ca1866756817304ca1866746817304ca0977626817304c21766756817304ca3764846817304ca2766646817304ca2756646817304ca0957626817304c20876867647204c30857646737204c31766756437204c31876947717204c92877646617104c40656526617104c02857646617104c43746626617104c4)) (.fork (a 10 0x646636427214c40967757427604cc0646637433304c41977826717304cd2977626717304cd1877826717304cd2957626717304cd2646615307300ca0747742817104cf0636626317104c9) (.fork (a 12 0x766756637214cf0766636727214cf0986837627704c10976837627704c10a77757837404c02875957837404c02975757637404c01956947637404c02766947437404c00767326617404c01876756847304cf2876756747304cf) (a 17 0x856847437514c40847436727514c41965757837504c21956947437504c21756947437504c20876867637304cf2764757637304cf0856847637304cf0756847637304cf1876867727304c61876857727304c62876757727304c62866757727304c62866857627304c62866837627304c62856837627304c61967646837204ce)))))
def j142 : Tree := (.fork (.fork (.fork (a 15 0x866856647434ce0766756647314c80766646727314c80986837427704ce2864957427704ce0956837427704ce1976757837304c31976947637304c32756947637304c30856847437304cb2644437433304ca1766715207200cd1846815207200c40747742617104c00946937317104ca) (a 17 0x976867647714c20976857647714c20876867647714c20986867727704c80876867647504cc0976947327504c80987537717504c80867537717504c80957326817304cd0427420307300c12877436617104cf2867436617104cf1857736617104cf2857436617104cf1757736617104cf2847436617104cf0436426317104c4)) (a 20 0x1876865837714c41764637633704ca1744637633704c50986837327704cb1876866757504c62876766757504c60876867847504c10986977747504c12876755647504c10876867637504c80976937427504c10756937427504c11876756817304c01876746817304c02756746817304c00957426817304cb2756927417204c80866826617104cb3755646617104cf3746426617104cf)) (.fork (.fork (a 18 0x987757627604c10977547527604c30967547527604c31876757427604c11865547427604c31866537327604c31766756847304c90987866747304c91876866647304c92866756647304c92754647643304cf0976757827304c10867726717304ca0857726717304ca2654417507300c90986927717204cb0866927717204cb1756436717204cb) (.fork (a 8 0xa87757837504cd1956947637504cd1756947637504cd1976947437504cd0867437617304c53624617613304c80976947627204c20546637427204c1) (a 16 0x1766756747534c11876866757514ce1876866727514ce2876756727514ce2866756727514ce0647641507500c70856847437404c62866837427404cd1876546817304c00967756817304c01856746817304c00967526817304cc3754846817304c00957526817304cc2757436817304c71767746617104cd))) (.fork (a 8 0x977646827314c61764747743704c00975957817604cb0a87847817504ce1766756637204c80866847717204c60986927717104cb0536526317104c0) (.fork (a 17 0x876867647514cf0877646727514cf1766756847314c01866756827314c01766756827314c02766646827314c02756646827314c00877626717504c01766756647304ca0967737717304c80757632717304c30747632717304c30637632717304c32654407537300c32644407537300c31656646307300c31766636717204cc) (a 17 0x1985857737704cf0967757737704cf1976867437704cf1976857437704cf1976847437704cf1876867437704cf1874867837604c00986947637604c00876947637604c00866947637604c00876866717504c82764756717504c80747742827104c61987646817104c92877646817104c92857646817104c93746626817104c9)))))
def j143 : Tree := (.fork j141 j142)
def j144 : Tree := (.fork (.fork (.fork (a 21 0x1985877837604c71976947637604c71876947637604c70866857437604cf0866847437604cf0856847437604cf0865547427604c70866537327604c70987866717504c72875766717504c70877546717504c51765646717504c51765746717504c50757546717504c50867747527304c40746736417204c62646536417204cc2546636417204cc1646426617104c52756527317104c32736527317104c3) (.fork (a 1 0x766727517204c5) (.fork (a 16 0x1875766757724c02875766757524c00977766837524c01866756837524c01766756837524c00756746737324c62654637633304c92644637633304c90876746817304c12754846817304c10877646717304c00867646717304c00857646717304c00846817713304cb0876827617204cd0866827617204cd) (a 9 0x876837627504cf2656615507500ce0537530507500c80956917407200c42766426617104c72765646617104c72756426617104c72755646617104c71646726617104c7)))) (.fork (a 17 0x757751647504c82654747743404c30976757817304cc2876756717304c01876846717304c02876746717304c01877726717304cf0877636717304c12756846717304c02867626717304cf0867636717304c12857626717304cf0857636717304c10757636717304c12837626717304cf1856836417204c01877754207200c9) (a 21 0x2875766757534c10987866747534c10967756837324c31856746837324c33754746737324c30876867647414ca0866837733504c52764737733504c50867547427504cf1756537327504cf0875757717504c50865757717504c50877536717504c41756747327404ca0847732817304ca2766547527204c72546737527204c70756747417204cc2756415207200ce2746415207200ce2867534207200ce))) (.fork (.fork (.fork (a 12 0x866646827314cb1754437433704ca1654747743504c22756537327304cc0876757717304c70866757717304c72646436417204c00876837617104c60876827617104c61766756317104c22756626317104c22736626317104c2) (a 12 0x876867647214cf1766756427214cf2766646427214cf2756646427214cf0986977627604c20866637427604c11755646717504c42627414307300c60977646817104c41846626817104c40866827417104c40856827417104c4)) (a 10 0x876867637704cf0877547527504cb1766715507500c92876546717304c12865756717304c13754746717304c12856546717304c11756846717304c10947436827104c22436626317104c9)) (.fork (.fork (a 15 0xa97947717504cf0a87947717504cf0987947717504cf2986827617204cf2976827617204cf2946827617204cf1656644207200c81876867747104c22876867647104c22876857647104c22866857647104c22877646727104c22867646727104c22857646727104c22867746627104c2) (a 10 0x2647314607600c41987626817304ce1977726817304ce1877726817304ce2857626817304ce2837626817304ce1766546717304ce0867656717304ce1756646717304ce3654746717304ce)) (a 20 0x876866727514c22877426717504c60877436717504c80767432717504c72867426717504c60867436717504c80757432717504c71857726717504c60857436717504c81757726717504c62837426717504c62877426617404cb0767436617404cd1757726617404cb2654617613304cd2644617613304cd0766727517304cd0756727517304cd0756727417204c71646526617104c0))))
def j145 : Tree := (.fork (.fork (.fork (a 19 0x1764747743714c30986977647614cb0845436827314c10876867647604c40876857647604c40866857647604c40a97767837604ce0975947827604c00876757427604cc0866757427604cc0986947327604c00866947327604c02875656717504ce0977856717504ce0877856717504ce0876836717204c80756836717204c82646415207200c92546737317104c6) (.fork (a 18 0x766756747534c71874967757724c42875856837524c40967756837524c41756747327504ca0987866717304c52876646717304c53764756717304c53764746717304c52866646717304c51766846717304c50867546717304c40857642717304c00847642717304c00857546717304c40647642717304c01876866617104c42766826617104c4) (a 11 0x745636727514c42764637633604c30a87857827504c92865757827504c90a97957727504c92985757727504c90987957727504c91986957427504c93874757427504c92876957427504c92876937427504c9))) (.fork (.fork (a 13 0x766756737524c70986957427604c80866957427604c80866937427604c81767634507500c62767534507500c62657634507500c61766646717304cb1867726717304cb0867536717304c40857536717304c40657536717304c41846426817104ca) (a 11 0x1986877837504cd1986867837504cd2876867837504cd2976867737504cd0a87847827504c92985947827504c91986947327504c92876947327504c90846837733304c41976847817204cb0866837717104ce)) (.fork (a 14 0x976967757534c40977856747534c41876866647434c42766856647434c40656646527320c11546534327320c12766756647314c11766756727314c12766646727314c12756646727314c10986857437704c50856847437704c53656544507500cb0766756617404c4) (a 11 0x876867637604c10876847637604c10866847637604c10875747627604cd0876747327604cd0866747327604cd0766756717504c90866646817304c70866857717304c10876817607200c01646626617104c4)))) (.fork (.fork (.fork (a 16 0xa97757837604c11985857837604c11985957837604c10977757837604c10967757837604c13874867437604c13874857437604c11976947437604c11876947437604c10537530607600ca0987846717504c92875646717504c92875746717504c90877846717504c90867846717504c91846526817104c8) (a 13 0x876867727504ca2865646617404c30767846617404c30956927417204c32866646417204c41866836417204c42646836417204c42546436417204c33644617613104c31756727317104c02546727317104c02756526317104c52736526317104c5)) (.fork (a 17 0x1876865847724c60986857647724c60876867647724c62874857647624c60987866747324c61866756837324c61866746837324c61766756837324c63764746737324c60857546737324c50654637633604cf1876866717504ce2876766717504ce2876756717504ce2866756717504ce1646615207200c00426417413104c2) (a 7 0x1767644327320c53646534327320c50856847437414c20877636717504ce0867636717504ce0866827517204cd0977646827104cb))) (.fork (a 12 0x2527314607600c01967726817304c40867436717304cc0757432717304cb0857436717304cc0747432717304cb0437432717304cb2766615307300c80856847417204c20986837817104cb1876537717104c71856737717104c7) (.fork (a 9 0x986977747534c60986957747534c60977836617404c30967836617404c30767836617404c30867747627304c62756747327304c62646636417204ca0956537817104c0) (a 14 0x976947437514c30877646717504ce0867646717504ce0857646717504ce1976857827304c52876757827304c52986757727304c51876957727304c51986957627304c52976857627304c52976837627304c52956837627304c50756715207200c30846837317104cd)))))
def j146 : Tree := (.fork j144 j145)
def j147 : Tree := (.fork j143 j146)
def j148 : Tree := (.fork (.fork (.fork (.fork (a 8 0x966947437404c32865756717204c51856836717204c51756836717204c51986947617204ca2976847617204ca2876947617204ca1746715207200ca) (a 15 0xa87757637704c20866837427604c41767624607600cf2987436717504cc2977436717504cc1957836717504cc1857836717504cc2947436717504cc2876757417104c71876827417104c72876727417104c72856737417104c72856727417104c72756837417104c72736827417104c7)) (a 10 0x1764747743724c62967436617404c31957836617404c32947436617404c30756747537304c80a67947617304c80867947617304c81757624307300c20967546837204c42956727417204c8)) (a 21 0x987867656644cc0987547727504ca1865847727504ca0957547727504ca2875547427504ca2865547427504ca0867847427504ca2855547427504ca2876537327504ca2875757327504ca2866537327504ca2865757327504ca1756837327504ca0876867717504c00656615507500c00876827617404c50766827617404c50867826717304c80857826717304c80967756837204c31756947617204cd)) (.fork (a 14 0x2767534607600ce0966657837304c53760846817304c51766756717304cc1766746717304cc2766646717304cc2756646717304cc0867626717304c40857626717304c40756436717204cf0746436717204cf2766756617104ca2766726617104ca2756726617104ca) (a 19 0x876867547524cf3654746737324cf0745436727314c21644637633604ce1746715607600c62865757427504ca1756837427504ca0877756717504cf2765656717504cf0765657637404c70987757727404c52876757427404c51856646817304cb3654846817304cb0547540307300c10757546637204c40986947717204c40866947717204c40756736717204c9)))
def j149 : Tree := (.fork (.fork (a 20 0x1767644637630c90876757547614ce1876865847704c00986857647704c00976867647704c00976857647704c00976757427704c80754647643604c80986957747304c42876757427304c31876837427304c32756837427304c30756536717204cb0876867617204cf3856646417204c53656846417204c50876867637104c92876756727104c82765636627104c92745636627104c9) (.fork (.fork (.fork (.fork .empty (.fork (.fork (a 20 0x1987865847724c22977765847724c22985967647724c20a77867647724c21966857647724c21986757547724c22876757547724c21987865747624c20a87967647624c23864857647624c22976757547624c21976967757324c21876967757324c22987656747324c21977856747324c21977756837324c21877756837324c22867656837324c23656746837324c21977856737324c2) (a 7 0x767736617404c71987846617104c42987746617104c43875646617104c42977746617104c42877846617104c43746826617104c4)) .empty)) .empty) (a 3 0x876867747534c30987766757704ca0976947637504c6)) (a 12 0x877736717504c90877326717504c50867736717504c90867326717504c50957636817304c70757636817304c70756717307300cf0746717307300cf0987846727104c61876846427104c62756846427104c62766526617104cd))) (.fork (a 19 0x876867647624ce0876857647624ce0866857647624ce1766756747324ce1766756737324ce1766746737324ce0846836427214c81655546617404ce0956947437304c91977836717304ca1877836717304ca2757836717304ca0876867647104c92865836827104cd0877646727104c91766756427104c92766646427104c92756646427104c90836826317104cd) (.fork (.fork (a 4 0x2765546617404ca2765646617404ca0767746617404ca2755646617404ca) (a 21 0x766757537320c01656646327320c02865847727304c80967847627304c81846837627304c81876867327304c82876757327304c81876837327304c82866757327304c82756837327304c80876867617304cc0876827617304cc2764757617304cc0866827617304cc0856827617304cc0756827617304cc1546534307300c11766756417204ca2766646417204ca2756646417204ca2646736417204ca)) (a 17 0x537530627620cb0876867647324c10857646737324c10877746717504c90877426717504c50867746717504c92765646717504c90867426717504c51767836717504c62755646717504c90757426717504c50986857837304c92864957837304c90977646817304c70957646817304c72756947417204ca1876626817104c9))))
def j150 : Tree := (.fork j148 j149)
def j151 : Tree := (.fork (.fork (.fork (a 17 0x876846727314cc1975757637704c11764437433704ca2644437433704ca0956537327704c31757624607600c50976967647404c10766756647304c00766717507300cc0766636717204c40756636717204c42876715207200c10987746817104cf1876426817104cf2865846817104cf2756426817104cf1846726817104cf) (a 13 0x987757727504cf2865757627504cf1756837627504cf2876757427504cf3426615507500c30987746817304c52865846817304c50957746817304c50766756637204c31876756817104c91876726817104c92756726817104c92766626617104c4)) (.fork (a 15 0x976867837504c00876867837504c00977856647304ca2644737733304c50957736817304c50857736817304c51756746717304c32756546717304c30867526717304cb0857526717304cb0657526717304cb0856847437104c40847436727104c42755436427104c42745436427104c4) (a 16 0x987866757614c50866856627414c80986867747704c50866837627604c60976947437504c52754437433504c42987636717504c61977836717504c62977636717504c61877836717504c62947636717504c60966947637404c00957436817304ca0866827517304c30856827517304c30656827517304c3))) (.fork (.fork (.fork (a 13 0x527520507500cc0976757837304cf0956947637304cf0756947637304cf2656837427304c50986857817304c92864957817304c92876537617104c62865757617104c61856827617104c61756837617104c61756827617104c62536827617104c6) (a 13 0x966637427704cf0956637427704cf1985857827604c20a97957627604c22985857627604c22986757427604c21976937427604c21876957427604c21876937427604c20867736717304cb0867326717304c70857736717304cb0857326717304c7)) (a 19 0x987766757734c70987866757634c71876866757534c71876866747534c72876766747534c72876756747534c72866756747534c70876867647524c80857646737524c80976867837514c21766756717504c80957547727404c02865547427404c02855547427404c02866537327404c01866646817304c40957536817304c60866547717204cb0856547717204cb)) (.fork (a 11 0x987766757724c71756746737324c50867746717304c70867426717304cf0857426717304cf0515647507300ce1656615307300c41866756837204cc1766756837204cc2766615207200cb1876866627104c2) (.fork (a 21 0x986977747514c90987846727514c90a97877837604c61976867837604c61876867837604c63874867737604c61985947827604c20a97947627604c20a87947627604c21876947327604c21644737733504ce0977826717504ca0877826717504ca1656837427404c80967546817304cb0957546817304cb0987866717204c63764756717204c61866836717204c61766836717204c61876526817104cd) (a 11 0x1876866617404c83764656617404c82766856617404c81876757727304cb2876757627304cb1876837627304cb2756837627304cb0967847527304c40977646837204c02756546417204c82546736417204c8)))))
def j152 : Tree := (.fork j150 j151)
def j153 : Tree := (.fork (.fork (a 21 0x967756837214ce0986977727504c71767426717504c00987726817304c10957726817304c10987846717304cb1877426717304c90756546717304c10867846717304cb2855746717304cb1857626717304c92757426717304c90527520307300ce1976927717204c01876927717204c02767526417204ce2757526417204ce2737526417204ce2877746617104c52867746617104c50746737317104cc) (a 21 0x977646837524cd0756437433604c60746437433604c60746737327500c61646615507500c12754747743404ce0866857737304cb0847632817304ca0637632817304ca0987836717304ca1877326717304c80867836717304ca0957836717304ca0857836717304ca0846817613304ce1657514307300ca0956947417204c11876815207200cd0876726817104cd0846426817104c80736726317104ce)) (.fork (.fork (a 19 0x2767534627620c21866837427604ce0986867817604c61857426717504cc1757426717504cc0866856617404c70986957717304c20986927717304c20866957717304c20866927717304c20956927717304c20856927717304c20756746717304c70756717613304c90746717613304c90546536417204c70866817407200c50856817407200c50856526817104c0) (a 10 0x766756837524cc1976867737704ca1876867737704ca0a87847627704c20856546817304c60987837617304c50867837617304c53546534307300c12877646427104c92857646427104c9)) (.fork (a 21 0x986977647604c22874867647604c22874857647604c20865647643604c80855647643604c80a87877837504c52976847637504c52876947637504c50657742617404c90747742617404c90656637427304cf1977736817304ca2757736817304ca2757326817304c20966947517204c31876867437104c92867436627104c91857736627104c92857436627104c92847436627104c90756537617104c1) (.fork (a 15 0x876866747534c61766756647314c62755436527314cf2745436527314cf0a97757727704c11985957727704c10a97857627704c10a87857627704c11956837627704c11986757427704c13874957427704c12876757427704c10987866757604c61746715507500cf1757326617404c0) (a 8 0x1857326717504c51757326717504c51547426717504c52537326717504c50966927517304c80956927517304c81756736717204ca0747742627104cc)))))
def j154 : Tree := (.fork (.fork (.fork (.fork (a 8 0x976967647434cf0876867647314cc0986867847604cc0766637433604cc0756637433604cc0655546617404cf0756747327304cc0646636417204c0) (a 22 0xa87967747514c70976967647414cc1764737733704ca0875757637604cc0865757637604cc0977757727604c30977857627604c31856837627604c31876867427604c32876757427604c31876837427604c32866757427604c32764747743504c80765646717504c40755646717504c41644717713504c80986957727304cb2987656717204c43656836717204c42846415207200c60747742427104c20866626817104c4)) (.fork (.fork (a 20 0xa97857837504cc1985757837504cc0a87857837504cc2985957837504cc2975957837504cc2875757837504cc2865757837504cc2985857737504cc2986857437504cc2976867437504cc2976857437504cc2976847437504cc2876947437504cc2866947437504cc2856947437504cc1865947827504c20a57547827504c21956947327504c21756947327504c21987656837204c2) (a 5 0x986977717504cf0986927717504cf0976927717504cf0876927717504cf0866537717104c4)) (a 5 0x755646737524c11876866627414c11986767837404c52876947637404c52657426717304c5))) (.fork (a 10 0x2764437433604cc0a87947737504c01747624507500c12737324507500c11877626717304c91867326717304cb0646615307300cf1766756737204ce0846837627204c60866827317104c2) (a 21 0x976757547724cd0966757547724cd1865646837524cd0967546837524cd1766755437314c70986867837604c70766637427504cb0756637427504cb1767624507500cb2657624507500cb0877726617404cb0767726617404cb1766756747304ca2766756647304ca2744637633304c30876757727304c21766756717204ce1766736717204ce0866827417204c80856827417204c81646826617104cd))) (.fork (a 15 0x766756647434cf0876757547604ca0876867737504c40876867327504c40876837327504c40756537327504cf0987836717504c30977836717504c30877836717504c30867836717504c30746737527204cf0976947617204ca0537530207200c90756727417104c60546537317104c2) (.fork (.fork (a 15 0x876867747504c92766755647504c91985767837504c60876867427504c50876837427504c52764757427504c50756837427504c52877646627104c72857646627104c72867436527104c01857736527104c02857436527104c02847436527104c01546526317104c02436526317104c0) (a 8 0x766756637424cf2764747743514c90766646717304c00756646717304c02644717713304c40766756617104cf0766726617104cf0956927417104c3)) (.fork (a 21 0x876747537604ca1877426717504c00765656717504c21857626717504c01757626717504c02757426717504c01986757837304c41976867837304c41976857837304c41876867837304c43874957837304c42876757837304c42866757837304c43874857737304c42865947827304c00a67947627304c02756947327304c00976927617304c80956927617304c80756927617304c80747742527104c0) (a 6 0x877756647314c91766756527314c92766646527314c92756646527314c91866756837214c31766756837214c3)))))
def j155 : Tree := (.fork j153 j154)
def j156 : Tree := (.fork j152 j155)
def j157 : Tree := (.fork j147 j156)
def j158 : Tree := (.fork (.fork (a 20 0x747743714bf3546727514b32655547414b81546627414b83876527314b42967757314b43756847314b43756827314b40747743504b41647433504be2437433504be3526717504b41877757304be3766547304be2867657304be3756647304be3656747304be3614307300bb3656717204b02415207200b2) (a 21 0x967547724b41856837324b41877747614b62877647614b62867647614b62857647614b62987537604b41967837604b40867747604b71867837604b43614607600b71747607500b01987847404bb2987747404bb3875547404bb2967747404bb2967427404b72867847404bb2957427404b72937427404b71857707200be)) (.fork (a 10 0x2767433504b32757433504b32877637404b12867637404b12767737404b12847637404b13754207200b73987647104b13977747104b13877847104b1) (.fork (a 9 0x877717504bd0867717504bd3857727504b53876757404b82876717304b52846717304b52757547304bc0847727204bc3766527104bd) (a 14 0x967757724b41857743704b92877437504b92867437504b91857737504b92857437504b91757737504b92847437504b91877757204bf3766537204bf2867657204bf3756637204bf3656737204bf2727413104b5))))
def j159 : Tree := (.fork (.fork (a 17 0x737733704b01977817604b01877817604b00867437604b23767427604bc0857437604b23435607600b63747717500bd3324507500bc3655547404bc3876547304b82967757304b83856747304b82967527304b43756847304b82957527304b43757837304bf) (a 9 0x2757547314b43646527314b42977647214be3646837214be2987643604b00757433604b10437433604b13320507500bb1437307300b9)) (.fork (.fork (a 9 0x757547524bd2655547424bd1646637424bd1546637424bd3877637704b51877717204b42747717204b41646617104b52426617104b5) (a 19 0x1877757634b22867657634b22877757534b23756747534b23766757434b21866837524bd0746737324b30867737604bb2877647404b03765547404b02967327404bb2867647404b02767747404b02857647404b01947827404bb2947327404bb3537717404bf0846817304be0637633304b6)) (a 12 0x3764537530b52534327320b62645537414b71636627414b71536627414b72756727314b63967437504b03755647504b32967527204b51957817204bb2947527204b52547817204bb)))
def j160 : Tree := (.fork j158 j159)
def j161 : Tree := (.fork (.fork (.fork (a 19 0x867537604b03757327604be3547627604be1877727500ba2757727500ba3625507500b92877647304b03967637304bd2867647304b03767837304bd2957327304b62857647304b01947827304b62947327304b62846417204ba3646717204b22836417204ba3766757104b23766727104b2) (a 15 0x1846837324b62757437314b61876837214b92876727214b92756837214b92836727214b92987437604b61957837604b61857837604b62947437604b62527317600b31757547504bc3426617404b00617613304b13626417204b1)) (.fork (a 6 0x3726717504bb3766817304bd3626817304b90717713304ba1656617104b82526617104b8) (a 21 0x987747724bb2865847724bb2876747324bb1876837324bb2756837324bb2746837324bb1987867504b22977767504b22877547504b13765647504b11767747504b13947437504b21847727500b42837327500b43977717204bc2877647204b13766437204b11967817204b92867647204b12857647204b13646737204b1))) (.fork (a 20 0x1977767714b73865837714b90747743514ba1646637214b42646427214b42636427214b40867547604b03855747604bd3757427604bc2877537504b31767737504b32957427304bc2647433304b42637433304b42937427304bc0617613204bf3742817104bf1836827104b22636317104b92626317104b9) (.fork (a 19 0x2644537530b11977647714be1766757214bf2766637214bf1766727214bf2756637214bf2636727214bf1987627704b11977727704b11877727704b12837627704b10537533600b52715507500bf3957637404b03757837404b03326617404b03876757304bf3876747304bf0647643200b8) (a 14 0x2867437514b41857737514b42857437514b42847437514b43436727514b43957437504b22877637304bf3877727304b62867637304bf2857637304bf2757737304bf2847637304bf3967647204be3767847204be))))
def j162 : Tree := (.fork j160 j161)
def j163 : Tree := (.fork (a 12 0x2867547614b51766757314b62766647314b61766727314b62756647314b62646727314b62876757604be0867827604b42647317600b03654507500bb3535307300b23742617104b8) (a 15 0x977857534bf1866857434bf2866647434bf2856647434bf2756427214ba1987427704b32867427704b31957727704b32837427704b30656617404b72757433304b22747433304b22987707200b12947317104be2937317104be))
def j164 : Tree := (a 18 0x3534627620bc0877637604bc0867637604bc3635607600b00766717504b40756717504b40717713504b83977637304b92867437304b50867717304bc1857737304b52857437304b50857717304bc2847437304b51547427304b12537327304b13765307300b30747743204b7)
def j165 : Tree := (.fork j163 j164)
def j166 : Tree := (.fork (a 19 0x1977747714b92877647714b92867647714b92857647714b91987727704bc2867727704bc2977327504b42877647504be2867647504be2857647504be1947827504b42947327504b43537717504bc1977817204b62747817204b63765207200be0867717104b92436317104b22426317104b2) (a 9 0x767763734bb0766757524b13634507500b00747743304b53326817304be3656647300b03420307300b03737417204b73967747104b4))
def j167 : Tree := (.fork j165 j166)
def j168 : Tree := (.fork (a 20 0x767763724b71977737714b23875837714b21877633704b50877647604b91967817604b70867647604b90857647604b93645607600b13314607600b43876767504bb3876757504bb2877637504bc2867637504bc2847637504bc2647307300b81316307300bb2644207200bb2867747104bf3746727104bf) (.fork (a 12 0x1847633704bd1987847504b82987747504b83875647504b82977747504b82977427504b42877847504b82867847504b82957427504b41757827504b42937427504b41847707500be) (a 15 0x766757534b11856837524be1987327704b62867327704b63767737704bd1847727704b62837327704b61987867404b53876657404b53766857404b53426817304be1867717204bb2647717204bb2866617104be2826617104be)))
def j169 : Tree := (.fork j167 j168)
def j170 : Tree := (.fork (.fork (a 4 0x967547704be0647643704ba0747743404b73726717304bd) (a 22 0x867657604ba3757627604b83547527604b12544507500b11987867304b43876647304b43866757304b43866747304b41977827304b02977627304b03766847304b42867547304b32857643304bf2957627304b02847643304bf2857547304b32757827304b01767617300ba0757607300bb3546717204b52927717204b53756727104b5)) (.fork (a 15 0x3875657504b63977437504bd2877857504b63957637504bd3757837504bd3437617304b51977827204b22977627204b22867547204b53756437204b53546737204b51657527204b12947627204b22547527204b12637427204b1) (a 18 0x3766757534b13766747534b13876757514be3876727514be3641507500b72867437404b60867717404bd1857737404b62857437404b63857727404bd1657737404b61657327404b22847437404b61547427404b22537327404b23756817304b03526817304bc3734207200bc)))
def j171 : Tree := (.fork (a 20 0x2977647314b62957647314b63646827314b61867743704b01957817604bb1857817604bb3657427604b32766757504b20877727504ba3847817504be3766637204b82867717204b62847717204b62877607200b02987717104bb3766627104be2536317104b02937717104bb2526317104b02927717104bb) (.fork (a 22 0x3644327320b02877647514bf2867647514bf2857647514bf3646727514bf1987867314b03876647314b03866757314b03766847314b03766827314b03626717504b03766647304ba2867537304b33867727304ba2857537304b32657737304b32657327304bf3632717304b31647527304bf3737717304b83656307300b30627623300bb) (a 21 0x977647724b01846837524b01646837524b01866837324b00647643324bb1987527704b43877437704bf1967727704b43757737704bf3757327704bb3547627704bb2987637604b01977837604b01877837604b02947637604b02876717504b82866717504b83547817504b13755547404b61647507300b73742827104b6)))
def j172 : Tree := (.fork j170 j171)
def j173 : Tree := (.fork j169 j172)
def j174 : Tree := (.fork j162 j173)
def j175 : Tree := (.fork (.fork (a 12 0x1987847434ba2987747434ba2967747434ba2867847434ba3767327304ba1767617304b23747527304ba3434307300bc2756417204bb3656417204be2746417204bb2736417204bb) (a 16 0x1757547524ba2757547324ba1967637704b83977637604bb2867437604b71857737604b72857437604b71857327604b32847437604b71547427604b32537327604b33544607600b83866717504b33546717504b21866857404b03967727304b9)) (.fork (a 7 0x637633704bd1876867504b82866757504b82437613204b02727517204b52756427104b22427713104b6) (.fork (a 20 0x1977767724b00867747624b61987867524b02977767524b03866757524b03866737524b03766837524b02756747324b62756737324b62746737324b63876757414b63847827404be1876817304b12757633304b92756817304b12747633304b92746817304b13646717304b02817713304bb2827617204bd) (a 7 0x947637714b11877727504bf2877627504bf2837627504bf3530507500b82917407200b43746617104b7))))
def j176 : Tree := (.fork (a 20 0x3644637630b41967647704b13765847704b10957427704b31857427604b71747743504b83751647504b82757637500b62657743404b33876717304b01977817304bc2757817304bc3636717304b10437433304bf1767607300bc3634307300bc3856417204b01767617204b01736727104b43736617104bf) (.fork (a 21 0x2877647414bd3765547414bd2867647414bd2767747414bd2857647414bd3746627414bd3871847704b53536717504b21877717404b82767717404b83757327404bd1757617404b53547627404bd2867727304bc2857727304bc3732817304bd1656647300bb2757417204b62747417204b63846527104bf3436617104ba) (.fork (a 12 0x1987867534b02977767534b03866757534b03866747534b01876757704bd0987727704b32867733504b91857717504bd1757717504bd2837733504b93957727404be3857827404be) (a 15 0x1987547724b41967747724b43865847724b42867547724b43865747624b42967547624b42967757324b43856747324b43856737324b43756837324b40977647714b13547427504bf3427607500b03757527204b51987807200b0))))
def j177 : Tree := (.fork j175 j176)
def j178 : Tree := (.fork (.fork (a 22 0x747743724bc2987547614b92967547614b92866647314bb1866827314bb0647643314b62646827314bb1867433704ba2637433704ba1657743504b21877717304b73757327304bc1757617304b40407537300be2757717304b70657537304be3547627304bc3646417204b02877617104b63766317104b22837617104b62827617104b6) (.fork (a 13 0x1977437704b51957637704b51757637704b52987627604b11977827604b12977627604b11877827604b13534607600bd2867417104ba2857417104ba3646817104ba2837417104ba2827417104ba) (a 14 0x2877647214b73766427214b72867647214b72857647214b73646727214b70967527704bf1867747604ba2867547604ba2857643604b81867427604b01857527604b01657527604b02637427604b03614507500b9))) (a 16 0x1987637704bf1977737704bf2877637704bf2867637704bf2847637704bf0766757504b71767717504b13547527504bb3856717304b12853647304b00657653300b10867717204bb1957837104b23646317104b92947437104b23436827104b2))
def j179 : Tree := (.fork (a 16 0x2853647314b81957647704b53947717504be3435507500b42867727404bb2866647304be3656717304bd0647643304b40417507300be2767517204bf1757617204b42747517204bf2547617204b43654207200b03877747104b42756527104b0) (.fork (a 14 0x1876867514b92876727514b92866757514b92866727514b91867737604b52867537604b51867327604b11647527604b13524607600ba3853837504b83436717504b43654307300bd1867727300ba3846427104b1) (a 16 0x747743524b13756727314b41536527314b91436527314b90977857504b01957817504b11757817504b13432717504b33436617404be2767517304be2757517304be2727517304be3424307300bd0647643204bb1546537204bf2727417204b3)))
def j180 : Tree := (.fork j178 j179)
def j181 : Tree := (.fork j177 j180)
def j182 : Tree := (.fork (.fork (.fork (a 19 0x977627704be2987327604b41877747604b92877647604b91877427604bf2867647604b92857647604b91857627604bf2757427604bf1947827604b42947327604b43324607600b01876847304b52876747304b52756847304b52847713304bf2876717204b62836717204b63436817104bd) (a 6 0x3654527520bc3767837604b73856717504bb1957817404b22957407200b83757317104b9)) (a 14 0x747743324b71867743714b92987647614b52977647614b51877847614b50957837314b02845437314b01836827314b01436827314b01957747704b50757637304ba1657517304b40407327300b32837517104b6)) (.fork (.fork (a 19 0x1987657724b21977757724b23875857724b21877757724b22867657724b21977857624b22877857524b22967757524b23856737524b23756837524b21987867424b23757327504bd3547627504bd3642717304b03546717304b22877647200b72867647200b72857647200b73876617104ba) (a 9 0x1766757634b32766757534b32766747534b32756747534b31877717504ba2877527504b11767727504b13866717304b22547517204be)) (a 14 0x3634527520b32765637514b42745637514b41736727514b41636727514b42877633604b33987427504b93957727504b93857827504b91876837204bb2756837204bb0947827204b73634207200bd3436427104bc)))
def j183 : Tree := (.fork (.fork (a 10 0x1766757624b72766757524b72766737524b72756737524b71957437704b02987427604b82957427604b81857827604b82937427604b83536717304b4) (a 14 0x747743704b53987737504bd3987327504b93847827504b91967817304b12847733304b41857717304bc2837733304b43877817204bb1766757104bc1766727104bc2756627104bc2867717104be2837717104be)) (.fork (.fork (a 18 0x1987657734b21877757734b22867657734b22987657634b21977857634b22977757534b22877857534b22967757534b23856747534b21987867434b23876647434b23766857434b20757547504b62766617404ba2756617404ba1646637204be3757817204b32627417204b2) (a 15 0x1656647320b02656527320b03544327320b02646527320b00647643714b13766757314b83766727314b81987437704ba2867437704ba1957737704ba1857737704ba2857437704ba2847437704ba2987727604b62867827604b6)) (a 17 0x1877737604b12877637604b11877327604bd2867637604b12847637604b11747627604bd2747327604bd2766717504b92756717504b91866817304b72867717304b12857717304b12646817304b72647417204b93845207200b22817607200b03646617104b4)))
def j184 : Tree := (.fork j182 j183)
def j185 : Tree := (.fork (.fork (a 19 0x877647614b10747743414b32867547214b33756427214b33546727214b31977647704b51967437704be1957537704be2987527604b63977437604b12967527604b63757837604b13654607600bf3530607600ba3434607600be3846717504b93765507500bc0767763204b70767763104b2) (a 16 0x3654637630b62544527520b42856527314be2846527314be2877727504ba2867727504ba3846617404b31867717304ba2657717304ba3644307300b23866417204b43546417204b32747617204b42927417204b33756317104b53547617104b0)) (.fork (.fork (a 17 0x1987647724b31977747724b33875847724b32877647724b32867647724b32857647724b33875747624b32977647624b31987867324b33866757324b33866747324b33866737324b33766837324b31766757614b33876717504bf0757607500b82417413104b9) (a 11 0x1857547624b22867547324b22857547324b23546737324b23767747714b30947437714b41987537704b91967737704b90757633604bf0637633604bf2715607600b1)) (a 18 0x1877757320b53756647320b52867437414b21857737414b22857437414b21657737414b22847437414b23636717504be0437433504bd1877727404b22767727404b22837627404b22715307300b62827517204bd2977647104bb3846627104bb1647643104b63646827104bb)))
def j186 : Tree := (.fork (a 18 0x1977837624bc1957547704bc0627623500b03314507500bc2867717404b61957817304b73436717304bc3432717304bb1747607300b72867417204b22857417204b22847417204b22755207200b71987817104bb3867747104bb3757717104b73436527104b52837817104bb) (.fork (a 17 0x1987847534b62987747534b62977747534b62877847534b62867847534b62957747534b60747743424b52876757614b00747537514bd1987643704bf3836617404b32757617304be3747627304b63324307300b13625307300b01957817104b02537817104b0) (a 21 0x2977437514b31957837514b32947437514b33755547414b21977637704b41877757604bf2867657604bf0867727604b83424607600bd3646717504be1857717404bd2655547404bb1657717404bd3987627304b53977727304b53877827304b52547417204bb2715207200b32867317104bd2847317104bd2837317104bd)))
def j187 : Tree := (.fork j185 j186)
def j188 : Tree := (.fork j184 j187)
def j189 : Tree := (.fork j181 j188)
def j190 : Tree := (.fork j174 j189)
def j191 : Tree := (.fork (.fork (a 21 0x2877647434b02867647434b02857647434b01877437614b13755737614b11987657704be3875857704be3757637704b52867427604b91857727604b93947527604b62837427604b92967437404b61957837404b61657837404b62947437404b61877707300bf3987617204b43856717204ba2815207200b23877417104bf) (a 11 0x1867743724b63655637514bd3767727304bf0857737304b52757537304b82657637304b83947617304b82747537304b82967547204b43856437204b43546837204b4)) (.fork (a 17 0x1987867654b63867656644b61987757724bf2967757624bf1866757714b91766757714b91766757504be2877717504b02867717504b03857327504b53847427504b53547727504b52615507500b81987837404bb2967737404bb2867837404bb3826717304bc) (a 13 0x2757317500bf0327323500bf3214507500b92877617404ba2827617404ba2967547304b22957547304b22967757204b93856737204b93756837204b93957617204be3745207200b33876527104b4)))
def j192 : Tree := (.fork (a 19 0x3544637630b03534527520b92977647514bd1856837214b43967427604bc3855547404bc3866647304b33766717304bc3762817304b51967837304b52957537304b52657837304b53626717304b42756737204b92757613204bb1746717204bf2737613204bb2436717204bf2756727104bf) (.fork (.fork (a 10 0x647643724b00977827504b21757437504b72987717204b93656437204bd2757547204bd3646537204bd3546637204bd2947717204b92427413104b3) (a 16 0x1987757734b72987757634b72967757634b73876757434b72755437314b82745437314b81736727314b81436727314b81747633604bf3857427504b23866637204bd2756437204b31746737204b32746437204b30547427204b93646527104ba)) (.fork (a 7 0x3877427404b93857627404b93757727404b92756747304b53540307300bc2756717204b62736717204b6) (.fork (a 5 0x967837414b83656817304b52717613204b12867407200b42857407200b4) (a 22 0x3765747624bf2757547624bf2877547524bf3765647524bf2867547524bf3546737524bf2877647424bf3765547424bf2867647424bf2857647424bf1877757324bf2867657324bf3656747324bf3656737324bf1987867514b42977767514b43756717504b52767437404be1757637404be1657637404be2757613304b02747613304b0)))))
def j193 : Tree := (.fork j191 j192)
def j194 : Tree := (.fork (.fork (a 22 0x1877547614bf2757547614bf1987647704b01977747704b01977427704bc3875847704b02877647704b02867647704b01957627704bc2857647704b02757427704bc0987867604b13764757604b10857643604bc0647643604bc1987847304ba2987747304ba2867847304ba2957747304ba3414307300b13876757104bc3876727104bc) (a 22 0x1867747630b41877627604b83514607600bd3635507500b73325507500b33877427304b12756547304b33857627304b11757637304ba2757437304ba3757727304b10657527304bf2877617204bf1756717204b52867617204bf2847617204bf2536717204b52877637104bc2867637104bc3857517104b62847637104bc3736627104bc)) (.fork (.fork (a 12 0x3877547724b23867647724b23767747724b23977547624b23967647624b23767847624b23987657324b23977757324b23877857324b21767437504b61757537504b63736617404ba) (a 13 0x2877747534b32867747534b31987767704ba3766757704ba1987817504bb1977837504b62977637504b62877817504bb2947637504b62756537204b20647527204b81757637104bb3436627104bb)) (a 10 0x3736717504b93326717504b53636817304b72717307300bf1987847104b62987747104b63876427104b62867847104b63846727104b63746827104b6)))
def j195 : Tree := (.fork (a 15 0x747743534b21877747624b72877647624b72867647624b72857647624b73766757324b73766747324b73766737324b71546527314ba1846837214b42846427214b42836427214b40756717304b60746717304b60617613104be) (a 19 0x767763714be0987817604b50867817604b53645507500b73425507500b31957837304b42957437304b42947437304b41987837104b62877647104bc3766427104bc2867647104bc2867837104b62857647104bc3746627104bc3646727104bc2836317104b63736827104b62826317104b6))
def j196 : Tree := (.fork (a 21 0x2767537320b13656327320b12757537320b12747537320b12987757614be2967757614be1766757514bf1766727514bf2756527314bf2977647504bd3746617404b43877327304b12877617304b92867617304b92857617304b93847627304b12827617304b93544307300b33766417204b53646437204bc3646427104b7) (.fork (a 5 0x1756727620b03654627620b01867727604b32867527604b30717713104bb) (a 19 0x1857647624b00537533620bd3530627620bd2877647324b02867647324b02857647324b03646737324b01977327704bd1747627704bd2747327704bd3746717504bc3426717504b21987837304b42867837304b42957737304b42857837304b43646817304bb1877757300b73766817104bc)))
def j197 : Tree := (.fork j195 j196)
def j198 : Tree := (.fork j194 j197)
def j199 : Tree := (.fork j193 j198)
def j200 : Tree := (.fork (.fork (a 19 0x1876847314b62876727314b62756847314b62756827314b62846727314b61877433704b52757433704b53855647504b31766757304b02766647304b02756647304b02647713304b42646307300b92636307300b93735307300be2717507300be1766717204b22636717204b22757407200b7) (a 18 0x1736727620b63634627620b61877647614bb3655737614b40757637314b63767437704b81957327704b11547427704b12537327704b10987837604b60867837604b63735607600ba3624507500b02977647404b02967647404b02767847404b03746817104bf3747613104b0)) (.fork (a 4 0x2756727514ba3875207200b83766617104ba3746427104b2) (a 20 0x1987867644b92987767644b93766857644b93876757544b91977437714b33755837714b31987737704ba2867737704ba3877427504bf0877757504b12765657504b10767527504bd3857627504bf1757637504b83757727504bf3746817304b21766757204b12766637204b12756637204b10747627204bd)))
def j201 : Tree := (.fork (.fork (a 13 0x1987837504b82977737504b82877837504b82867837504b81977857304bd3856647304bd3656847304bd2867437104b21857737104b22857437104b22847437104b23736427104b23436727104b2) (a 10 0x1957427704b10987847604b60867847604b63745607600ba3756717304b92647733304ba3736817304b23526717304b52867517204b22847517204b2)) (.fork (a 18 0x1866857414bc2866627414bc2856627414bc1877727604b32867627604b32837627604b32867433504b21987817404ba1977837404b02967637404b02767837404b02947637404b03436817304bd2767537300bb2757537300bb2747537300bb0747743104b23736817104bf) (a 19 0x1987867614ba2987767614ba3866757614ba1987747704ba2867747704ba2977437504b21957837504b21757837504b22947437504b22877607500b43762847304b92867517304b92857517304b92827517304b93524307300b81977857204be3856637204be3656837204be3645207200b8)))
def j202 : Tree := (.fork j200 j201)
def j203 : Tree := (.fork (.fork (a 18 0x1877527604bc2767527604bc2737527604bc3520507500bc1987817304b91977837304bf2867817304b92957637304bf2857817304b92757837304bf1657537304be2657437304be3657727304b52947637304bf2757607300b13514307300b83857617104b63736527104b0) (a 17 0x2656527314b42646527314b41866837214be0647643214b91987547704b31967747704b31967427704bf3865847704b31957527704bf3757437704ba2637427704bf3977427604b22865757604b43957627604b23757827604b23736717304bb3326717304b7)) (.fork (a 15 0x2877647524bc2867647524bc2857647524bc3646737524bc1987837514b92977737514b92867837514b92867747414b80767763314b13766717504b41766757404b13857327404b83847427404b83547727404b83536817304bb) (a 22 0x1987767734bb3766757734bb1987867634bb2987767634bb3866757634bb3876767534bb3876757534bb3876747534bb2867747434ba1987757704b81967837504b02765647504b31767837504b02755647504b30757427504bf1647713504b71977837204b01857717204bd3646637204b62547717204bd1757607200ba3646627104b1)))
def j204 : Tree := (.fork (.fork (a 13 0x2977647304bf2957647304bf2617307300b71987867204b63866757204b63866737204b63766837204b61987867104b13876627104b13766827104b13756427104b03746527104b03546727104b0) (a 12 0x1987767724bb3766757724bb1987867624bb3866757624bb1867747624ba2867547624ba3756747324ba3756737324ba2865837714be3746717304bb3426717304b70527523300b8)) (.fork (a 19 0x1987847514b92987747514b92977747514b92867847514b93846727514b91977767704ba1967327704bf3977737604b63977327604b23877837604b63947627604b21647733504be3826717504ba3857427404b81657437404b10767763304b53546817304bb3866717204b60867707200be) (a 17 0x1757637514b93865647504b01767847504b03876617404b83877627304bb3867327304b42757637304b43847527304b43534307300b62645307300be2977647204b03866437204b03756417204b83646837204b03546437204bf3526417204b43546427104ba)))
def j205 : Tree := (.fork j203 j204)
def j206 : Tree := (.fork j202 j205)
def j207 : Tree := (.fork j199 j206)
def j208 : Tree := (.fork (.fork (a 12 0x977857514b23655547414b81766757604b20867627604be0967817404b52867747304bb2867427304b72857427304b72837427304b71877707200b92747317104b32737317104b3) (a 13 0x987867614b50647643614b02967757214b73756837214b70987747704b52865847704b53644607600b21847707600b90657517304b43655307300b93520307300b32727517300be1957807200bc)) (a 20 0x857737324be1987837414be2967737414be2867837414be0747743314b32987727504b30977837504b52977727504b32877827504b31747627504b42747327504b41877707500b71756717304b83846717304b52546717304b83726817304b83727613304ba1766757200bc3767747104b51436427104b9))
def j209 : Tree := (.fork (.fork (a 12 0x2757547214b83546637214b81847733704b02987657604bf1977857604bf1877857604bf1857437604b22877607300b02647317300b01846817104ba2637417104bd2426817104ba) (a 17 0x3766757714be0437433704bf1747433604b12437433604b13766757504b32757327500b51747627500b52747327500b52737327500b52857743404bb3836717304ba3632817304ba2817613304bb2436417204b52756317104b72736317104b72726317104b7)) (.fork (a 21 0x1866857644b41766857644b41977647724bb2977647524bb3646837524bb1746737324b71987847414b72987747414b73875547414b72967747414b72867847414b71757627504ba2757427504ba2987717404b22967717404b21846817304bd2957417204b02947417204b01876817104bf2756817104bf2726817104bf) (a 17 0x2646327320b62636327320b62767437414b71757637414b73655537414b71657637414b73436627414b70637633500b52867737304ba2867327304b62857737304ba2857327304b61847727304b62837327304b62534307300b82723417204b32626617104b4)))
def j210 : Tree := (.fork j208 j209)
def j211 : Tree := (.fork (.fork (a 16 0x2867537620b13536727620b11987817604bb1877647604b73867427604b72867817604bb1867437604b01857537604b01657537604b01657427404b32987717304b12957717304b12927717304b11856817104b82526817104b82527317104bf) (a 14 0x2867547314bf3746527314bf3546727314bf3634607600b42866617404b32856617404b32756717304bb2746717304bb2757627304b62717613304b42546417204b32536417204b32817407200b22727317104b0)) (.fork (.fork (a 16 0x1766757534be1866757724b31766757724b31876837524b32766837524b32756837524b31867727600bd0737733504b72867747404b62867427404bc1657727404bc2837427404bc1746717304b32747627204b42615207200b80417413104b9) (a 7 0x647643624b03877737704ba3877327704b03847627704b01856817304bd2546817304bd2767507300be)) (a 8 0x3837617304ba1866837204b03534207200b21866827104bb2866627104bb3857647104bc0647643104b61546527104ba)))
def j212 : Tree := (.fork (.fork (a 17 0x1766757524bc1747743514b53646427214ba2987647604b13875747604b12977647604b11877847604b11847643604bc1857547604b01647643604bc2867737404bc2867327404b81847727404b82837327404b83516307300b13764207200b22537417104bf) (.fork (a 13 0x3987637504b93977737504b93877837504b93742617404ba3756737204b52867527204bb2847527204bb1987867200b93877437104be3757737104be1757617104b81536527104bd2537617104b8) (a 10 0x1877756644b52877656644b50957817304b11657527304b72657427304b72637427304b72967517204b02947517204b01877717104b12737717104b1))) (.fork (a 22 0x1766757734b60987867634b61876867534b62876747534b62866757534b62866747534b62755537530b12745537530b10847437614b63766647314b63755437314bf3736527314bf3877427704b10967757704b33857627704b13757727704b11987867604b62987767604b63866757604b62867537600ba3624607600b42977647200bd) (a 15 0x977837514b32845637514b31877637604b61766717504be2967517304b83756747304b82867527304b42957517304b82857527304b42657727304b42927517304b83624307300b73756717204ba3526717204b63742627104bc)))
def j213 : Tree := (.fork j211 j212)
def j214 : Tree := (.fork j210 j213)
def j215 : Tree := (.fork (.fork (.fork (a 18 0x987847634b61536527320be2536327320be2877647314b62867647314b62857647314b63646727314b61987847604be2987747604be1767433604b62867847604be2637433604b62757327304b60757617304ba1747627304b62747327304b62646417204b82636417204b8) (a 6 0x2977647434bf2967647434bf2957647434bf1646617404b71546617404b72627317104b0)) (.fork (a 17 0x2977647414be2967647414be2767847414be3846627414be1867733704b51877437604b61857637604b61757637604b62867743504bc1746717504ba1646717504ba0957837304b21866817104ba1747743104b13742427104b12626817104ba2637317104bb) (a 11 0x3967747514bb3877427604b10867527604b03857627604b13757727604b13766647500b72655507500bb2987727304bd2867827304bd2957727304bd2857827304bd))) (.fork (a 18 0x1876757734b12876757634b13987437504b82987717504bf2977717504bf3957737504b83957327504b43857837504b83547827504b42927717504bf1877737500ba2877637500ba2757737500ba3837517304bb3987657204b41857717104b92646427104b72537717104b9) (a 14 0x857647624b12765647524b12755647524b11746737524b11646737524b11766757324b11987867414b13876657414b13876627414b13766857414b11767327504bd3987637404b53977737404b53877837404b5)))
def j216 : Tree := (.fork (a 22 0x1876757724b20977647704b52877433604bc1857647604b92877757504be3947737504b03514507500b12757427304b83214307300b22615307300bf3766757204be3766737204be1877727204b62867627204b62837613204b92847627204b62837627204b62876727104bd2756827104bd1636627104be2537517104b22827317104b2) (.fork (a 15 0x3654327320bb2867747514ba3746727514ba3766757304b53766747304b51877727304b12867627304b12857627304b12757727304b12837627304b13766717204b71846837204b63626717204b32827417204bc2846427104b1) (.fork (a 12 0x1977547724bf1967647724bf3765847724bf2757547724bf3865647524bf2967547524bf3546837524bf2977647424bf1977857324bf3656837324bf2847613304b13846617104b7) (a 15 0x3765437314b52757737314b51866757704b71766757704b71987837604bd2987737604bd2867837604bd0977817504b81767427504be1757527504be2637427504be3726617404b22847633304b82757427204b62547627204b6))))
def j217 : Tree := (.fork j215 j216)
def j218 : Tree := (.fork (.fork (a 14 0x987847614bb2877737504b92877327504b52867737504b92867327504b51847727504b52837327504b52767527304ba2757527304ba0737733304b02737527304ba2757307300bf2747307300bf1427307300bb) (a 18 0x3646637214b43875767604bb1877547604ba1867647604ba0867427604b33765747604ba2757547604ba3425607600b73534507500b13735507500b62856547304b22977617204be2947617204be2757417104b92547317104b82737417104b92537317104b82727417104b9)) (.fork (a 11 0x1766757414bd2756627414bd0767763704b52767327404bd0767617404b51747627404bd2747327404bd1856837204b43530207200b22856527104bf3857547104b0) (a 21 0x3765656644b00877757534bf1766757434bf2766647434bf2756647434bf1977837324b00877637614b00847637614b03847527704b41857727600bd1757327504bf3836717504b81547427504bf2537327504bf2757607500b52987727404bc0967837404b52967727404bc2767527204bb2747527204bb2737527204bb)))
def j219 : Tree := (.fork (.fork (a 16 0x767763324b72877747504b92877427504b52867747504b92867427504b51757727504b52837427504b51987817204b12867817204b12847817204b13877647104b73867437104b02656527104b53546317104b02637717104b72927317104b0) (a 19 0x877757524bf1766757424bf2766637424bf2756637424bf2867743514b92987547604b43865747604b42967547604b41867847604b43745507500b63766757404b61766717304b02646717304b02766617104bf2756617104bf2957417104b32937417104b32726617104bf2927417104b3)) (.fork (a 19 0x1877537604ba1867637604ba0867327604b32747537604ba3414607600bb1756717504b21656717504b23524507500b12767427404bd2757427404bd3977737304b42977617304b83877837304b42957617304b83947627304b02927617304b80756717204b70717713204bb3742527104b0) (a 18 0x1957647724b02977647324b03646837324b00987837614ba1877757314b93766527314b92867657314b93756647314b91987867214b33866757214b33766837214b32987757604b92967757604b91757427504bf3635307300be3314307300be3325307300ba0417413204be)))
def j220 : Tree := (.fork j218 j219)
def j221 : Tree := (.fork j217 j220)
def j222 : Tree := (.fork j214 j221)
def j223 : Tree := (.fork j207 j222)
def j224 : Tree := (.fork j190 j223)
def j225 : Tree := (a 4 0x3743714af3743504a43647414a83727304a7)
def j226 : Tree := (a 9 0x1877704a53867534ab3857324a42757704a53847424a43747604a73547724a43707600a93807200ac)
def j227 : Tree := (.fork j225 j226)
def j228 : Tree := (a 6 0x3877424a33857624a33757724a33637500ab3727204a13717504a5)
def j229 : Tree := (.fork j227 j228)
def j230 : Tree := (a 10 0x2757624a93657214a03847434a90637630af3627500ab3733704a03437604a43433604a33217300a23613104a6)
def j231 : Tree := (a 4 0x3657324ad3647424ad3547524ad3627504ad)
def j232 : Tree := (a 2 0x3633304ab2817304a7)
def j233 : Tree := (a 8 0x3877414a13867524ae2757324a11747624a12747324a12737324a13737604ad3327600a6)
def j234 : Tree := (.fork j232 j233)
def j235 : Tree := (.fork j231 j234)
def j236 : Tree := (a 6 0x3877530a52867504a22647320a63637414a72437204a12427104ac)
def j237 : Tree := (.fork j235 j236)
def j238 : Tree := (.fork j230 j237)
def j239 : Tree := (.fork j229 j238)
def j240 : Tree := (a 14 0x3877324af3877214a62867514a02757424a53847624af3847324aa3747724af3637324a13537604a03427600a52537204af3617500a33727404a12527104ab)
def j241 : Tree := (a 18 0x3757600a93767214ad2757434a52747530a53743514a43647324a13647214a83533600a53643200a13547604a03437600a53837624ae3837104a41737614a93637704a93417300ab3617104a23417104ac)
def j242 : Tree := (.fork j240 j241)
def j243 : Tree := (.fork j239 j242)
def j244 : Tree := (a 9 0x3877604ac3867434af3767314ac3857534af3657734af3747214a53437704a03827604a82617404af)
def j245 : Tree := (a 1 0x2717504a7)
def j246 : Tree := (a 3 0x3537620a13637604a43717304a4)
def j247 : Tree := (.fork j245 j246)
def j248 : Tree := (.fork .empty j247)
def j249 : Tree := (.fork j248 .empty)
def j250 : Tree := (a 1 0x3743204a3)
def j251 : Tree := (.fork j249 j250)
def j252 : Tree := (.fork j244 j251)
def j253 : Tree := (a 10 0x3766644a23877200a02767524a33763734a72757524a33743304ab2737524a33527600ab2627104ae3717104a2)
def j254 : Tree := (.fork j252 j253)
def j255 : Tree := (a 5 0x3763724a72847304a93647604a93517204aa3517104a2)
def j256 : Tree := (a 2 0x2837204a61637514af)
def j257 : Tree := (a 4 0x3867424af3857524af3657724af3647200a4)
def j258 : Tree := (a 3 0x2767534a02757534a02747534a0)
def j259 : Tree := (.fork j258 .empty)
def j260 : Tree := (.fork j259 .empty)
def j261 : Tree := (.fork j260 .empty)
def j262 : Tree := (.fork j261 .empty)
def j263 : Tree := (.fork j262 .empty)
def j264 : Tree := (.fork .empty j263)
def j265 : Tree := (.fork .empty j264)
def j266 : Tree := (.fork .empty j265)
def j267 : Tree := (.fork j266 .empty)
def j268 : Tree := (.fork j267 .empty)
def j269 : Tree := (.fork j268 .empty)
def j270 : Tree := (.fork j269 .empty)
def j271 : Tree := (a 1 0x3537600a2)
def j272 : Tree := (.fork j270 j271)
def j273 : Tree := (a 1 0x3727300ab)
def j274 : Tree := (.fork j272 j273)
def j275 : Tree := (.fork j257 j274)
def j276 : Tree := (.fork j256 j275)
def j277 : Tree := (.fork j255 j276)
def j278 : Tree := (.fork j254 j277)
def j279 : Tree := (a 7 0x3657604a53847534a23743404ae3643704a43547704ac3607300a73317104a1)
def j280 : Tree := (a 10 0x1767644af2757544af2647300a13547600a73747414a53837524a13817104a03717404ab3417204a71207200ac)
def j281 : Tree := (.fork j279 j280)
def j282 : Tree := (a 14 0x3867324a33757320a11767614a32857404a73757214ab3847524a33647724a33643324af3547324af1837714a43737414aa3623300ad3537704a73727504a4)
def j283 : Tree := (.fork j281 j282)
def j284 : Tree := (.fork j278 j283)
def j285 : Tree := (.fork j243 j284)
def j286 : Tree := (a 12 0x3877504a13867404a23847504ac3747624a33747104a92727620aa3637714af3637504a33633704a53437314a03517300a40207200a1)
def j287 : Tree := (a 15 0x2877604aa3657300ad3747630a83757614a73647714af3647504a33737204ac3737104a83437304a03437204a73433304ae3727704ab2427214ae3427704a63217500a7)
def j288 : Tree := (.fork j286 j287)
def j289 : Tree := (a 6 0x3867314a63743724a83647514a43643314ac3537304ac3527704af)
def j290 : Tree := (a 1 0x1537414ad)
def j291 : Tree := (a 6 0x1867724a03653300a03757634a52837524a03717600a13607200ad)
def j292 : Tree := (a 5 0x2767504a92757504a93657714a03717204a63713504a3)
def j293 : Tree := (.fork j291 j292)
def j294 : Tree := (.fork j290 j293)
def j295 : Tree := (.fork j289 j294)
def j296 : Tree := (a 16 0x3877514a53867304ac0657650ac3857504a33757624aa3757104a03747614af3743524a73643304a83643204af1547414a53547304a83547204af3637514a73537314a73437404a5)
def j297 : Tree := (.fork j295 j296)
def j298 : Tree := (.fork j288 j297)
def j299 : Tree := (a 19 0x3767520a43877304a83877204af3767634ad1757604a03657614ac3737520af3743324ae3837314a23737514a32637214a83637304aa3637204a13537714ad3537504a13437514ae3827204af3617300a03627704a0)
def j300 : Tree := (a 15 0x3867504a53767624ac3657320a53767104a23647300ab1847724a93847314a23743704a63647304aa3647204a13643714ad3547714ad3547504a12837324a93727500a2)
def j301 : Tree := (.fork j299 j300)
def j302 : Tree := (a 5 0x3763204a73763104a21747604a23743414a33647614a1)
def j303 : Tree := (a 6 0x3757630a63857314ae2647520a43657304a83547514ad3713304a9)
def j304 : Tree := (.fork j302 j303)
def j305 : Tree := (a 15 0x3877404a63767614ac1857724a82657414af3657204a43627300a13637404a73633604ae3437714a23437504ac3433504ab2627414af3607500a03413204a63413104ac)
def j306 : Tree := (.fork j304 j305)
def j307 : Tree := (a 14 0x3877614a13767644a42857434a12857414a72757314a53637300a33743424a53647404af3623500a03537514a50327320a52727314a53727604a33317600a5)
def j308 : Tree := (.fork j306 j307)
def j309 : Tree := (.fork j301 j308)
def j310 : Tree := (.fork j298 j309)
def j311 : Tree := (.fork j285 j310)
def j312 : Tree := (a 12 0x1867744ae2757214aa3847414a43747314a33737304ab2327320a32727214aa3327304a32817104a40607600a00307300a72417204ab)
def j313 : Tree := (a 5 0x3767714a23767504ac3327500a03323500af2317104a4)
def j314 : Tree := (.fork j312 j313)
def j315 : Tree := (a 7 0x1767604a93857214a43547630a01847704a03637520a93747304ab3427304a3)
def j316 : Tree := (a 8 0x1656644a33747204ae3643724a03837414a33737314a23827504a83427204a63707500ac)
def j317 : Tree := (.fork j315 j316)
def j318 : Tree := (.fork j314 j317)
def j319 : Tree := (a 7 0x2867534a23867604a21857704ac3757304a71537530a83643604a83527304af)
def j320 : Tree := (a 10 0x1877754ac3756644ac3867200aa2757414a53757204aa3837324ac3737404ad3417600ad3527204a23327404a5)
def j321 : Tree := (.fork j319 j320)
def j322 : Tree := (a 15 0x3757620a33767514ad3763714aa3757314ad3847214a03747404ab3743534a83533620af1547424af3547314a83717300ab3427404ab3817604a62717304a83507300af)
def j323 : Tree := (.fork j321 j322)
def j324 : Tree := (.fork j318 j323)
def j325 : Tree := (a 8 0x3877314ac1867704a53767304a03737620ad3747514aa3837604ad3637314ad3627304a8)
def j326 : Tree := (a 9 0x1877724a73767204a33757714a93757504a32757724a73727600af2827104a23627204ab3527504ab)
def j327 : Tree := (.fork j325 j326)
def j328 : Tree := (a 5 0x3767500a43847604ad3647314ad3827304ac1507500a4)
def j329 : Tree := (a 10 0x1877734a72877634a73867414a82757734a73737600af3737500a93847200a53743104a41647524a82527320a7)
def j330 : Tree := (.fork j328 j329)
def j331 : Tree := (.fork j327 j330)
def j332 : Tree := (a 19 0x3867214aa3767404a53763314a52857644a73857604a23747600a73657314a23747714ab3747504af3643214a63547214a60527520ac2637424a93437414a53627404a53427504af3317300a63817204af2617104a9)
def j333 : Tree := (a 14 0x2877614ab3763304a53757514ab2757604ad2647500a62757200ae2647434a93737714aa3737504ae3523300a23827404ad3327504ae3707200a93307300a6)
def j334 : Tree := (.fork j332 j333)
def j335 : Tree := (.fork j331 j334)
def j336 : Tree := (.fork j324 j335)
def j337 : Tree := (a 11 0x3867614ab3767604a43857514a43747704ab2647314ad3537300ac3643614a13547614a93627604ac3817404aa3517304a9)
def j338 : Tree := (a 6 0x3656644ae3767200ac3743314a33837504a53737324ae3437104a9)
def j339 : Tree := (.fork j337 j338)
def j340 : Tree := (a 6 0x2847314a11637630af2647304a53433704af2827314a12307300a7)
def j341 : Tree := (a 16 0x3877544a83767300aa3867644a83767744a82757514a91657504a83747324ae3637320ad3633500ab3737704aa3527300ab2637204a83537614a82727514a93517600a13327704a2)
def j342 : Tree := (.fork j340 j341)
def j343 : Tree := (.fork j339 j342)
def j344 : Tree := (a 2 0x3847514ad0507500a3)
def j345 : Tree := (a 1 0x757604aa)
def j346 : Tree := (a 2 0x3747300a51607600ac)
def j347 : Tree := (.fork j345 j346)
def j348 : Tree := (.fork j344 j347)
def j349 : Tree := (.fork j348 .empty)
def j350 : Tree := (a 1 0x1307300a9)
def j351 : Tree := (.fork j349 j350)
def j352 : Tree := (a 13 0x3877524ac3867624ac3867204a13867104a73767534a83767724ac3757324aa3747424aa3643624a23643104ad3547624aa3547104a53733504ac)
def j353 : Tree := (.fork j351 j352)
def j354 : Tree := (a 6 0x3877654a73767524a82757714ad3537104a53717500af3817304a7)
def j355 : Tree := (a 13 0x3877534ac3867634ac3767734ac3757704a62657404a73547300a73737530a23747434aa3647524ad1647504ac3837514a70627620a33437614ac)
def j356 : Tree := (.fork j354 j355)
def j357 : Tree := (.fork j353 j356)
def j358 : Tree := (.fork j343 j357)
def j359 : Tree := (a 18 0x3877634a53757300aa3767324a73857614a43757604a62757404ab3847634a03747524a73647624a73537320a03647104ad1547404a62837214a03837304a23837204a92527314a83527604a63617304a0)
def j360 : Tree := (a 17 0x3877624a43767320ad3877104aa3767704af2757614af3847304a23847204a93847104a53747534a70537530af3647704aa2547304a83737524a63637104ac3427300a53817504a73617204a8)
def j361 : Tree := (.fork j359 j360)
def j362 : Tree := (a 22 0x3867654a31867714af3767434af3767414a53763704a53857304aa3857204a13857104ad3757534af2757634a33657634af3657704a23847614ac3747200af3647434aa3837404a73733304a03637614a33427604ae3317500a93707300a63617404a5)
def j363 : Tree := (a 13 0x3877644ae3767424af3763324ae3757524af2757204ae2757104a43657624af3657104aa2737204ae2727104a43713204a63713104ac3613204a0)
def j364 : Tree := (a 3 0x3867514a73613304af3407200a6)
def j365 : Tree := (a 5 0x2757304a22747304a23327300a53327604a12717204a3)
def j366 : Tree := (.fork j364 j365)
def j367 : Tree := (a 6 0x3877434a93857634a93757734a93847404a53837614aa1437314ab)
def j368 : Tree := (.fork j366 j367)
def j369 : Tree := (.fork j363 j368)
def j370 : Tree := (.fork j362 j369)
def j371 : Tree := (.fork j361 j370)
def j372 : Tree := (.fork j358 j371)
def j373 : Tree := (.fork j336 j372)
def j374 : Tree := (.fork j311 j373)
def j375 : Tree := (a 1 0x36309a)
def j376 : Tree := (a 2 0x331491350093)
def j377 : Tree := (.fork j375 j376)
def j378 : Tree := (a 1 0x353492)
def j379 : Tree := (a 1 0x35249c)
def j380 : Tree := (a 1 0x37649b)
def j381 : Tree := (.fork j379 j380)
def j382 : Tree := (.fork .empty j381)
def j383 : Tree := (.fork j378 j382)
def j384 : Tree := (a 3 0x36509935449333009b)
def j385 : Tree := (.fork j383 j384)
def j386 : Tree := (a 2 0x36449a343490)
def j387 : Tree := (a 1 0x370490)
def j388 : Tree := (a 1 0x36349e)
def j389 : Tree := (.fork j387 j388)
def j390 : Tree := (a 1 0x362497)
def j391 : Tree := (a 1 0x31049c)
def j392 : Tree := (.fork j390 j391)
def j393 : Tree := (a 1 0x332092)
def j394 : Tree := (.fork j392 j393)
def j395 : Tree := (.fork j389 j394)
def j396 : Tree := (.fork j386 j395)
def j397 : Tree := (.fork j385 j396)
def j398 : Tree := (.fork j377 j397)
def j399 : Tree := (a 1 0x35149e)
def j400 : Tree := (a 1 0x365497)
def j401 : Tree := (.fork j399 j400)
def j402 : Tree := (a 1 0x350490)
def j403 : Tree := (.fork j402 .empty)
def j404 : Tree := (.fork j403 .empty)
def j405 : Tree := (.fork j404 .empty)
def j406 : Tree := (.fork .empty j405)
def j407 : Tree := (.fork j406 .empty)
def j408 : Tree := (.fork j407 .empty)
def j409 : Tree := (.fork j408 .empty)
def j410 : Tree := (.fork j409 .empty)
def j411 : Tree := (.fork j410 .empty)
def j412 : Tree := (.fork j411 .empty)
def j413 : Tree := (.fork j412 .empty)
def j414 : Tree := (.fork .empty j413)
def j415 : Tree := (.fork .empty j414)
def j416 : Tree := (.fork .empty j415)
def j417 : Tree := (a 1 0x371494)
def j418 : Tree := (.fork j416 j417)
def j419 : Tree := (.fork j418 .empty)
def j420 : Tree := (.fork .empty j419)
def j421 : Tree := (.fork j420 .empty)
def j422 : Tree := (.fork j401 j421)
def j423 : Tree := (a 2 0x36149434049b)
def j424 : Tree := (a 1 0x330490)
def j425 : Tree := (a 1 0x352097)
def j426 : Tree := (.fork j424 j425)
def j427 : Tree := (.fork j426 .empty)
def j428 : Tree := (a 1 0x320493)
def j429 : Tree := (.fork j427 j428)
def j430 : Tree := (.fork j429 .empty)
def j431 : Tree := (.fork j423 j430)
def j432 : Tree := (.fork j422 j431)
def j433 : Tree := (a 2 0x373494372493)
def j434 : Tree := (a 1 0x360490)
def j435 : Tree := (.fork j434 .empty)
def j436 : Tree := (.fork j435 .empty)
def j437 : Tree := (.fork j436 .empty)
def j438 : Tree := (.fork j437 .empty)
def j439 : Tree := (.fork .empty j438)
def j440 : Tree := (.fork .empty j439)
def j441 : Tree := (.fork j440 .empty)
def j442 : Tree := (.fork .empty j441)
def j443 : Tree := (.fork .empty j442)
def j444 : Tree := (.fork j443 .empty)
def j445 : Tree := (.fork .empty j444)
def j446 : Tree := (.fork j445 .empty)
def j447 : Tree := (.fork j446 .empty)
def j448 : Tree := (.fork .empty j447)
def j449 : Tree := (.fork j448 .empty)
def j450 : Tree := (.fork j449 .empty)
def j451 : Tree := (a 3 0x26449e36009632009c)
def j452 : Tree := (.fork j450 j451)
def j453 : Tree := (a 2 0x374491362097)
def j454 : Tree := (.fork j452 j453)
def j455 : Tree := (.fork j433 j454)
def j456 : Tree := (a 1 0x34249f)
def j457 : Tree := (a 1 0x34149d)
def j458 : Tree := (a 1 0x375490)
def j459 : Tree := (a 1 0x35309d)
def j460 : Tree := (.fork j458 j459)
def j461 : Tree := (.fork j457 j460)
def j462 : Tree := (.fork .empty j461)
def j463 : Tree := (.fork j456 j462)
def j464 : Tree := (a 2 0x33249e32149c)
def j465 : Tree := (.fork j463 j464)
def j466 : Tree := (.fork j455 j465)
def j467 : Tree := (.fork j432 j466)
def j468 : Tree := (.fork j398 j467)
def c : Tables
  | 10 => j0
  | 11 => j1
  | 12 => j10
  | 13 => j41
  | 14 => j138
  | _ => .empty
def d : Tables
  | 9 => j139
  | 10 => j140
  | 11 => j157
  | 12 => j224
  | 13 => j374
  | 14 => j468
  | _ => .empty
def rs := rawStep ls ms gs (normals c ls ms gs 14)
def p0_10 (q : Key) := !call (ns (run c ns 9)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj0 : j0.all p0_10 = true := by decide +kernel
def p0_11 (q : Key) := !call (ns (run c ns 10)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj1 : j1.all p0_11 = true := by decide +kernel
def p0_12 (q : Key) := !call (ns (run c ns 11)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj2 : j2.all p0_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj3 : j3.all p0_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj4 : j4.all p0_12 = true := by decide +kernel
theorem hj5 : j5.all p0_12 = true := Tree.fork_all _ hj3 hj4
theorem hj6 : j6.all p0_12 = true := Tree.fork_all _ hj2 hj5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj7 : j7.all p0_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj8 : j8.all p0_12 = true := by decide +kernel
theorem hj9 : j9.all p0_12 = true := Tree.fork_all _ hj7 hj8
theorem hj10 : j10.all p0_12 = true := Tree.fork_all _ hj6 hj9
def p0_13 (q : Key) := !call (ns (run c ns 12)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj11 : j11.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj12 : j12.all p0_13 = true := by decide +kernel
theorem hj13 : j13.all p0_13 = true := Tree.fork_all _ hj11 hj12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj14 : j14.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj15 : j15.all p0_13 = true := by decide +kernel
theorem hj16 : j16.all p0_13 = true := Tree.fork_all _ hj14 hj15
theorem hj17 : j17.all p0_13 = true := Tree.fork_all _ hj13 hj16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj18 : j18.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj19 : j19.all p0_13 = true := by decide +kernel
theorem hj20 : j20.all p0_13 = true := Tree.fork_all _ hj18 hj19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj21 : j21.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj22 : j22.all p0_13 = true := by decide +kernel
theorem hj23 : j23.all p0_13 = true := Tree.fork_all _ hj21 hj22
theorem hj24 : j24.all p0_13 = true := Tree.fork_all _ hj20 hj23
theorem hj25 : j25.all p0_13 = true := Tree.fork_all _ hj17 hj24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj26 : j26.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj27 : j27.all p0_13 = true := by decide +kernel
theorem hj28 : j28.all p0_13 = true := Tree.fork_all _ hj26 hj27
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj29 : j29.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj30 : j30.all p0_13 = true := by decide +kernel
theorem hj31 : j31.all p0_13 = true := Tree.fork_all _ hj29 hj30
theorem hj32 : j32.all p0_13 = true := Tree.fork_all _ hj28 hj31
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj33 : j33.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj34 : j34.all p0_13 = true := by decide +kernel
theorem hj35 : j35.all p0_13 = true := Tree.fork_all _ hj33 hj34
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj36 : j36.all p0_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj37 : j37.all p0_13 = true := by decide +kernel
theorem hj38 : j38.all p0_13 = true := Tree.fork_all _ hj36 hj37
theorem hj39 : j39.all p0_13 = true := Tree.fork_all _ hj35 hj38
theorem hj40 : j40.all p0_13 = true := Tree.fork_all _ hj32 hj39
theorem hj41 : j41.all p0_13 = true := Tree.fork_all _ hj25 hj40
def p0_14 (q : Key) := !call (ns (run c ns 13)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj42 : j42.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj43 : j43.all p0_14 = true := by decide +kernel
theorem hj44 : j44.all p0_14 = true := Tree.fork_all _ hj42 hj43
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj45 : j45.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj46 : j46.all p0_14 = true := by decide +kernel
theorem hj47 : j47.all p0_14 = true := Tree.fork_all _ hj45 hj46
theorem hj48 : j48.all p0_14 = true := Tree.fork_all _ hj44 hj47
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj49 : j49.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj50 : j50.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj51 : j51.all p0_14 = true := by decide +kernel
theorem hj52 : j52.all p0_14 = true := Tree.fork_all _ hj50 hj51
theorem hj53 : j53.all p0_14 = true := Tree.fork_all _ hj49 hj52
theorem hj54 : j54.all p0_14 = true := Tree.fork_all _ hj48 hj53
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj55 : j55.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj56 : j56.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj57 : j57.all p0_14 = true := by decide +kernel
theorem hj58 : j58.all p0_14 = true := Tree.fork_all _ hj56 hj57
theorem hj59 : j59.all p0_14 = true := Tree.fork_all _ hj55 hj58
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj60 : j60.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj61 : j61.all p0_14 = true := by decide +kernel
theorem hj62 : j62.all p0_14 = true := Tree.fork_all _ hj60 hj61
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj63 : j63.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj64 : j64.all p0_14 = true := by decide +kernel
theorem hj65 : j65.all p0_14 = true := Tree.fork_all _ hj63 hj64
theorem hj66 : j66.all p0_14 = true := Tree.fork_all _ hj62 hj65
theorem hj67 : j67.all p0_14 = true := Tree.fork_all _ hj59 hj66
theorem hj68 : j68.all p0_14 = true := Tree.fork_all _ hj54 hj67
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj69 : j69.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj70 : j70.all p0_14 = true := by decide +kernel
theorem hj71 : j71.all p0_14 = true := Tree.fork_all _ hj69 hj70
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj72 : j72.all p0_14 = true := by decide +kernel
theorem hj73 : j73.all p0_14 = true := Tree.fork_all _ hj71 hj72
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj74 : j74.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj75 : j75.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj76 : j76.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj77 : j77.all p0_14 = true := by decide +kernel
theorem hj78 : j78.all p0_14 = true := Tree.fork_all _ hj76 hj77
theorem hj79 : j79.all p0_14 = true := Tree.fork_all _ hj75 hj78
theorem hj80 : j80.all p0_14 = true := Tree.fork_all _ hj74 hj79
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj81 : j81.all p0_14 = true := by decide +kernel
theorem hj82 : j82.all p0_14 = true := Tree.fork_all _ hj80 hj81
theorem hj83 : j83.all p0_14 = true := Tree.fork_all _ hj73 hj82
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj84 : j84.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj85 : j85.all p0_14 = true := by decide +kernel
theorem hj86 : j86.all p0_14 = true := Tree.fork_all _ hj84 hj85
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj87 : j87.all p0_14 = true := by decide +kernel
theorem hj88 : j88.all p0_14 = true := Tree.fork_all _ hj86 hj87
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj89 : j89.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj90 : j90.all p0_14 = true := by decide +kernel
theorem hj91 : j91.all p0_14 = true := Tree.fork_all _ hj89 hj90
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj92 : j92.all p0_14 = true := by decide +kernel
theorem hj93 : j93.all p0_14 = true := Tree.fork_all _ hj91 hj92
theorem hj94 : j94.all p0_14 = true := Tree.fork_all _ hj88 hj93
theorem hj95 : j95.all p0_14 = true := Tree.fork_all _ hj83 hj94
theorem hj96 : j96.all p0_14 = true := Tree.fork_all _ hj68 hj95
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj97 : j97.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj98 : j98.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj99 : j99.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj100 : j100.all p0_14 = true := by decide +kernel
theorem hj101 : j101.all p0_14 = true := Tree.fork_all _ hj99 hj100
theorem hj102 : j102.all p0_14 = true := Tree.fork_all _ hj98 hj101
theorem hj103 : j103.all p0_14 = true := Tree.fork_all _ hj97 hj102
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj104 : j104.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj105 : j105.all p0_14 = true := by decide +kernel
theorem hj106 : j106.all p0_14 = true := Tree.fork_all _ hj104 hj105
theorem hj107 : j107.all p0_14 = true := Tree.fork_all _ hj103 hj106
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj108 : j108.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj109 : j109.all p0_14 = true := by decide +kernel
theorem hj110 : j110.all p0_14 = true := Tree.fork_all _ hj108 hj109
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj111 : j111.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj112 : j112.all p0_14 = true := by decide +kernel
theorem hj113 : j113.all p0_14 = true := Tree.fork_all _ hj111 hj112
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj114 : j114.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj115 : j115.all p0_14 = true := by decide +kernel
theorem hj116 : j116.all p0_14 = true := Tree.fork_all _ hj114 hj115
theorem hj117 : j117.all p0_14 = true := Tree.fork_all _ hj113 hj116
theorem hj118 : j118.all p0_14 = true := Tree.fork_all _ hj110 hj117
theorem hj119 : j119.all p0_14 = true := Tree.fork_all _ hj107 hj118
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj120 : j120.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj121 : j121.all p0_14 = true := by decide +kernel
theorem hj122 : j122.all p0_14 = true := Tree.fork_all _ hj120 hj121
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj123 : j123.all p0_14 = true := by decide +kernel
theorem hj124 : j124.all p0_14 = true := Tree.fork_all _ hj122 hj123
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj125 : j125.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj126 : j126.all p0_14 = true := by decide +kernel
theorem hj127 : j127.all p0_14 = true := Tree.fork_all _ hj125 hj126
theorem hj128 : j128.all p0_14 = true := Tree.fork_all _ hj124 hj127
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj129 : j129.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj130 : j130.all p0_14 = true := by decide +kernel
theorem hj131 : j131.all p0_14 = true := Tree.fork_all _ hj129 hj130
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj132 : j132.all p0_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj133 : j133.all p0_14 = true := by decide +kernel
theorem hj134 : j134.all p0_14 = true := Tree.fork_all _ hj132 hj133
theorem hj135 : j135.all p0_14 = true := Tree.fork_all _ hj131 hj134
theorem hj136 : j136.all p0_14 = true := Tree.fork_all _ hj128 hj135
theorem hj137 : j137.all p0_14 = true := Tree.fork_all _ hj119 hj136
theorem hj138 : j138.all p0_14 = true := Tree.fork_all _ hj96 hj137
def p1_9 (q : Key) := !call (rs (run d rs 8)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj139 : j139.all p1_9 = true := by decide +kernel
def p1_10 (q : Key) := !call (rs (run d rs 9)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj140 : j140.all p1_10 = true := by decide +kernel
def p1_11 (q : Key) := !call (rs (run d rs 10)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj141 : j141.all p1_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj142 : j142.all p1_11 = true := by decide +kernel
theorem hj143 : j143.all p1_11 = true := Tree.fork_all _ hj141 hj142
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj144 : j144.all p1_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj145 : j145.all p1_11 = true := by decide +kernel
theorem hj146 : j146.all p1_11 = true := Tree.fork_all _ hj144 hj145
theorem hj147 : j147.all p1_11 = true := Tree.fork_all _ hj143 hj146
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj148 : j148.all p1_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj149 : j149.all p1_11 = true := by decide +kernel
theorem hj150 : j150.all p1_11 = true := Tree.fork_all _ hj148 hj149
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj151 : j151.all p1_11 = true := by decide +kernel
theorem hj152 : j152.all p1_11 = true := Tree.fork_all _ hj150 hj151
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj153 : j153.all p1_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj154 : j154.all p1_11 = true := by decide +kernel
theorem hj155 : j155.all p1_11 = true := Tree.fork_all _ hj153 hj154
theorem hj156 : j156.all p1_11 = true := Tree.fork_all _ hj152 hj155
theorem hj157 : j157.all p1_11 = true := Tree.fork_all _ hj147 hj156
def p1_12 (q : Key) := !call (rs (run d rs 11)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj158 : j158.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj159 : j159.all p1_12 = true := by decide +kernel
theorem hj160 : j160.all p1_12 = true := Tree.fork_all _ hj158 hj159
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj161 : j161.all p1_12 = true := by decide +kernel
theorem hj162 : j162.all p1_12 = true := Tree.fork_all _ hj160 hj161
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj163 : j163.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj164 : j164.all p1_12 = true := by decide +kernel
theorem hj165 : j165.all p1_12 = true := Tree.fork_all _ hj163 hj164
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj166 : j166.all p1_12 = true := by decide +kernel
theorem hj167 : j167.all p1_12 = true := Tree.fork_all _ hj165 hj166
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj168 : j168.all p1_12 = true := by decide +kernel
theorem hj169 : j169.all p1_12 = true := Tree.fork_all _ hj167 hj168
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj170 : j170.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj171 : j171.all p1_12 = true := by decide +kernel
theorem hj172 : j172.all p1_12 = true := Tree.fork_all _ hj170 hj171
theorem hj173 : j173.all p1_12 = true := Tree.fork_all _ hj169 hj172
theorem hj174 : j174.all p1_12 = true := Tree.fork_all _ hj162 hj173
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj175 : j175.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj176 : j176.all p1_12 = true := by decide +kernel
theorem hj177 : j177.all p1_12 = true := Tree.fork_all _ hj175 hj176
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj178 : j178.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj179 : j179.all p1_12 = true := by decide +kernel
theorem hj180 : j180.all p1_12 = true := Tree.fork_all _ hj178 hj179
theorem hj181 : j181.all p1_12 = true := Tree.fork_all _ hj177 hj180
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj182 : j182.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj183 : j183.all p1_12 = true := by decide +kernel
theorem hj184 : j184.all p1_12 = true := Tree.fork_all _ hj182 hj183
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj185 : j185.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj186 : j186.all p1_12 = true := by decide +kernel
theorem hj187 : j187.all p1_12 = true := Tree.fork_all _ hj185 hj186
theorem hj188 : j188.all p1_12 = true := Tree.fork_all _ hj184 hj187
theorem hj189 : j189.all p1_12 = true := Tree.fork_all _ hj181 hj188
theorem hj190 : j190.all p1_12 = true := Tree.fork_all _ hj174 hj189
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj191 : j191.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj192 : j192.all p1_12 = true := by decide +kernel
theorem hj193 : j193.all p1_12 = true := Tree.fork_all _ hj191 hj192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj194 : j194.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj195 : j195.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj196 : j196.all p1_12 = true := by decide +kernel
theorem hj197 : j197.all p1_12 = true := Tree.fork_all _ hj195 hj196
theorem hj198 : j198.all p1_12 = true := Tree.fork_all _ hj194 hj197
theorem hj199 : j199.all p1_12 = true := Tree.fork_all _ hj193 hj198
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj200 : j200.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj201 : j201.all p1_12 = true := by decide +kernel
theorem hj202 : j202.all p1_12 = true := Tree.fork_all _ hj200 hj201
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj203 : j203.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj204 : j204.all p1_12 = true := by decide +kernel
theorem hj205 : j205.all p1_12 = true := Tree.fork_all _ hj203 hj204
theorem hj206 : j206.all p1_12 = true := Tree.fork_all _ hj202 hj205
theorem hj207 : j207.all p1_12 = true := Tree.fork_all _ hj199 hj206
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj208 : j208.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj209 : j209.all p1_12 = true := by decide +kernel
theorem hj210 : j210.all p1_12 = true := Tree.fork_all _ hj208 hj209
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj211 : j211.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj212 : j212.all p1_12 = true := by decide +kernel
theorem hj213 : j213.all p1_12 = true := Tree.fork_all _ hj211 hj212
theorem hj214 : j214.all p1_12 = true := Tree.fork_all _ hj210 hj213
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj215 : j215.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj216 : j216.all p1_12 = true := by decide +kernel
theorem hj217 : j217.all p1_12 = true := Tree.fork_all _ hj215 hj216
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj218 : j218.all p1_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj219 : j219.all p1_12 = true := by decide +kernel
theorem hj220 : j220.all p1_12 = true := Tree.fork_all _ hj218 hj219
theorem hj221 : j221.all p1_12 = true := Tree.fork_all _ hj217 hj220
theorem hj222 : j222.all p1_12 = true := Tree.fork_all _ hj214 hj221
theorem hj223 : j223.all p1_12 = true := Tree.fork_all _ hj207 hj222
theorem hj224 : j224.all p1_12 = true := Tree.fork_all _ hj190 hj223
def p1_13 (q : Key) := !call (rs (run d rs 12)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj225 : j225.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj226 : j226.all p1_13 = true := by decide +kernel
theorem hj227 : j227.all p1_13 = true := Tree.fork_all _ hj225 hj226
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj228 : j228.all p1_13 = true := by decide +kernel
theorem hj229 : j229.all p1_13 = true := Tree.fork_all _ hj227 hj228
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj230 : j230.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj231 : j231.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj232 : j232.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj233 : j233.all p1_13 = true := by decide +kernel
theorem hj234 : j234.all p1_13 = true := Tree.fork_all _ hj232 hj233
theorem hj235 : j235.all p1_13 = true := Tree.fork_all _ hj231 hj234
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj236 : j236.all p1_13 = true := by decide +kernel
theorem hj237 : j237.all p1_13 = true := Tree.fork_all _ hj235 hj236
theorem hj238 : j238.all p1_13 = true := Tree.fork_all _ hj230 hj237
theorem hj239 : j239.all p1_13 = true := Tree.fork_all _ hj229 hj238
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj240 : j240.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj241 : j241.all p1_13 = true := by decide +kernel
theorem hj242 : j242.all p1_13 = true := Tree.fork_all _ hj240 hj241
theorem hj243 : j243.all p1_13 = true := Tree.fork_all _ hj239 hj242
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj244 : j244.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj245 : j245.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj246 : j246.all p1_13 = true := by decide +kernel
theorem hj247 : j247.all p1_13 = true := Tree.fork_all _ hj245 hj246
theorem hj248 : j248.all p1_13 = true := Tree.fork_all _ rfl hj247
theorem hj249 : j249.all p1_13 = true := Tree.fork_all _ hj248 rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj250 : j250.all p1_13 = true := by decide +kernel
theorem hj251 : j251.all p1_13 = true := Tree.fork_all _ hj249 hj250
theorem hj252 : j252.all p1_13 = true := Tree.fork_all _ hj244 hj251
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj253 : j253.all p1_13 = true := by decide +kernel
theorem hj254 : j254.all p1_13 = true := Tree.fork_all _ hj252 hj253
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj255 : j255.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj256 : j256.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj257 : j257.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj258 : j258.all p1_13 = true := by decide +kernel
theorem hj259 : j259.all p1_13 = true := Tree.fork_all _ hj258 rfl
theorem hj260 : j260.all p1_13 = true := Tree.fork_all _ hj259 rfl
theorem hj261 : j261.all p1_13 = true := Tree.fork_all _ hj260 rfl
theorem hj262 : j262.all p1_13 = true := Tree.fork_all _ hj261 rfl
theorem hj263 : j263.all p1_13 = true := Tree.fork_all _ hj262 rfl
theorem hj264 : j264.all p1_13 = true := Tree.fork_all _ rfl hj263
theorem hj265 : j265.all p1_13 = true := Tree.fork_all _ rfl hj264
theorem hj266 : j266.all p1_13 = true := Tree.fork_all _ rfl hj265
theorem hj267 : j267.all p1_13 = true := Tree.fork_all _ hj266 rfl
theorem hj268 : j268.all p1_13 = true := Tree.fork_all _ hj267 rfl
theorem hj269 : j269.all p1_13 = true := Tree.fork_all _ hj268 rfl
theorem hj270 : j270.all p1_13 = true := Tree.fork_all _ hj269 rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj271 : j271.all p1_13 = true := by decide +kernel
theorem hj272 : j272.all p1_13 = true := Tree.fork_all _ hj270 hj271
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj273 : j273.all p1_13 = true := by decide +kernel
theorem hj274 : j274.all p1_13 = true := Tree.fork_all _ hj272 hj273
theorem hj275 : j275.all p1_13 = true := Tree.fork_all _ hj257 hj274
theorem hj276 : j276.all p1_13 = true := Tree.fork_all _ hj256 hj275
theorem hj277 : j277.all p1_13 = true := Tree.fork_all _ hj255 hj276
theorem hj278 : j278.all p1_13 = true := Tree.fork_all _ hj254 hj277
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj279 : j279.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj280 : j280.all p1_13 = true := by decide +kernel
theorem hj281 : j281.all p1_13 = true := Tree.fork_all _ hj279 hj280
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj282 : j282.all p1_13 = true := by decide +kernel
theorem hj283 : j283.all p1_13 = true := Tree.fork_all _ hj281 hj282
theorem hj284 : j284.all p1_13 = true := Tree.fork_all _ hj278 hj283
theorem hj285 : j285.all p1_13 = true := Tree.fork_all _ hj243 hj284
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj286 : j286.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj287 : j287.all p1_13 = true := by decide +kernel
theorem hj288 : j288.all p1_13 = true := Tree.fork_all _ hj286 hj287
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj289 : j289.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj290 : j290.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj291 : j291.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj292 : j292.all p1_13 = true := by decide +kernel
theorem hj293 : j293.all p1_13 = true := Tree.fork_all _ hj291 hj292
theorem hj294 : j294.all p1_13 = true := Tree.fork_all _ hj290 hj293
theorem hj295 : j295.all p1_13 = true := Tree.fork_all _ hj289 hj294
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj296 : j296.all p1_13 = true := by decide +kernel
theorem hj297 : j297.all p1_13 = true := Tree.fork_all _ hj295 hj296
theorem hj298 : j298.all p1_13 = true := Tree.fork_all _ hj288 hj297
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj299 : j299.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj300 : j300.all p1_13 = true := by decide +kernel
theorem hj301 : j301.all p1_13 = true := Tree.fork_all _ hj299 hj300
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj302 : j302.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj303 : j303.all p1_13 = true := by decide +kernel
theorem hj304 : j304.all p1_13 = true := Tree.fork_all _ hj302 hj303
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj305 : j305.all p1_13 = true := by decide +kernel
theorem hj306 : j306.all p1_13 = true := Tree.fork_all _ hj304 hj305
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj307 : j307.all p1_13 = true := by decide +kernel
theorem hj308 : j308.all p1_13 = true := Tree.fork_all _ hj306 hj307
theorem hj309 : j309.all p1_13 = true := Tree.fork_all _ hj301 hj308
theorem hj310 : j310.all p1_13 = true := Tree.fork_all _ hj298 hj309
theorem hj311 : j311.all p1_13 = true := Tree.fork_all _ hj285 hj310
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj312 : j312.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj313 : j313.all p1_13 = true := by decide +kernel
theorem hj314 : j314.all p1_13 = true := Tree.fork_all _ hj312 hj313
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj315 : j315.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj316 : j316.all p1_13 = true := by decide +kernel
theorem hj317 : j317.all p1_13 = true := Tree.fork_all _ hj315 hj316
theorem hj318 : j318.all p1_13 = true := Tree.fork_all _ hj314 hj317
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj319 : j319.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj320 : j320.all p1_13 = true := by decide +kernel
theorem hj321 : j321.all p1_13 = true := Tree.fork_all _ hj319 hj320
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj322 : j322.all p1_13 = true := by decide +kernel
theorem hj323 : j323.all p1_13 = true := Tree.fork_all _ hj321 hj322
theorem hj324 : j324.all p1_13 = true := Tree.fork_all _ hj318 hj323
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj325 : j325.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj326 : j326.all p1_13 = true := by decide +kernel
theorem hj327 : j327.all p1_13 = true := Tree.fork_all _ hj325 hj326
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj328 : j328.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj329 : j329.all p1_13 = true := by decide +kernel
theorem hj330 : j330.all p1_13 = true := Tree.fork_all _ hj328 hj329
theorem hj331 : j331.all p1_13 = true := Tree.fork_all _ hj327 hj330
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj332 : j332.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj333 : j333.all p1_13 = true := by decide +kernel
theorem hj334 : j334.all p1_13 = true := Tree.fork_all _ hj332 hj333
theorem hj335 : j335.all p1_13 = true := Tree.fork_all _ hj331 hj334
theorem hj336 : j336.all p1_13 = true := Tree.fork_all _ hj324 hj335
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj337 : j337.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj338 : j338.all p1_13 = true := by decide +kernel
theorem hj339 : j339.all p1_13 = true := Tree.fork_all _ hj337 hj338
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj340 : j340.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj341 : j341.all p1_13 = true := by decide +kernel
theorem hj342 : j342.all p1_13 = true := Tree.fork_all _ hj340 hj341
theorem hj343 : j343.all p1_13 = true := Tree.fork_all _ hj339 hj342
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj344 : j344.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj345 : j345.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj346 : j346.all p1_13 = true := by decide +kernel
theorem hj347 : j347.all p1_13 = true := Tree.fork_all _ hj345 hj346
theorem hj348 : j348.all p1_13 = true := Tree.fork_all _ hj344 hj347
theorem hj349 : j349.all p1_13 = true := Tree.fork_all _ hj348 rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj350 : j350.all p1_13 = true := by decide +kernel
theorem hj351 : j351.all p1_13 = true := Tree.fork_all _ hj349 hj350
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj352 : j352.all p1_13 = true := by decide +kernel
theorem hj353 : j353.all p1_13 = true := Tree.fork_all _ hj351 hj352
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj354 : j354.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj355 : j355.all p1_13 = true := by decide +kernel
theorem hj356 : j356.all p1_13 = true := Tree.fork_all _ hj354 hj355
theorem hj357 : j357.all p1_13 = true := Tree.fork_all _ hj353 hj356
theorem hj358 : j358.all p1_13 = true := Tree.fork_all _ hj343 hj357
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj359 : j359.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj360 : j360.all p1_13 = true := by decide +kernel
theorem hj361 : j361.all p1_13 = true := Tree.fork_all _ hj359 hj360
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj362 : j362.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj363 : j363.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj364 : j364.all p1_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj365 : j365.all p1_13 = true := by decide +kernel
theorem hj366 : j366.all p1_13 = true := Tree.fork_all _ hj364 hj365
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj367 : j367.all p1_13 = true := by decide +kernel
theorem hj368 : j368.all p1_13 = true := Tree.fork_all _ hj366 hj367
theorem hj369 : j369.all p1_13 = true := Tree.fork_all _ hj363 hj368
theorem hj370 : j370.all p1_13 = true := Tree.fork_all _ hj362 hj369
theorem hj371 : j371.all p1_13 = true := Tree.fork_all _ hj361 hj370
theorem hj372 : j372.all p1_13 = true := Tree.fork_all _ hj358 hj371
theorem hj373 : j373.all p1_13 = true := Tree.fork_all _ hj336 hj372
theorem hj374 : j374.all p1_13 = true := Tree.fork_all _ hj311 hj373
def p1_14 (q : Key) := !call (rs (run d rs 13)) q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj375 : j375.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj376 : j376.all p1_14 = true := by decide +kernel
theorem hj377 : j377.all p1_14 = true := Tree.fork_all _ hj375 hj376
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj378 : j378.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj379 : j379.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj380 : j380.all p1_14 = true := by decide +kernel
theorem hj381 : j381.all p1_14 = true := Tree.fork_all _ hj379 hj380
theorem hj382 : j382.all p1_14 = true := Tree.fork_all _ rfl hj381
theorem hj383 : j383.all p1_14 = true := Tree.fork_all _ hj378 hj382
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj384 : j384.all p1_14 = true := by decide +kernel
theorem hj385 : j385.all p1_14 = true := Tree.fork_all _ hj383 hj384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj386 : j386.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj387 : j387.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj388 : j388.all p1_14 = true := by decide +kernel
theorem hj389 : j389.all p1_14 = true := Tree.fork_all _ hj387 hj388
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj390 : j390.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj391 : j391.all p1_14 = true := by decide +kernel
theorem hj392 : j392.all p1_14 = true := Tree.fork_all _ hj390 hj391
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj393 : j393.all p1_14 = true := by decide +kernel
theorem hj394 : j394.all p1_14 = true := Tree.fork_all _ hj392 hj393
theorem hj395 : j395.all p1_14 = true := Tree.fork_all _ hj389 hj394
theorem hj396 : j396.all p1_14 = true := Tree.fork_all _ hj386 hj395
theorem hj397 : j397.all p1_14 = true := Tree.fork_all _ hj385 hj396
theorem hj398 : j398.all p1_14 = true := Tree.fork_all _ hj377 hj397
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj399 : j399.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj400 : j400.all p1_14 = true := by decide +kernel
theorem hj401 : j401.all p1_14 = true := Tree.fork_all _ hj399 hj400
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj402 : j402.all p1_14 = true := by decide +kernel
theorem hj403 : j403.all p1_14 = true := Tree.fork_all _ hj402 rfl
theorem hj404 : j404.all p1_14 = true := Tree.fork_all _ hj403 rfl
theorem hj405 : j405.all p1_14 = true := Tree.fork_all _ hj404 rfl
theorem hj406 : j406.all p1_14 = true := Tree.fork_all _ rfl hj405
theorem hj407 : j407.all p1_14 = true := Tree.fork_all _ hj406 rfl
theorem hj408 : j408.all p1_14 = true := Tree.fork_all _ hj407 rfl
theorem hj409 : j409.all p1_14 = true := Tree.fork_all _ hj408 rfl
theorem hj410 : j410.all p1_14 = true := Tree.fork_all _ hj409 rfl
theorem hj411 : j411.all p1_14 = true := Tree.fork_all _ hj410 rfl
theorem hj412 : j412.all p1_14 = true := Tree.fork_all _ hj411 rfl
theorem hj413 : j413.all p1_14 = true := Tree.fork_all _ hj412 rfl
theorem hj414 : j414.all p1_14 = true := Tree.fork_all _ rfl hj413
theorem hj415 : j415.all p1_14 = true := Tree.fork_all _ rfl hj414
theorem hj416 : j416.all p1_14 = true := Tree.fork_all _ rfl hj415
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj417 : j417.all p1_14 = true := by decide +kernel
theorem hj418 : j418.all p1_14 = true := Tree.fork_all _ hj416 hj417
theorem hj419 : j419.all p1_14 = true := Tree.fork_all _ hj418 rfl
theorem hj420 : j420.all p1_14 = true := Tree.fork_all _ rfl hj419
theorem hj421 : j421.all p1_14 = true := Tree.fork_all _ hj420 rfl
theorem hj422 : j422.all p1_14 = true := Tree.fork_all _ hj401 hj421
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj423 : j423.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj424 : j424.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj425 : j425.all p1_14 = true := by decide +kernel
theorem hj426 : j426.all p1_14 = true := Tree.fork_all _ hj424 hj425
theorem hj427 : j427.all p1_14 = true := Tree.fork_all _ hj426 rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj428 : j428.all p1_14 = true := by decide +kernel
theorem hj429 : j429.all p1_14 = true := Tree.fork_all _ hj427 hj428
theorem hj430 : j430.all p1_14 = true := Tree.fork_all _ hj429 rfl
theorem hj431 : j431.all p1_14 = true := Tree.fork_all _ hj423 hj430
theorem hj432 : j432.all p1_14 = true := Tree.fork_all _ hj422 hj431
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj433 : j433.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj434 : j434.all p1_14 = true := by decide +kernel
theorem hj435 : j435.all p1_14 = true := Tree.fork_all _ hj434 rfl
theorem hj436 : j436.all p1_14 = true := Tree.fork_all _ hj435 rfl
theorem hj437 : j437.all p1_14 = true := Tree.fork_all _ hj436 rfl
theorem hj438 : j438.all p1_14 = true := Tree.fork_all _ hj437 rfl
theorem hj439 : j439.all p1_14 = true := Tree.fork_all _ rfl hj438
theorem hj440 : j440.all p1_14 = true := Tree.fork_all _ rfl hj439
theorem hj441 : j441.all p1_14 = true := Tree.fork_all _ hj440 rfl
theorem hj442 : j442.all p1_14 = true := Tree.fork_all _ rfl hj441
theorem hj443 : j443.all p1_14 = true := Tree.fork_all _ rfl hj442
theorem hj444 : j444.all p1_14 = true := Tree.fork_all _ hj443 rfl
theorem hj445 : j445.all p1_14 = true := Tree.fork_all _ rfl hj444
theorem hj446 : j446.all p1_14 = true := Tree.fork_all _ hj445 rfl
theorem hj447 : j447.all p1_14 = true := Tree.fork_all _ hj446 rfl
theorem hj448 : j448.all p1_14 = true := Tree.fork_all _ rfl hj447
theorem hj449 : j449.all p1_14 = true := Tree.fork_all _ hj448 rfl
theorem hj450 : j450.all p1_14 = true := Tree.fork_all _ hj449 rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj451 : j451.all p1_14 = true := by decide +kernel
theorem hj452 : j452.all p1_14 = true := Tree.fork_all _ hj450 hj451
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj453 : j453.all p1_14 = true := by decide +kernel
theorem hj454 : j454.all p1_14 = true := Tree.fork_all _ hj452 hj453
theorem hj455 : j455.all p1_14 = true := Tree.fork_all _ hj433 hj454
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj456 : j456.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj457 : j457.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj458 : j458.all p1_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj459 : j459.all p1_14 = true := by decide +kernel
theorem hj460 : j460.all p1_14 = true := Tree.fork_all _ hj458 hj459
theorem hj461 : j461.all p1_14 = true := Tree.fork_all _ hj457 hj460
theorem hj462 : j462.all p1_14 = true := Tree.fork_all _ rfl hj461
theorem hj463 : j463.all p1_14 = true := Tree.fork_all _ hj456 hj462
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hj464 : j464.all p1_14 = true := by decide +kernel
theorem hj465 : j465.all p1_14 = true := Tree.fork_all _ hj463 hj464
theorem hj466 : j466.all p1_14 = true := Tree.fork_all _ hj455 hj465
theorem hj467 : j467.all p1_14 = true := Tree.fork_all _ hj432 hj466
theorem hj468 : j468.all p1_14 = true := Tree.fork_all _ hj398 hj467
theorem hc : Cert c ns := by
  intro n
  cases n with
  | zero => exact rfl
  | succ n =>
    cases n with
    | zero => exact rfl
    | succ n =>
      cases n with
      | zero => exact rfl
      | succ n =>
        cases n with
        | zero => exact rfl
        | succ n =>
          cases n with
          | zero => exact rfl
          | succ n =>
            cases n with
            | zero => exact rfl
            | succ n =>
              cases n with
              | zero => exact rfl
              | succ n =>
                cases n with
                | zero => exact rfl
                | succ n =>
                  cases n with
                  | zero => exact rfl
                  | succ n =>
                    cases n with
                    | zero => exact hj0
                    | succ n =>
                      cases n with
                      | zero => exact hj1
                      | succ n =>
                        cases n with
                        | zero => exact hj10
                        | succ n =>
                          cases n with
                          | zero => exact hj41
                          | succ n =>
                            cases n with
                            | zero => exact hj138
                            | succ n =>
                              rfl
theorem hd : Cert d rs := by
  intro n
  cases n with
  | zero => exact rfl
  | succ n =>
    cases n with
    | zero => exact rfl
    | succ n =>
      cases n with
      | zero => exact rfl
      | succ n =>
        cases n with
        | zero => exact rfl
        | succ n =>
          cases n with
          | zero => exact rfl
          | succ n =>
            cases n with
            | zero => exact rfl
            | succ n =>
              cases n with
              | zero => exact rfl
              | succ n =>
                cases n with
                | zero => exact rfl
                | succ n =>
                  cases n with
                  | zero => exact hj139
                  | succ n =>
                    cases n with
                    | zero => exact hj140
                    | succ n =>
                      cases n with
                      | zero => exact hj157
                      | succ n =>
                        cases n with
                        | zero => exact hj224
                        | succ n =>
                          cases n with
                          | zero => exact hj374
                          | succ n =>
                            cases n with
                            | zero => exact hj468
                            | succ n =>
                              rfl
theorem transfer (t H ph : Nat) (h : FixedStart.ready c d budget 14 t H ph = false) :
    chk [] rt 0 14 t H ph = false :=
  (chkF_eq c d [] rt 0 14 t H ph (by rw [eqL,eqM,eqG]; exact hc)
    (by rw [eqL,eqM,eqG]; exact hd)).symm.trans ((FixedStart.prepared c d budget 14 t H ph eqB).trans h)
end
end D14
end Memo

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
lemma a0 : ∀ e ∈ acc0, Imp [] e.1 e.2 := by simp [acc0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : c0.all (fun e => okE [] (pr acc0 e.1) e) = true := by decide +kernel
lemma j0 : ∀ e ∈ c0, Imp [] e.1 e.2 := okAll k0 a0
lemma a1 : ∀ e ∈ acc1, Imp [] e.1 e.2 := apI j0 a0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1 : c1.all (fun e => okE [] (pr acc1 e.1) e) = true := by decide +kernel
lemma j1 : ∀ e ∈ c1, Imp [] e.1 e.2 := okAll k1 a1
lemma a2 : ∀ e ∈ acc2, Imp [] e.1 e.2 := apI j1 a1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2 : c2.all (fun e => okE [] (pr acc2 e.1) e) = true := by decide +kernel
lemma j2 : ∀ e ∈ c2, Imp [] e.1 e.2 := okAll k2 a2
lemma a3 : ∀ e ∈ acc3, Imp [] e.1 e.2 := apI j2 a2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k3 : c3.all (fun e => okE [] (pr acc3 e.1) e) = true := by decide +kernel
lemma j3 : ∀ e ∈ c3, Imp [] e.1 e.2 := okAll k3 a3
lemma a4 : ∀ e ∈ acc4, Imp [] e.1 e.2 := apI j3 a3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4 : c4.all (fun e => okE [] (pr acc4 e.1) e) = true := by decide +kernel
lemma j4 : ∀ e ∈ c4, Imp [] e.1 e.2 := okAll k4 a4
lemma a5 : ∀ e ∈ acc5, Imp [] e.1 e.2 := apI j4 a4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5 : c5.all (fun e => okE [] (pr acc5 e.1) e) = true := by decide +kernel
lemma j5 : ∀ e ∈ c5, Imp [] e.1 e.2 := okAll k5 a5
lemma a6 : ∀ e ∈ acc6, Imp [] e.1 e.2 := apI j5 a5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6 : c6.all (fun e => okE [] (pr acc6 e.1) e) = true := by decide +kernel
lemma j6 : ∀ e ∈ c6, Imp [] e.1 e.2 := okAll k6 a6
lemma a7 : ∀ e ∈ acc7, Imp [] e.1 e.2 := apI j6 a6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7 : c7.all (fun e => okE [] (pr acc7 e.1) e) = true := by decide +kernel
lemma j7 : ∀ e ∈ c7, Imp [] e.1 e.2 := okAll k7 a7
lemma a8 : ∀ e ∈ acc8, Imp [] e.1 e.2 := apI j7 a7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k8 : c8.all (fun e => okE [] (pr acc8 e.1) e) = true := by decide +kernel
lemma j8 : ∀ e ∈ c8, Imp [] e.1 e.2 := okAll k8 a8
lemma a9 : ∀ e ∈ acc9, Imp [] e.1 e.2 := apI j8 a8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k9 : c9.all (fun e => okE [] (pr acc9 e.1) e) = true := by decide +kernel
lemma j9 : ∀ e ∈ c9, Imp [] e.1 e.2 := okAll k9 a9
lemma a10 : ∀ e ∈ acc10, Imp [] e.1 e.2 := apI j9 a9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k10 : c10.all (fun e => okE [] (pr acc10 e.1) e) = true := by decide +kernel
lemma j10 : ∀ e ∈ c10, Imp [] e.1 e.2 := okAll k10 a10
lemma a11 : ∀ e ∈ acc11, Imp [] e.1 e.2 := apI j10 a10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k11 : c11.all (fun e => okE [] (pr acc11 e.1) e) = true := by decide +kernel
lemma j11 : ∀ e ∈ c11, Imp [] e.1 e.2 := okAll k11 a11
lemma a12 : ∀ e ∈ acc12, Imp [] e.1 e.2 := apI j11 a11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12 : c12.all (fun e => okE [] (pr acc12 e.1) e) = true := by decide +kernel
lemma j12 : ∀ e ∈ c12, Imp [] e.1 e.2 := okAll k12 a12
lemma a13 : ∀ e ∈ acc13, Imp [] e.1 e.2 := apI j12 a12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k13 : c13.all (fun e => okE [] (pr acc13 e.1) e) = true := by decide +kernel
lemma j13 : ∀ e ∈ c13, Imp [] e.1 e.2 := okAll k13 a13
lemma a14 : ∀ e ∈ acc14, Imp [] e.1 e.2 := apI j13 a13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k14 : c14.all (fun e => okE [] (pr acc14 e.1) e) = true := by decide +kernel
lemma j14 : ∀ e ∈ c14, Imp [] e.1 e.2 := okAll k14 a14
lemma a15 : ∀ e ∈ acc15, Imp [] e.1 e.2 := apI j14 a14
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k15 : c15.all (fun e => okE [] (pr acc15 e.1) e) = true := by decide +kernel
lemma j15 : ∀ e ∈ c15, Imp [] e.1 e.2 := okAll k15 a15
lemma a16 : ∀ e ∈ acc16, Imp [] e.1 e.2 := apI j15 a15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16 : c16.all (fun e => okE [] (pr acc16 e.1) e) = true := by decide +kernel
lemma j16 : ∀ e ∈ c16, Imp [] e.1 e.2 := okAll k16 a16
lemma a17 : ∀ e ∈ acc17, Imp [] e.1 e.2 := apI j16 a16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k17 : c17.all (fun e => okE [] (pr acc17 e.1) e) = true := by decide +kernel
lemma j17 : ∀ e ∈ c17, Imp [] e.1 e.2 := okAll k17 a17
lemma a18 : ∀ e ∈ acc18, Imp [] e.1 e.2 := apI j17 a17
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k18 : c18.all (fun e => okE [] (pr acc18 e.1) e) = true := by decide +kernel
lemma j18 : ∀ e ∈ c18, Imp [] e.1 e.2 := okAll k18 a18
lemma a19 : ∀ e ∈ acc19, Imp [] e.1 e.2 := apI j18 a18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k19 : c19.all (fun e => okE [] (pr acc19 e.1) e) = true := by decide +kernel
lemma j19 : ∀ e ∈ c19, Imp [] e.1 e.2 := okAll k19 a19
lemma a20 : ∀ e ∈ acc20, Imp [] e.1 e.2 := apI j19 a19
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k20 : c20.all (fun e => okE [] (pr acc20 e.1) e) = true := by decide +kernel
lemma j20 : ∀ e ∈ c20, Imp [] e.1 e.2 := okAll k20 a20
lemma a21 : ∀ e ∈ acc21, Imp [] e.1 e.2 := apI j20 a20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k21 : c21.all (fun e => okE [] (pr acc21 e.1) e) = true := by decide +kernel
lemma j21 : ∀ e ∈ c21, Imp [] e.1 e.2 := okAll k21 a21
lemma a22 : ∀ e ∈ acc22, Imp [] e.1 e.2 := apI j21 a21
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k22 : c22.all (fun e => okE [] (pr acc22 e.1) e) = true := by decide +kernel
lemma j22 : ∀ e ∈ c22, Imp [] e.1 e.2 := okAll k22 a22
lemma a23 : ∀ e ∈ acc23, Imp [] e.1 e.2 := apI j22 a22
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k23 : c23.all (fun e => okE [] (pr acc23 e.1) e) = true := by decide +kernel
lemma j23 : ∀ e ∈ c23, Imp [] e.1 e.2 := okAll k23 a23
lemma a24 : ∀ e ∈ acc24, Imp [] e.1 e.2 := apI j23 a23
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k24 : c24.all (fun e => okE [] (pr acc24 e.1) e) = true := by decide +kernel
lemma j24 : ∀ e ∈ c24, Imp [] e.1 e.2 := okAll k24 a24
lemma a25 : ∀ e ∈ acc25, Imp [] e.1 e.2 := apI j24 a24
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k25 : c25.all (fun e => okE [] (pr acc25 e.1) e) = true := by decide +kernel
lemma j25 : ∀ e ∈ c25, Imp [] e.1 e.2 := okAll k25 a25
lemma a26 : ∀ e ∈ acc26, Imp [] e.1 e.2 := apI j25 a25
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k26 : c26.all (fun e => okE [] (pr acc26 e.1) e) = true := by decide +kernel
lemma j26 : ∀ e ∈ c26, Imp [] e.1 e.2 := okAll k26 a26
lemma a27 : ∀ e ∈ acc27, Imp [] e.1 e.2 := apI j26 a26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k27 : c27.all (fun e => okE [] (pr acc27 e.1) e) = true := by decide +kernel
lemma j27 : ∀ e ∈ c27, Imp [] e.1 e.2 := okAll k27 a27
lemma a28 : ∀ e ∈ acc28, Imp [] e.1 e.2 := apI j27 a27
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k28 : c28.all (fun e => okE [] (pr acc28 e.1) e) = true := by decide +kernel
lemma j28 : ∀ e ∈ c28, Imp [] e.1 e.2 := okAll k28 a28
lemma a29 : ∀ e ∈ acc29, Imp [] e.1 e.2 := apI j28 a28
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k29 : c29.all (fun e => okE [] (pr acc29 e.1) e) = true := by decide +kernel
lemma j29 : ∀ e ∈ c29, Imp [] e.1 e.2 := okAll k29 a29
lemma a30 : ∀ e ∈ acc30, Imp [] e.1 e.2 := apI j29 a29
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k30 : c30.all (fun e => okE [] (pr acc30 e.1) e) = true := by decide +kernel
lemma j30 : ∀ e ∈ c30, Imp [] e.1 e.2 := okAll k30 a30
lemma a31 : ∀ e ∈ acc31, Imp [] e.1 e.2 := apI j30 a30
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k31 : c31.all (fun e => okE [] (pr acc31 e.1) e) = true := by decide +kernel
lemma j31 : ∀ e ∈ c31, Imp [] e.1 e.2 := okAll k31 a31
lemma a32 : ∀ e ∈ acc32, Imp [] e.1 e.2 := apI j31 a31
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k32 : c32.all (fun e => okE [] (pr acc32 e.1) e) = true := by decide +kernel
lemma j32 : ∀ e ∈ c32, Imp [] e.1 e.2 := okAll k32 a32
lemma a33 : ∀ e ∈ acc33, Imp [] e.1 e.2 := apI j32 a32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k33 : c33.all (fun e => okE [] (pr acc33 e.1) e) = true := by decide +kernel
lemma j33 : ∀ e ∈ c33, Imp [] e.1 e.2 := okAll k33 a33
lemma a34 : ∀ e ∈ acc34, Imp [] e.1 e.2 := apI j33 a33
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k34 : c34.all (fun e => okE [] (pr acc34 e.1) e) = true := by decide +kernel
lemma j34 : ∀ e ∈ c34, Imp [] e.1 e.2 := okAll k34 a34
lemma a35 : ∀ e ∈ acc35, Imp [] e.1 e.2 := apI j34 a34
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k35 : c35.all (fun e => okE [] (pr acc35 e.1) e) = true := by decide +kernel
lemma j35 : ∀ e ∈ c35, Imp [] e.1 e.2 := okAll k35 a35
lemma a36 : ∀ e ∈ acc36, Imp [] e.1 e.2 := apI j35 a35
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k36 : c36.all (fun e => okE [] (pr acc36 e.1) e) = true := by decide +kernel
lemma j36 : ∀ e ∈ c36, Imp [] e.1 e.2 := okAll k36 a36
lemma a37 : ∀ e ∈ acc37, Imp [] e.1 e.2 := apI j36 a36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k37 : c37.all (fun e => okE [] (pr acc37 e.1) e) = true := by decide +kernel
lemma j37 : ∀ e ∈ c37, Imp [] e.1 e.2 := okAll k37 a37
lemma a38 : ∀ e ∈ acc38, Imp [] e.1 e.2 := apI j37 a37
noncomputable abbrev b32 (t H ph : Nat) := chk [] (pr acc38 32) 32 11 t H ph
abbrev B32 (t : Nat) := ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, b32 t p.1 p.2 = false
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a0 : b32 0 0x1fbefffbfdfffbaffffffbeffbffeffffaffffdbeeffffdefbf 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a1 : b32 0 0x40 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a2 : b32 0 0x1000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a3 : b32 0 0x20000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a4 : b32 0 0x1000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a5 : b32 0 0x10000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a6 : b32 0 0x400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a7 : b32 0 0x2000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a8 : b32 0 0x100000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a9 : b32 0 0x400000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a10 : b32 0 0x10000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a11 : b32 0 0x40000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a12 : b32 0 0x10000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a13 : b32 0 0x400000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a14 : b32 0 0x1000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a15 : b32 0 0x4000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a16 : b32 0 0x40000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a17 : b32 0 0x200000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a18 : b32 0 0x40000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a19 : b32 0 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32a20 : b32 0 0x4000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32zero : B32 0 := by
  refine ⟨[(0x1fbefffbfdfffbaffffffbeffbffeffffaffffdbeeffffdefbf,1),(0x40,0),(0x1000,0),(0x20000,0),(0x1000000000,0),(0x10000000000,0),(0x400000000000,0),(0x2000000000000,0),(0x100000000000000000,0),(0x400000000000000000,0),(0x10000000000000000000000,0),(0x40000000000000000000000000,0),(0x10000000000000000000000000000,0),(0x400000000000000000000000000000,0),(0x1000000000000000000000000000000000000,0),(0x4000000000000000000000000000000000000,0),(0x40000000000000000000000000000000000000,0),(0x200000000000000000000000000000000000000000,0),(0x40000000000000000000000000000000000000000000,0),(0x100000000000000000000000000000000000000000000000,0),(0x4000000000000000000000000000000000000000000000000,0)], by decide +kernel, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b32a0
  · exact b32a1
  · exact b32a2
  · exact b32a3
  · exact b32a4
  · exact b32a5
  · exact b32a6
  · exact b32a7
  · exact b32a8
  · exact b32a9
  · exact b32a10
  · exact b32a11
  · exact b32a12
  · exact b32a13
  · exact b32a14
  · exact b32a15
  · exact b32a16
  · exact b32a17
  · exact b32a18
  · exact b32a19
  · exact b32a20
theorem b32one {t : Nat} (h : b32 t FF 1 = false) : B32 t :=
  ⟨[(FF,1)], ffull, fun p hp => by
    have he : p = (FF,1) := List.mem_singleton.mp hp
    subst p
    exact h⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t1 : b32 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t2 : b32 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t3 : b32 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t4 : b32 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t5 : b32 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t6 : b32 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t7 : b32 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t8 : b32 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t9 : b32 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t10 : b32 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b32t11 : b32 11 FF 1 = false := by decide +kernel
theorem boundAt32 : Imp [] 32 12 := by
  apply imp_of (E := []) (Q := pr acc38 32) (Z := 32) (L := 12) (Or.inl rfl) (by decide +kernel) (by decide)
  · intro e he
    exact a38 e (List.mem_filter.mp he).1
  · right
    intro t ht
    interval_cases t
    · exact b32zero
    · exact b32one b32t1
    · exact b32one b32t2
    · exact b32one b32t3
    · exact b32one b32t4
    · exact b32one b32t5
    · exact b32one b32t6
    · exact b32one b32t7
    · exact b32one b32t8
    · exact b32one b32t9
    · exact b32one b32t10
    · exact b32one b32t11
lemma j38 : ∀ e ∈ c38, Imp [] e.1 e.2 := by
  intro e he
  have h : e = (32,12) := List.mem_singleton.mp he
  subst e
  exact boundAt32

lemma a39 : ∀ e ∈ acc39, Imp [] e.1 e.2 := apI j38 a38
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k39 : c39.all (fun e => okE [] (pr acc39 e.1) e) = true := by decide +kernel
lemma j39 : ∀ e ∈ c39, Imp [] e.1 e.2 := okAll k39 a39
lemma a40 : ∀ e ∈ acc40, Imp [] e.1 e.2 := apI j39 a39
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k40 : c40.all (fun e => okE [] (pr acc40 e.1) e) = true := by decide +kernel
lemma j40 : ∀ e ∈ c40, Imp [] e.1 e.2 := okAll k40 a40
lemma a41 : ∀ e ∈ acc41, Imp [] e.1 e.2 := apI j40 a40
noncomputable abbrev low4 (t H ph : Nat) := chk [] (pr acc41 4) 4 11 t H ph
abbrev lowB4 (t : Nat) := ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, low4 t p.1 p.2 = false
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4a0 : low4 0 0xffffddfffff77fdfefeff7ffbaffffeffffddffffffffffffe 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4a1 : low4 0 0x200000080201010080001000000000000000000000001 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4a2 : low4 0 0x2000000000000000000004000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4a3 : low4 0 0x220000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4a4 : low4 0 0x100000000000800000000000040000010000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4zero : lowB4 0 := by
  refine ⟨[(0xffffddfffff77fdfefeff7ffbaffffeffffddffffffffffffe,1),(0x200000080201010080001000000000000000000000001,0),(0x2000000000000000000004000000000000000000000000,0),(0x220000000000000,0),(0x100000000000800000000000040000010000000000000000000,0)], by decide +kernel, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact low4a0
  · exact low4a1
  · exact low4a2
  · exact low4a3
  · exact low4a4
theorem low4one {t : Nat} (h : low4 t FF 1 = false) : lowB4 t :=
  ⟨[(FF,1)], ffull, fun p hp => by
    have e : p = (FF,1) := List.mem_singleton.mp hp
    subst p
    exact h⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t1 : low4 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t2 : low4 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t3 : low4 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t4 : low4 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t5 : low4 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t6 : low4 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t7 : low4 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t8 : low4 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t9 : low4 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t10 : low4 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low4t11 : low4 11 FF 1 = false := by decide +kernel
theorem low4bound : Imp [] 4 12 := by
  apply imp_of (E := []) (Q := pr acc41 4) (Z := 4) (L := 12) (Or.inl rfl) (by decide +kernel) (by decide)
  · intro e he
    exact a41 e (List.mem_filter.mp he).1
  · right
    intro t ht
    interval_cases t
    · exact low4zero
    · exact low4one low4t1
    · exact low4one low4t2
    · exact low4one low4t3
    · exact low4one low4t4
    · exact low4one low4t5
    · exact low4one low4t6
    · exact low4one low4t7
    · exact low4one low4t8
    · exact low4one low4t9
    · exact low4one low4t10
    · exact low4one low4t11
lemma j41 : ∀ e ∈ c41, Imp [] e.1 e.2 := by
  intro e he
  have h : e = (4,12) := List.mem_singleton.mp he
  subst e
  exact low4bound
lemma a42 : ∀ e ∈ acc42, Imp [] e.1 e.2 := apI j41 a41
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k42 : c42.all (fun e => okE [] (pr acc42 e.1) e) = true := by decide +kernel
lemma j42 : ∀ e ∈ c42, Imp [] e.1 e.2 := okAll k42 a42
lemma a43 : ∀ e ∈ acc43, Imp [] e.1 e.2 := apI j42 a42
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k43 : c43.all (fun e => okE [] (pr acc43 e.1) e) = true := by decide +kernel
lemma j43 : ∀ e ∈ c43, Imp [] e.1 e.2 := okAll k43 a43
lemma a44 : ∀ e ∈ acc44, Imp [] e.1 e.2 := apI j43 a43
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := a44
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_p : pOk 0 rt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_0 : chk [] rt 0 13 0 FF 1 = false := Memo.D13.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_1 : chk [] rt 0 13 1 FF 1 = false := Memo.D13.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_2 : chk [] rt 0 13 2 FF 1 = false := Memo.D13.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_3 : chk [] rt 0 13 3 FF 1 = false := Memo.D13.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_4 : chk [] rt 0 13 4 FF 1 = false := Memo.D13.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_5 : chk [] rt 0 13 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_6 : chk [] rt 0 13 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_7 : chk [] rt 0 13 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_8 : chk [] rt 0 13 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_9 : chk [] rt 0 13 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_10 : chk [] rt 0 13 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_11 : chk [] rt 0 13 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_12 : chk [] rt 0 13 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_13 : chk [] rt 0 13 13 FF 1 = false := by decide +kernel
lemma iroot : Imp [] 0 14 := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by
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
  · exact one root_11
  · exact one root_12
  · exact one root_13)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_0 : chk [] rt 0 14 1 0x19fffee99f367fdff7ffddffffffffef9ff7fffff77ffdf9f77 1 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_1 : chk [] rt 0 14 1 0x8000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_2 : chk [] rt 0 14 1 0x80000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_3 : chk [] rt 0 14 1 0x20000000000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_4 : chk [] rt 0 14 1 0x2000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_5 : chk [] rt 0 14 1 0x8 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_6 : chk [] rt 0 14 1 0x8000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_7 : chk [] rt 0 14 1 0x40000000000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_8 : chk [] rt 0 14 1 0x8000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_9 : chk [] rt 0 14 1 0x2000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_10 : chk [] rt 0 14 1 0x200000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_11 : chk [] rt 0 14 1 0x100000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_12 : chk [] rt 0 14 1 0x800000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_13 : chk [] rt 0 14 1 0x4000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_14 : chk [] rt 0 14 1 0x20000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_15 : chk [] rt 0 14 1 0x2000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_16 : chk [] rt 0 14 1 0x1000000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_17 : chk [] rt 0 14 1 0x8000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_18 : chk [] rt 0 14 1 0x40000000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_19 : chk [] rt 0 14 1 0x800000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_20 : chk [] rt 0 14 1 0x2000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_21 : chk [] rt 0 14 1 0x2000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_22 : chk [] rt 0 14 1 0x80 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_23 : chk [] rt 0 14 1 0x40000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_24 : chk [] rt 0 14 1 0x200000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_25 : chk [] rt 0 14 1 0x1000000000000000000000000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_26 : chk [] rt 0 14 1 0x100000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_27 : chk [] rt 0 14 1 0x4000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutPart0_1_28 : chk [] rt 0 14 1 0x4000000000000000000 0 = false := Memo.D14.transfer _ _ _ (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutResult0_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 14 1 p.1 p.2 = false := by
  refine ⟨[(0x19fffee99f367fdff7ffddffffffffef9ff7fffff77ffdf9f77,1),(0x8000000000000000000000000000000000000000,0),(0x80000000000000000000000000000000000000000,0),(0x20000000000000000000000000000000000000000000000000,0),(0x2000000000000000000000000000000000000,0),(0x8,0),(0x8000000000000000,0),(0x40000000000000000000000000000000000000000000000000,0),(0x8000000000000000000000000000000000,0),(0x2000000000000000000000000000000000000000000,0),(0x200000000000000000000000000000,0),(0x100000000000000000000000000000000000000000000,0),(0x800000000,0),(0x4000000000000000000000000000000000000000000,0),(0x20000000000000000000000000000000000000000000,0),(0x2000000000000000000000000000000,0),(0x1000000000000000000000000000000000000000000000,0),(0x8000000000,0),(0x40000000000000000000000000000000000000000000,0),(0x800000000000000000000000000000000000000,0),(0x2000,0),(0x2000000000000000000,0),(0x80,0),(0x40000000000000000000000000000000000000000,0),(0x200000,0),(0x1000000000000000000000000000000000000000,0),(0x100000000000000000000,0),(0x4000,0),(0x4000000000000000000,0)], by decide +kernel, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cutPart0_1_0
  · exact cutPart0_1_1
  · exact cutPart0_1_2
  · exact cutPart0_1_3
  · exact cutPart0_1_4
  · exact cutPart0_1_5
  · exact cutPart0_1_6
  · exact cutPart0_1_7
  · exact cutPart0_1_8
  · exact cutPart0_1_9
  · exact cutPart0_1_10
  · exact cutPart0_1_11
  · exact cutPart0_1_12
  · exact cutPart0_1_13
  · exact cutPart0_1_14
  · exact cutPart0_1_15
  · exact cutPart0_1_16
  · exact cutPart0_1_17
  · exact cutPart0_1_18
  · exact cutPart0_1_19
  · exact cutPart0_1_20
  · exact cutPart0_1_21
  · exact cutPart0_1_22
  · exact cutPart0_1_23
  · exact cutPart0_1_24
  · exact cutPart0_1_25
  · exact cutPart0_1_26
  · exact cutPart0_1_27
  · exact cutPart0_1_28
lemma iroot_one {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 14 1 S) : False := by
  have hmin : ∀ q < 14, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  exact imp_of_live (L := 15) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr cutResult0_1)

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
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
def EF : ℕ := ((((((((((((((rawP.getD 0 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 4 0)) ||| (rawP.getD 1 0 &&& rawP.getD 4 0)) ||| (rawP.getD 0 0 &&& rawP.getD 5 0)) ||| (rawP.getD 1 0 &&& rawP.getD 5 0)) ||| (rawP.getD 2 0 &&& rawP.getD 5 0)) ||| (rawP.getD 1 0 &&& rawP.getD 6 0)) ||| (rawP.getD 2 0 &&& rawP.getD 6 0)) ||| (rawP.getD 4 0 &&& rawP.getD 6 0)) ||| (rawP.getD 0 0 &&& rawP.getD 7 0)) ||| (rawP.getD 2 0 &&& rawP.getD 7 0)) ||| (rawP.getD 3 0 &&& rawP.getD 7 0)) ||| (rawP.getD 4 0 &&& rawP.getD 7 0)) ||| (rawP.getD 6 0 &&& rawP.getD 7 0))
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
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
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
theorem final : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)) t → 14 ≤ t := by
  rintro t ⟨D, hD, hs, hf⟩
  by_contra hlt
  have hlt' : t < 14 := by omega
  exact iroot D.size (by omega) (bridge D hD hf)

theorem fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

private def countedNot (g : Gate) : Bool := match g.op with | .not => true | _ => false
private def countedBi (g : Gate) : Bool := !countedNot g

private def LiveUnder (m T b u : Nat) (S : Set Nat) : Prop :=
  ∃ k t : Nat, k ≤ b ∧ t ≤ u ∧ ∃ U : Finset Nat, (U : Set Nat) ⊆ S ∧ Live Z0 m T (k+t) t U

private theorem LiveUnder.mono {m T b u S b' u' S'} (h : LiveUnder m T b u S)
    (hb : b ≤ b') (hu : u ≤ u') (sub : S ⊆ S') : LiveUnder m T b' u' S' := by
  obtain ⟨k,t,hk,ht,U,hU,hl⟩ := h
  exact ⟨k,t,hk.trans hb,ht.trans hu,U,hU.trans sub,hl⟩

private theorem LiveUnder.binary {m T b u S d a c} (ha : a ∈ S) (hc : c ∈ S)
    (h : LiveUnder m T b u (insert (op d a c) S)) : LiveUnder m T (b+1) u S := by
  obtain ⟨k,t,hk,ht,U,hU,hl⟩ := h
  by_cases fresh : op d a c ∈ U
  · by_cases dup : a = c
    · subst c
      rw [op_self] at hU
      exact ⟨k,t,by omega,ht,U,fun x hx => (hU hx).elim (fun e => e ▸ ha) id,hl⟩
    · refine ⟨k+1,t,by omega,ht,insert a (insert c (U.erase (op d a c))),?_,?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ha
        · rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hc
          · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
            exact (hU mem).resolve_left ne
      · rw [show k+1+t = k+t+1 by omega]
        apply Live.bi dup (al0 _ _ _)
        rwa [Finset.insert_erase fresh]
  · exact ⟨k,t,by omega,ht,U,fun x hx => (hU hx).resolve_left (fun e => fresh (e ▸ hx)),hl⟩

private theorem LiveUnder.unary {m T b u S a} (ha : a ∈ S)
    (h : LiveUnder m T b u (insert (a ^^^ m) S)) : LiveUnder m T b (u+1) S := by
  obtain ⟨k,t,hk,ht,U,hU,hl⟩ := h
  by_cases fresh : a ^^^ m ∈ U
  · refine ⟨k,t+1,hk,by omega,insert a (U.erase (a ^^^ m)),?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
        exact (hU mem).resolve_left ne
    · apply Live.un
      rwa [Finset.insert_erase fresh]
  · exact ⟨k,t,hk,by omega,U,fun x hx => (hU hx).resolve_left (fun e => fresh (e ▸ hx)),hl⟩

private theorem ex_live_counted {T : Nat} (m : Nat) (gs : List Gate) :
    ∀ (w : List Nat) (S : Set Nat), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    LiveUnder m T (gs.countP countedBi) (gs.countP countedNot) S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i,rfl⟩
    exact ⟨0,0,by simp,by simp,{w.getD i 0},by simpa using getD_mem hw h0 i,.stop⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have go := ih (w ++ [gv m w g]) (insert (gv m w g) S) (fun x hx => by
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inr (hw x hx)
      · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    have stay (h : gv m w g ∈ S) :
        LiveUnder m T ((g::gs).countP countedBi) ((g::gs).countP countedNot) S := by
      exact go.mono (by rw [List.countP_cons]; omega) (by rw [List.countP_cons]; omega)
        (fun x hx => hx.elim (fun e => e ▸ h) id)
    obtain ⟨hop,hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o,l⟩ := g
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        simpa [List.countP_cons,countedBi,countedNot] using
          (LiveUnder.binary (d:=false) (rd i) (rd j) go)
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        simpa [List.countP_cons,countedBi,countedNot] using
          (LiveUnder.binary (d:=true) (rd i) (rd j) go)
    · match l with
      | [] => exact stay hm
      | i :: _ =>
        simpa [List.countP_cons,countedBi,countedNot] using (LiveUnder.unary (rd i) go)

private theorem counted_partition (gs : List Gate) :
    gs.countP countedBi + gs.countP countedNot = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : countedNot g <;> simp [countedBi,h] <;> omega

private theorem counted_unique {α} (p : α → Bool) (gs : List α)
    (h : ∀ i j : Fin gs.length, p (gs.get i) → p (gs.get j) → i = j) :
    gs.countP p ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail (i j : Fin gs.length) (hi : p (gs.get i)) (hj : p (gs.get j)) : i = j :=
      Fin.succ_injective _ (h i.succ j.succ hi hj)
    by_cases head : p g = true
    · have z : gs.countP p = 0 := List.countP_eq_zero.mpr (by
        intro a ha pa
        obtain ⟨i,hi⟩ := List.get_of_mem ha
        have hh := h 0 i.succ head (show p (gs.get i) from hi ▸ pa)
        exact Fin.succ_ne_zero i hh.symm)
      simp [head,z]
    · simpa [head] using ih tail

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) (w : List ℕ) (S : Set ℕ)
    (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (hm : m ∈ S)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : ∃ g ∈ gs, g.op = GateOp.not)
    (one : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (output : ∃ i, (ex m gs w).getD i 0 = T) :
    Sol Z0 m T (gs.length - 1) S ∨ ∃ U : Finset ℕ, (U : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length 1 U := by
  obtain ⟨k,t,hk,ht,U,hU,hl⟩ := ex_live_counted m gs w S hw h0 hm hg output
  have iffNot (g : Gate) : countedNot g ↔ g.op = .not := by
    cases g with | mk op ins => cases op <;> simp [countedNot]
  have cap := counted_unique countedNot gs (fun i j hi hj => one i j ((iffNot _).mp hi) ((iffNot _).mp hj))
  obtain ⟨g,hg',hn⟩ := hnot
  have pos : 0 < gs.countP countedNot := List.countP_pos_iff.mpr ⟨g,hg',(iffNot g).mpr hn⟩
  have total := counted_partition gs
  by_cases short : k+t < gs.length
  · exact Or.inl (hl.sol.mono (by omega) hU)
  · have exactSize : k+t = gs.length := by omega
    have unary : t=1 := by omega
    rw [exactSize,unary] at hl
    exact Or.inr ⟨U,hU,hl⟩

theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (one : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i = j)
    (hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length 1 S0 := by
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
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
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot one ⟨o, hout⟩

section onenot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def onWit : List Gate := [⟨.or, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [0, 15]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [7, 14]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 15 ≤ gates.length := by
      by_contra hlt
      by_cases hlt2 : gates.length < 14
      · exact iroot gates.length hlt2 (bridge ⟨gates, o⟩ (fanInTwo_of hfit) hf)
      · have heq : gates.length = 14 := by omega
        rcases bridge_not gates o (fanInTwo_of hfit) hnot hone hf with hsol | ⟨S0, hS0, hl0⟩
        · exact iroot (gates.length - 1) (by omega) hsol
        · rw [heq] at hl0; exact iroot_one hS0 hl0
    have hw : onWit.length = 15 := rfl
    exact ⟨onWit, 22, onWitBasis, by omega, fun x => (onWitCorrect x).trans (onGraphCorrect x)⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg; obtain ⟨ho, hl⟩ := hfit g hg; refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim

end onenot
end PEqualNP.Outside.L_meta_32950

theorem PEqualNP.Outside.L_meta_32950 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_32950.onFinal
