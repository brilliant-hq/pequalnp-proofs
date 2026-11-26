import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20806

namespace OneHot19369ProjectedSearch

def st (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)

def pick (b t f : Bool) : Bool := Bool.rec (motive := fun _ => Bool) f t b

theorem pick_eq (b t f : Bool) : pick b t f = if b then t else f := by cases b <;> rfl

def bitN (s c : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight s c) 1) 1

theorem bitN_eq (s c : ℕ) : bitN s c = s.testBit c := by
  have h1 : Nat.land (Nat.shiftRight s c) 1 = (s >>> c) % 2 := Nat.and_one_is_mod _
  have h2 : s.testBit c = decide ((s >>> c) % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rw [h2]
  unfold bitN
  rw [h1]
  by_cases h : (s >>> c) % 2 = 1
  · rw [h]; rfl
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.2 fun hh => h (Nat.eq_of_beq_eq_true hh)

def ext1 (c s : ℕ) (L : List ℕ) (k : List ℕ → ℕ → Bool) : Bool :=
  pick (bitN s c) (k L s) (st (Nat.lor s (Nat.pow 2 c)) fun s' => k (c :: L) s')

def grow (z : ℕ) (ws : List ℕ) : ℕ → List ℕ → (List ℕ → ℕ → Bool) → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → (List ℕ → ℕ → Bool) → Bool) (fun s L k => k L s)
    (fun b _ ih s L k => st (Nat.land z b) fun p => ext1 p s L fun L s =>
      st (Nat.lor z b) fun q => ext1 q s L fun L s => ih s L k) ws

def anyb (goal z : ℕ) (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih => pick (Nat.beq (Nat.land z b) goal) true
      (pick (Nat.beq (Nat.lor z b) goal) true ih)) ws

def chk (M goal : ℕ) (ws L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun z _ ih => pick (Nat.beq z goal) true (pick (Nat.beq (Nat.xor z M) goal) true
      (pick (anyb goal z ws) true ih))) L

def loop (goal : ℕ) (f : ℕ → List ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun z post ih => pick (Nat.beq z goal) true (pick (f z post) true ih)) L

def srch (M goal : ℕ) (j : ℕ) : List ℕ → ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → List ℕ → Bool) (fun ws _ L => chk M goal ws L)
    (fun _ ih ws s L => loop goal (fun z post => st (Nat.xor z M) fun q => ext1 q s post fun L s =>
      grow z ws s L fun L s => ih (z :: ws) s L) L) j

theorem ext1_spec (c s : ℕ) (L : List ℕ) : ∃ L' s', (∀ k, ext1 c s L k = k L' s') ∧
    (∀ d ∈ L, d ∈ L') ∧ (c ∈ L' ∨ s.testBit c = true) ∧
    (∀ d, s'.testBit d = true → s.testBit d = true ∨ d ∈ L') := by
  by_cases h : s.testBit c = true
  · refine ⟨L, s, fun k => ?_, fun d hd => hd, .inr h, fun d hd => .inl hd⟩
    unfold ext1
    rw [bitN_eq, h]; rfl
  · refine ⟨c :: L, s ||| 2 ^ c, fun k => ?_, fun d hd => List.mem_cons_of_mem _ hd,
      .inl List.mem_cons_self, fun d hd => ?_⟩
    · unfold ext1
      rw [bitN_eq, Bool.eq_false_iff.2 h]; rfl
    · rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hd
      rcases hd with hd | hd
      · exact .inl hd
      · have : c = d := of_decide_eq_true hd
        exact .inr (this ▸ List.mem_cons_self)

theorem grow_spec (z : ℕ) : ∀ (ws : List ℕ) (s : ℕ) (L : List ℕ), ∃ L' s',
    (∀ k, grow z ws s L k = k L' s') ∧ (∀ d ∈ L, d ∈ L') ∧
    (∀ b ∈ ws, (z &&& b ∈ L' ∨ s.testBit (z &&& b) = true) ∧
      (z ||| b ∈ L' ∨ s.testBit (z ||| b) = true)) ∧
    (∀ d, s'.testBit d = true → s.testBit d = true ∨ d ∈ L') := by
  intro ws
  induction ws with
  | nil => intro s L; exact ⟨L, s, fun k => rfl, fun d hd => hd, by simp, fun d hd => .inl hd⟩
  | cons b ws ih =>
    intro s L
    obtain ⟨L1, s1, e1, m1, c1, t1⟩ := ext1_spec (z &&& b) s L
    obtain ⟨L2, s2, e2, m2, c2, t2⟩ := ext1_spec (z ||| b) s1 L1
    obtain ⟨L3, s3, e3, m3, c3, t3⟩ := ih s2 L2
    have back1 : ∀ d, s1.testBit d = true → d ∈ L3 ∨ s.testBit d = true := fun d hd =>
      (t1 d hd).elim .inr fun h => .inl (m3 d (m2 d h))
    have back2 : ∀ d, s2.testBit d = true → d ∈ L3 ∨ s.testBit d = true := fun d hd =>
      (t2 d hd).elim (back1 d) fun h => .inl (m3 d h)
    refine ⟨L3, s3, fun k => ?_, fun d hd => m3 d (m2 d (m1 d hd)), ?_, ?_⟩
    · change ext1 (z &&& b) s L (fun L s => ext1 (z ||| b) s L fun L s => grow z ws s L k) = _
      rw [e1, e2, e3]
    · intro b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · refine ⟨c1.imp (fun h => m3 _ (m2 _ h)) id, ?_⟩
        rcases c2 with h | h
        · exact .inl (m3 _ h)
        · exact back1 _ h
      · obtain ⟨p, q⟩ := c3 b' hb'
        exact ⟨p.elim .inl (back2 _), q.elim .inl (back2 _)⟩
    · intro d hd
      rcases t3 d hd with h | h
      · exact (back2 d h).symm
      · exact .inr h

def Ob (M : ℕ) (ws : List ℕ) (d : ℕ) : Prop :=
  d = M ∨ (∃ a ∈ ws, d = a ^^^ M) ∨ ∃ a ∈ ws, ∃ b ∈ ws, d = a &&& b ∨ d = a ||| b

def Der (M : ℕ) : List ℕ → List ℕ → Prop
  | _, [] => True
  | ws, d :: D => (d ∈ 0 :: ws ∨ Ob M ws d) ∧ Der M (d :: ws) D

theorem Ob_mono {M : ℕ} {ws ws' : List ℕ} (h : ∀ x ∈ 0 :: ws, x ∈ 0 :: ws') {d : ℕ}
    (hd : d ∈ 0 :: ws ∨ Ob M ws d) : d ∈ 0 :: ws' ∨ Ob M ws' d := by
  have hz : ∀ x ∈ ws, x = 0 ∨ x ∈ ws' := fun x hx => List.mem_cons.1 (h x (List.mem_cons_of_mem _ hx))
  have m0 : (0 : ℕ) ∈ 0 :: ws' := List.mem_cons_self
  rcases hd with hd | rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact .inl (h d hd)
  · exact .inr (.inl rfl)
  · rcases hz a ha with rfl | ha
    · exact .inr (.inl (by simp))
    · exact .inr (.inr (.inl ⟨a, ha, rfl⟩))
  · rcases hz a ha with rfl | ha
    · exact .inl (by simp)
    · rcases hz b hb with rfl | hb
      · exact .inl (by simp)
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inl rfl⟩))
  · rcases hz a ha with rfl | ha
    · exact .inl (by simpa using h b (List.mem_cons_of_mem _ hb))
    · rcases hz b hb with rfl | hb
      · exact .inl (by simpa using Or.inr ha)
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inr rfl⟩))

theorem Der_mono (M : ℕ) : ∀ (D ws ws' : List ℕ), (∀ x ∈ 0 :: ws, x ∈ 0 :: ws') →
    Der M ws D → Der M ws' D := by
  intro D
  induction D with
  | nil => intro ws ws' _ _; trivial
  | cons d D ih =>
    intro ws ws' h hD
    refine ⟨Ob_mono h hD.1, ih _ _ ?_ hD.2⟩
    intro x hx
    simp only [List.mem_cons] at hx h ⊢
    rcases hx with hx | hx | hx
    · exact .inl hx
    · exact .inr (.inl hx)
    · rcases h x (.inr hx) with h | h
      · exact .inl h
      · exact .inr (.inr h)

theorem Der_filter (M z : ℕ) : ∀ (D ws ws' : List ℕ), (∀ x ∈ 0 :: ws, x ∈ 0 :: ws') → z ∈ ws' →
    Der M ws D → Der M ws' (D.filter fun x => decide (x ≠ z)) := by
  intro D
  induction D with
  | nil => intro ws ws' _ _ _; trivial
  | cons d D ih =>
    intro ws ws' h hz hD
    have hsub : ∀ ws'' : List ℕ, (∀ x ∈ 0 :: ws', x ∈ 0 :: ws'') → d ∈ 0 :: ws'' →
        ∀ x ∈ 0 :: d :: ws, x ∈ 0 :: ws'' := by
      intro ws'' h2 hd x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hd
        · exact h2 x (h x (List.mem_cons_of_mem _ hx))
    by_cases hdz : d = z
    · subst hdz
      rw [List.filter_cons_of_neg (by simp)]
      exact ih _ _ (hsub ws' (fun x hx => hx) (List.mem_cons_of_mem _ hz)) hz hD.2
    · rw [List.filter_cons_of_pos (by simpa using hdz)]
      refine ⟨Ob_mono h hD.1, ih _ _ (hsub (d :: ws') ?_ (by simp)) (List.mem_cons_of_mem _ hz) hD.2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)

theorem Der_first (M goal : ℕ) (ws : List ℕ) (hg : goal ∉ 0 :: ws) : ∀ D : List ℕ, Der M ws D →
    goal ∈ D → ∃ d ∈ D, d ∉ 0 :: ws ∧ Ob M ws d := by
  intro D
  induction D with
  | nil => intro _ h; simp at h
  | cons d D ih =>
    intro hD hgD
    by_cases hd : d ∈ 0 :: ws
    · have hne : goal ≠ d := fun e => hg (e ▸ hd)
      have hD' : Der M ws D := Der_mono M D (d :: ws) ws (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hd
          · exact List.mem_cons_of_mem _ hx) hD.2
      obtain ⟨e, he, h⟩ := ih hD' ((List.mem_cons.1 hgD).resolve_left hne)
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩
    · exact ⟨d, List.mem_cons_self, hd, hD.1.resolve_left hd⟩

theorem Ob_cons {M z d : ℕ} {ws : List ℕ} (h : Ob M (z :: ws) d) :
    Ob M ws d ∨ d = z ^^^ M ∨ (∃ b ∈ ws, d = z &&& b ∨ d = z ||| b) ∨ d ∈ 0 :: z :: ws := by
  rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hd⟩
  · exact .inl (.inl rfl)
  · rcases List.mem_cons.1 ha with rfl | ha
    · exact .inr (.inl rfl)
    · exact .inl (.inr (.inl ⟨a, ha, rfl⟩))
  · rcases List.mem_cons.1 ha with ea | ha'
    · rcases List.mem_cons.1 hb with eb | hb'
      · refine .inr (.inr (.inr ?_))
        subst ea; subst eb
        rcases hd with rfl | rfl <;> simp
      · subst ea
        exact .inr (.inr (.inl ⟨b, hb', hd⟩))
    · rcases List.mem_cons.1 hb with eb | hb'
      · refine .inr (.inr (.inl ⟨a, ha', ?_⟩))
        subst eb
        rcases hd with rfl | rfl
        · exact .inl (Nat.and_comm _ _)
        · exact .inr (Nat.or_comm _ _)
      · exact .inl (.inr (.inr ⟨a, ha', b, hb', hd⟩))

theorem pick_true {b t f : Bool} (h : b = true ∧ t = true ∨ b = false ∧ f = true) :
    pick b t f = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem pick_or {b f : Bool} (h : b = true ∨ f = true) : pick b true f = true := by
  cases b
  · exact (h.resolve_left (by simp))
  · rfl

theorem beq_self (a : ℕ) : Nat.beq a a = true := Nat.beq_refl a

theorem anyb_true (goal z : ℕ) (ws : List ℕ) (h : ∃ b ∈ ws, goal = z &&& b ∨ goal = z ||| b) :
    anyb goal z ws = true := by
  induction ws with
  | nil => simp at h
  | cons c ws ih =>
    change pick (Nat.beq (z &&& c) goal) true (pick (Nat.beq (z ||| c) goal) true (anyb goal z ws)) = true
    obtain ⟨b, hb, hd⟩ := h
    rcases List.mem_cons.1 hb with rfl | hb
    · rcases hd with rfl | rfl
      · exact pick_or (.inl (beq_self _))
      · exact pick_or (.inr (pick_or (.inl (beq_self _))))
    · exact pick_or (.inr (pick_or (.inr (ih ⟨b, hb, hd⟩))))

theorem chk_true (M goal : ℕ) (ws L : List ℕ)
    (h : ∃ z ∈ L, z = goal ∨ goal = z ^^^ M ∨ ∃ b ∈ ws, goal = z &&& b ∨ goal = z ||| b) :
    chk M goal ws L = true := by
  induction L with
  | nil => simp at h
  | cons c L ih =>
    change pick (Nat.beq c goal) true (pick (Nat.beq (c ^^^ M) goal) true
      (pick (anyb goal c ws) true (chk M goal ws L))) = true
    obtain ⟨z, hz, hd⟩ := h
    rcases List.mem_cons.1 hz with rfl | hz
    · rcases hd with rfl | rfl | hd
      · exact pick_or (.inl (beq_self _))
      · exact pick_or (.inr (pick_or (.inl (beq_self _))))
      · exact pick_or (.inr (pick_or (.inr (pick_or (.inl (anyb_true _ _ _ hd))))))
    · exact pick_or (.inr (pick_or (.inr (pick_or (.inr (ih ⟨z, hz, hd⟩))))))

theorem srch_sound (M goal : ℕ) : ∀ (j : ℕ) (ws : List ℕ) (s : ℕ) (L D : List ℕ),
    Der M ws D → D.length ≤ j + 2 → goal ∈ D → goal ∉ 0 :: ws →
    (∀ d ∈ D, d ∉ 0 :: ws → Ob M ws d → d ∈ L) →
    (∀ d ∈ D, d ∉ 0 :: ws → s.testBit d = true → d ∈ L) → srch M goal j ws s L = true := by
  intro j
  induction j with
  | zero =>
    intro ws s L D hD hlen hgD hg h1 _
    change chk M goal ws L = true
    obtain ⟨z, hz, hz0, hzo⟩ := Der_first M goal ws hg D hD hgD
    have hzL := h1 z hz hz0 hzo
    by_cases hgo : Ob M ws goal
    · exact chk_true _ _ _ _ ⟨goal, h1 goal hgD hg hgo, .inl rfl⟩
    · have hzg : z ≠ goal := fun e => hgo (e ▸ hzo)
      match D, hD, hlen, hgD, hz with
      | [], _, _, hgD, _ => simp at hgD
      | [a], _, _, hgD, hz =>
        exact (hzg ((List.mem_singleton.1 hz).trans (List.mem_singleton.1 hgD).symm)).elim
      | [a, b], hD, _, hgD, hz =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgD hz
        rcases hgD with rfl | rfl
        · exact (hgo (hD.1.resolve_left hg)).elim
        · rcases hz with rfl | rfl
          · have hb := hD.2.1
            have hgz : goal ∉ 0 :: z :: ws := by
              intro hm
              simp only [List.mem_cons] at hm hg
              rcases hm with h | h | h
              · exact hg (.inl h)
              · exact hzg h.symm
              · exact hg (.inr h)
            rcases Ob_cons (hb.resolve_left hgz) with h | h | h | h
            · exact (hgo h).elim
            · exact chk_true _ _ _ _ ⟨z, hzL, .inr (.inl h)⟩
            · exact chk_true _ _ _ _ ⟨z, hzL, .inr (.inr h)⟩
            · exact (hgz h).elim
          · exact (hzg rfl).elim
      | _ :: _ :: _ :: _, _, hlen, _, _ => simp at hlen
  | succ j ih =>
    intro ws s L D hD hlen hgD hg h1 h2
    set f : ℕ → List ℕ → Bool := fun z post => st (Nat.xor z M) fun q => ext1 q s post fun L s =>
      grow z ws s L fun L s => srch M goal j (z :: ws) s L with hf
    change loop goal f L = true
    induction L with
    | nil =>
      obtain ⟨z, hz, hz0, hzo⟩ := Der_first M goal ws hg D hD hgD
      exact absurd (h1 z hz hz0 hzo) (by simp)
    | cons z post ihL =>
      change pick (Nat.beq z goal) true (pick (f z post) true (loop goal f post)) = true
      by_cases hzD : z ∈ D ∧ z ∉ 0 :: ws
      · obtain ⟨hzD, hz0⟩ := hzD
        by_cases hzg : z = goal
        · subst hzg; exact pick_or (.inl (beq_self _))
        · refine pick_or (.inr (pick_or (.inl ?_)))
          obtain ⟨L1, s1, e1, m1, c1, t1⟩ := ext1_spec (z ^^^ M) s post
          obtain ⟨L2, s2, e2, m2, c2, t2⟩ := grow_spec z ws s1 L1
          have hfz : f z post = srch M goal j (z :: ws) s2 L2 := by
            change ext1 (z ^^^ M) s post (fun L s => grow z ws s L fun L s => srch M goal j (z :: ws) s L) = _
            rw [e1, e2]
          rw [hfz]
          have hback : ∀ d ∈ D, d ∉ 0 :: z :: ws → d ∈ z :: post → d ∈ L2 := by
            intro d _ hd hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact (hd (by simp)).elim
            · exact m2 d (m1 d hm)
          have hd0 : ∀ d, d ∉ 0 :: z :: ws → d ∉ 0 :: ws := by
            intro d hd hm
            simp only [List.mem_cons] at hd hm
            exact hd (hm.elim .inl fun h => .inr (.inr h))
          have hs1 : ∀ d ∈ D, d ∉ 0 :: z :: ws → s1.testBit d = true → d ∈ L2 := by
            intro d hdD hd hb
            rcases t1 d hb with h | h
            · exact hback d hdD hd (h2 d hdD (hd0 d hd) h)
            · exact m2 d h
          have hmem : ∀ d ∈ D.filter (fun x => decide (x ≠ z)), d ∈ D := fun d hd =>
            (List.mem_filter.1 hd).1
          refine ih (z :: ws) s2 L2 (D.filter fun x => decide (x ≠ z)) ?_ ?_ ?_ ?_ ?_ ?_
          · exact Der_filter M z D ws (z :: ws) (fun x hx => by
              rcases List.mem_cons.1 hx with rfl | hx
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) List.mem_cons_self hD
          · have : (D.filter fun x => decide (x ≠ z)).length < D.length :=
              List.length_filter_lt_length_iff_exists.2 ⟨z, hzD, by simp⟩
            omega
          · exact List.mem_filter.2 ⟨hgD, by simpa using fun e => hzg e.symm⟩
          · intro hm
            simp only [List.mem_cons] at hm hg
            rcases hm with h | h | h
            · exact hg (.inl h)
            · exact hzg h.symm
            · exact hg (.inr h)
          · intro d hd hd1 hdo
            have hdD := hmem d hd
            rcases Ob_cons hdo with h | h | ⟨b, hb, h⟩ | h
            · exact hback d hdD hd1 (h1 d hdD (hd0 d hd1) h)
            · subst h
              rcases c1 with h | h
              · exact m2 _ h
              · exact hback _ hdD hd1 (h2 _ hdD (hd0 _ hd1) h)
            · rcases h with rfl | rfl
              · exact (c2 b hb).1.elim id (hs1 _ hdD hd1)
              · exact (c2 b hb).2.elim id (hs1 _ hdD hd1)
            · exact (hd1 h).elim
          · intro d hd hd1 hb
            have hdD := hmem d hd
            rcases t2 d hb with h | h
            · exact hs1 d hdD hd1 h
            · exact h
      · refine pick_or (.inr (pick_or (.inr (ihL ?_ ?_))))
        · intro d hd hd0 ho
          rcases List.mem_cons.1 (h1 d hd hd0 ho) with rfl | h
          · exact (hzD ⟨hd, hd0⟩).elim
          · exact h
        · intro d hd hd0 hb
          rcases List.mem_cons.1 (h2 d hd hd0 hb) with rfl | h
          · exact (hzD ⟨hd, hd0⟩).elim
          · exact h

def raw (M : ℕ) (ws : List ℕ) : List ℕ :=
  M :: (ws.map fun a => a ^^^ M) ++ ws.flatMap fun a => ws.flatMap fun b => [a &&& b, a ||| b]

theorem raw_mem {M : ℕ} {ws : List ℕ} {d : ℕ} (h : Ob M ws d) : d ∈ raw M ws := by
  unfold raw
  rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, h⟩
  · simp
  · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩))
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, ?_⟩⟩)
    rcases h with rfl | rfl <;> simp

def maskOf (l : List ℕ) : ℕ := l.foldr (fun c m => m ||| 2 ^ c) 0

theorem maskOf_bit (l : List ℕ) (d : ℕ) (h : (maskOf l).testBit d = true) : d ∈ l := by
  induction l with
  | nil => simp [maskOf] at h
  | cons c l ih =>
    change (maskOf l ||| 2 ^ c).testBit d = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem _ (ih h)
    · have : c = d := of_decide_eq_true h
      exact this ▸ List.mem_cons_self

end OneHot19369ProjectedSearch

namespace OneHot19369ProjectedTransport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open OneHot19369ProjectedSearch

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

def Cov (R : ℕ) (ws : List ℕ) (w : ℕ → List Bool) : Prop :=
  ∀ i, ∃ t ∈ 0 :: ws, ∀ r < R, (w r).getD i false = t.testBit r

theorem gate_cov (R M : ℕ) (hM : ∀ r < R, M.testBit r = true) (ws : List ℕ) (w : ℕ → List Bool)
    (hw : Cov R ws w) (g : Gate) (hg : Ok g) :
    ∃ z, (z ∈ 0 :: ws ∨ Ob M ws z) ∧ ∀ r < R,
      g.op.eval (g.inputs.map fun i => (w r).getD i false) = z.testBit r := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have notv : ∀ (a r : ℕ), r < R → (a ^^^ M).testBit r = !(a.testBit r) := by
    intro a r hr
    rw [Nat.testBit_xor, hM r hr]
    cases a.testBit r <;> rfl
  have z0 : (0 : ℕ) ∈ 0 :: ws := List.mem_cons_self
  have mNot : ∀ a ∈ 0 :: ws, a ^^^ M ∈ 0 :: ws ∨ Ob M ws (a ^^^ M) := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact .inr (.inl (by simp))
    · exact .inr (.inr (.inl ⟨a, ha, rfl⟩))
  have mAnd : ∀ a ∈ 0 :: ws, ∀ b ∈ 0 :: ws, a &&& b ∈ 0 :: ws ∨ Ob M ws (a &&& b) := by
    intro a ha b hb
    rcases List.mem_cons.1 ha with rfl | ha
    · simp
    · rcases List.mem_cons.1 hb with rfl | hb
      · simp
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inl rfl⟩))
  have mOr : ∀ a ∈ 0 :: ws, ∀ b ∈ 0 :: ws, a ||| b ∈ 0 :: ws ∨ Ob M ws (a ||| b) := by
    intro a ha b hb
    rcases List.mem_cons.1 ha with rfl | ha
    · exact .inl (by simpa using hb)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact .inl (by simpa using Or.inr ha)
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inr rfl⟩))
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨0 ^^^ M, mNot 0 z0, fun r hr => by rw [notv 0 r hr]; simp [GateOp.eval]⟩
    · exact ⟨0, .inl z0, fun r hr => by simp [GateOp.eval]⟩
    · exact ⟨0 ^^^ M, mNot 0 z0, fun r hr => by rw [notv 0 r hr]; simp [GateOp.eval]⟩
  | [i], _ =>
    obtain ⟨a, ha, hav⟩ := hw i
    rcases hop with rfl | rfl | rfl
    · exact ⟨a, .inl ha, fun r hr => by
        simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
    · exact ⟨a, .inl ha, fun r hr => by
        simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
    · exact ⟨a ^^^ M, mNot a ha, fun r hr => by
        rw [notv a r hr]; simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
  | [i, j], _ =>
    obtain ⟨a, ha, hav⟩ := hw i
    obtain ⟨b, hb, hbv⟩ := hw j
    rcases hop with rfl | rfl | rfl
    · exact ⟨a &&& b, mAnd a ha b hb, fun r hr => by
        rw [Nat.testBit_and]; simp only [List.map_cons, List.map_nil, hav r hr, hbv r hr]; simp [GateOp.eval]⟩
    · exact ⟨a ||| b, mOr a ha b hb, fun r hr => by
        rw [Nat.testBit_or]; simp only [List.map_cons, List.map_nil, hav r hr, hbv r hr]; simp [GateOp.eval]⟩
    · exact ⟨a ^^^ M, mNot a ha, fun r hr => by
        rw [notv a r hr]; simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
  | _ :: _ :: _ :: _, hlen => simp at hlen

theorem to_der (R M : ℕ) (hM : ∀ r < R, M.testBit r = true) (o : ℕ) : ∀ (gs : List Gate) (ws : List ℕ)
    (w : ℕ → List Bool) (m : ℕ), (∀ g ∈ gs, Ok g) → (∀ r < R, (w r).length = m) → Cov R ws w →
    ∃ D, Der M ws D ∧ D.length = gs.length ∧
      ∃ t, (t ∈ 0 :: ws ∨ t ∈ D) ∧ ∀ r < R, (wiresFrom gs (w r)).getD o false = t.testBit r := by
  intro gs
  induction gs with
  | nil =>
    intro ws w m _ _ hw
    obtain ⟨t, ht, htv⟩ := hw o
    exact ⟨[], trivial, rfl, t, .inl ht, htv⟩
  | cons g gs ih =>
    intro ws w m hok hlen hw
    obtain ⟨z, hz, hzv⟩ := gate_cov R M hM ws w hw g (hok g List.mem_cons_self)
    obtain ⟨D, hD, hDl, t, ht, htv⟩ := ih (z :: ws)
      (fun r => w r ++ [g.op.eval (g.inputs.map fun i => (w r).getD i false)]) (m + 1)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) (fun r hr => by simp [hlen r hr]) (by
        intro i
        by_cases hi : i = m
        · subst hi
          refine ⟨z, by simp, fun r hr => ?_⟩
          rw [← hzv r hr]
          exact getD_snoc_len _ _ _ _ (hlen r hr)
        · obtain ⟨t, ht, htv⟩ := hw i
          refine ⟨t, ?_, fun r hr => ?_⟩
          · rcases List.mem_cons.1 ht with rfl | ht
            · simp
            · simp [ht]
          · rw [getD_snoc_ne _ _ _ _ (by rw [hlen r hr]; exact hi)]
            exact htv r hr)
    refine ⟨z :: D, ⟨hz, hD⟩, by simp [hDl], t, ?_, htv⟩
    rcases ht with ht | ht
    · rcases List.mem_cons.1 ht with rfl | ht
      · simp
      · rcases List.mem_cons.1 ht with rfl | ht
        · simp
        · exact .inl (List.mem_cons_of_mem _ ht)
    · exact .inr (List.mem_cons_of_mem _ ht)

theorem generated_lt (D ws : List ℕ) (initial : ∀ x ∈ ws, x < 256)
    (runs : Der 255 ws D) (d : ℕ) (seen : d ∈ D) : d < 256 := by
  induction D generalizing ws d with
  | nil => simp at seen
  | cons t tail ih =>
    have ht : t < 256 := by
      rcases runs.1 with held | rfl | ⟨a,ha,rfl⟩ | ⟨a,ha,b,hb,rfl|rfl⟩
      · rcases List.mem_cons.1 held with rfl|held
        · norm_num
        · exact initial _ held
      · norm_num
      · exact Nat.xor_lt_two_pow (n := 8) (initial a ha) (by norm_num)
      · exact Nat.and_lt_two_pow (n := 8) a (initial b hb)
      · exact Nat.or_lt_two_pow (n := 8) (initial a ha) (initial b hb)
    rcases List.mem_cons.1 seen with rfl|later
    · exact ht
    · exact ih (t::ws) (fun x h => by rcases List.mem_cons.1 h with rfl|h
                                      · exact ht
                                      · exact initial x h) runs.2 d later

end OneHot19369ProjectedTransport

namespace SignedSmallTable

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open OneHot19369ProjectedSearch OneHot19369ProjectedTransport

def basis : List ℕ := [1, 14, 48, 192, 66, 20, 32, 137]
def immediate : List ℕ := [255, 254, 15, 49, 193, 67, 21, 33, 241, 62, 206, 2, 78, 4, 30, 46, 8, 143, 207, 240, 114, 16, 52, 185, 63, 64, 194, 212, 224, 128, 201, 189, 86, 98, 203, 235, 157, 223, 169, 118]
def seen : ℕ := maskOf (0::basis ++ immediate)

theorem checkedBase : ∀ d ∈ raw 255 basis, d ∈ 0::basis ∨ d ∈ immediate := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem failed : srch 255 89 3 basis seen immediate = false := by decide +kernel

theorem packed (D : List ℕ) (derives : Der 255 basis D) (small : D.length ≤ 5)
    (output : 89 ∈ D) : False := by
  have absent : (89 : ℕ) ∉ 0::basis := by decide
  have wrong := srch_sound 255 89 3 basis seen immediate D derives small output absent
    (fun d _ h allowed => (checkedBase d (raw_mem allowed)).resolve_left h)
    (fun d _ h cached => by
      unfold seen at cached
      rcases List.mem_append.1 (maskOf_bit _ _ cached) with hd|hd
      · exact (h hd).elim
      · exact hd)
  rw [failed] at wrong
  exact Bool.noConfusion wrong

theorem cannotCompute (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 5)
    (pool : ℕ → List Bool) (n : ℕ) (width : ∀ r < 8, (pool r).length = n)
    (captures : Cov 8 basis pool) : ¬ ∀ r < 8, C.eval (pool r) = (89 : ℕ).testBit r := by
  intro fits
  have all : ∀ r < 8, (255 : ℕ).testBit r = true := by decide +kernel
  obtain ⟨D,derives,count,t,location,agree⟩ :=
    to_der 8 255 all C.output C.gates basis pool n fan width captures
  have inputsSmall : ∀ w ∈ 0::basis, w < 256 := by decide
  have hlt : t < 256 := by
    rcases location with h|h
    · exact inputsSmall t h
    · exact generated_lt D basis (fun w hw => inputsSmall w (List.mem_cons_of_mem _ hw)) derives t h
  have eq : t = 89 := by
    apply Nat.eq_of_testBit_eq
    intro r
    by_cases hr : r < 8
    · exact (agree r hr).symm.trans (fits r hr)
    · have hp : 2 ^ 8 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hp),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) hp)]
  subst t
  have cap : D.length ≤ 5 := by rw [count]; exact small
  exact packed D derives cap (location.resolve_left (by decide))

end SignedSmallTable

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def selected : List ℕ := [3, 4, 5, 7, 9, 10, 12, 15]

private def row (k : ℕ) : Fin 4 := ⟨(selected.getD k 0 / 4) % 4, Nat.mod_lt _ (by decide)⟩
private def col (k : ℕ) : Fin 4 := ⟨selected.getD k 0 % 4, Nat.mod_lt _ (by decide)⟩
private def pool (r : ℕ) := oneEach (row r) (col r)
private def signature (i : ℕ) := ([1, 14, 48, 192, 66, 20, 32, 137] : List ℕ).getD i 0

private theorem width (r : ℕ) : (pool r).length = 8 := by simp [pool,oneEach]

private theorem covers : OneHot19369ProjectedTransport.Cov 8 SignedSmallTable.basis pool := by
  have tab : ∀ i : Fin 8, signature i.val ∈ 0 :: SignedSmallTable.basis ∧
      ∀ r : Fin 8, (pool r.val).getD i.val false = (signature i.val).testBit r.val := by decide +kernel
  intro i
  by_cases hi : i < 8
  · exact ⟨signature i,(tab ⟨i,hi⟩).1,fun r hr => (tab ⟨i,hi⟩).2 ⟨r,hr⟩⟩
  · refine ⟨0,by simp,?_⟩
    intro r _
    rw [List.getD_eq_default _ _ (by rw [width]; omega)]
    simp

private theorem packedGoal : ∀ r : Fin 8,
    (13263 : ℕ).testBit (4*(row r.val).val+(col r.val).val) = (89:ℕ).testBit r.val := by
  decide +kernel

theorem lower : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13263 : ℕ).testBit (4 * u.val + v.val)) C) := by
  rintro ⟨C,fan,cap,rep⟩
  apply SignedSmallTable.cannotCompute C fan cap pool 8 (fun r _ => width r) covers
  intro r hr
  exact (rep (row r) (col r)).trans (packedGoal ⟨r,hr⟩)

end PEqualNP.Outside.L_meta_20806

theorem PEqualNP.Outside.L_meta_20806 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13263 : ℕ).testBit (4 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_20806.lower
