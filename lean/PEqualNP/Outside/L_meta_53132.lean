import PEqualNP.Defs

-- Exhaustion certificate: a kernel-run search over sets of five-bit wire masks (a set is a Nat
-- bitset), with a soundness proof that every circuit of the statement is covered by the search.

namespace PEqualNP.Outside.L_meta_53132

open PEqualNP.CircuitLowerBounds

def elems (S : Nat) : List Nat := (List.range 32).filter (fun a => S.testBit a)

def aoHas (S v : Nat) : Bool :=
  (elems S).any (fun a => (elems S).any (fun c => (a &&& c == v) || (a ||| c == v)))

def notHas (S v : Nat) : Bool := (elems S).any (fun a => 31 ^^^ a == v)

def hit (A B C S : Nat) : Bool := S.testBit A && S.testBit B && S.testBit C

def miss (A B C S : Nat) : Nat :=
  (if S.testBit A then 0 else 1) + (if S.testBit B then 0 else 1) + (if S.testBit C then 0 else 1)

def reach (A B C : Nat) : Nat → Nat → Nat → Bool
  | 0, _, S => hit A B C S
  | k+1, b, S => hit A B C S || (decide (miss A B C S ≤ k+1) &&
      (reach A B C k b S || (decide (0 < b) && reach A B C k (b-1) S) ||
       (List.range 32).any (fun v => !S.testBit v &&
         ((aoHas S v && reach A B C k b (S ||| 2^v)) ||
          (decide (0 < b) && notHas S v && reach A B C k (b-1) (S ||| 2^v))))))

theorem mem_elems {S a : Nat} : a ∈ elems S ↔ a < 32 ∧ S.testBit a = true := by
  simp [elems, List.mem_filter, List.mem_range]

theorem bits32 : ∀ a < 32, ∀ c < 32, a &&& c < 32 ∧ a ||| c < 32 ∧ 31 ^^^ a < 32 := by
  decide +kernel

theorem uniq32 : ∀ m < 32, ∀ a < 32, (∀ t : Fin 5, m.testBit t.val = a.testBit t.val) → m = a := by
  decide +kernel

theorem t31 : ∀ t : Fin 5, (31 : Nat).testBit t.val = true := by decide

theorem or_pow_self {S v : Nat} (h : S.testBit v = true) : S ||| 2^v = S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : v = i
  · subst hi; simp [h]
  · simp [hi]

theorem testBit_or_pow (S v x : Nat) : (S ||| 2^v).testBit x = (S.testBit x || decide (v = x)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem miss_step (A B C S v : Nat) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    miss A B C S ≤ miss A B C (S ||| 2^v) + 1 := by
  unfold miss
  rw [testBit_or_pow, testBit_or_pow, testBit_or_pow]
  by_cases a : S.testBit A = true <;> by_cases b : S.testBit B = true <;>
    by_cases c : S.testBit C = true <;> by_cases x : v = A <;> by_cases y : v = B <;>
    by_cases z : v = C <;> simp_all

theorem miss_of_hit {A B C S : Nat} (h : hit A B C S = true) : miss A B C S = 0 := by
  simp only [hit, Bool.and_eq_true] at h
  simp [miss, h.1.1, h.1.2, h.2]

theorem reach_hit {A B C S : Nat} (k b : Nat) (h : hit A B C S = true) : reach A B C k b S = true := by
  cases k with
  | zero => simpa [reach] using h
  | succ k => simp [reach, h]

theorem reach_miss {A B C S k b : Nat} (h : reach A B C k b S = true) :
    hit A B C S = true ∨ miss A B C S ≤ k := by
  cases k with
  | zero => left; simpa [reach] using h
  | succ k =>
    simp only [reach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem classify (S L : Nat) (W : Fin 5 → List Bool) (g : Gate)
    (h31 : S.testBit 31 = true) (h0 : S.testBit 0 = true)
    (hinv : ∀ i < L, ∃ m, m < 32 ∧ S.testBit m = true ∧ ∀ t, (W t).getD i false = m.testBit t.val)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < L) :
    ∃ v, v < 32 ∧ (∀ t, g.op.eval (g.inputs.map fun i => (W t).getD i false) = v.testBit t.val) ∧
      (S.testBit v = true ∨ (g.op ≠ GateOp.not ∧ aoHas S v = true) ∨
        (g.op = GateOp.not ∧ notHas S v = true)) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hin ⊢
  match ins, hlen, hin with
  | [], _, _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨31, by decide, fun t => by simp [GateOp.eval, t31 t], Or.inl h31⟩
    · exact ⟨0, by decide, fun t => by simp [GateOp.eval], Or.inl h0⟩
    · exact ⟨31, by decide, fun t => by simp [GateOp.eval, t31 t], Or.inl h31⟩
  | [i], _, hin =>
    obtain ⟨m, hm, hS, hw⟩ := hinv i (hin i (by simp))
    rcases hop with rfl | rfl | rfl
    · exact ⟨m, hm, fun t => by simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval], Or.inl hS⟩
    · exact ⟨m, hm, fun t => by simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval], Or.inl hS⟩
    · refine ⟨31 ^^^ m, (bits32 m hm m hm).2.2, fun t => ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval, Nat.testBit_xor, t31 t]
      · simp only [notHas, List.any_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, rfl⟩
  | [i, j], _, hin =>
    obtain ⟨m, hm, hS, hw⟩ := hinv i (hin i (by simp))
    obtain ⟨n, hn, hT, hv⟩ := hinv j (hin j (by simp))
    rcases hop with rfl | rfl | rfl
    · refine ⟨m &&& n, (bits32 m hm n hn).1, fun t => ?_, Or.inr (Or.inl ⟨(fun h => nomatch h), ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t, hv t]; simp [GateOp.eval, Nat.testBit_and]
      · simp only [aoHas, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, n, mem_elems.mpr ⟨hn, hT⟩, Or.inl rfl⟩
    · refine ⟨m ||| n, (bits32 m hm n hn).2.1, fun t => ?_, Or.inr (Or.inl ⟨(fun h => nomatch h), ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t, hv t]; simp [GateOp.eval, Nat.testBit_or]
      · simp only [aoHas, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, n, mem_elems.mpr ⟨hn, hT⟩, Or.inr rfl⟩
    · refine ⟨31 ^^^ m, (bits32 m hm m hm).2.2, fun t => ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval, Nat.testBit_xor, t31 t]
      · simp only [notHas, List.any_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, rfl⟩
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

theorem sound (A B C : Nat) (hA : A < 32) (hB : B < 32) (hC : C < 32)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∀ (gs : List Gate) (W : Fin 5 → List Bool) (L S k b : Nat),
      (∀ t, (W t).length = L) → S.testBit 31 = true → S.testBit 0 = true →
      (∀ i < L, ∃ m, m < 32 ∧ S.testBit m = true ∧ ∀ t, (W t).getD i false = m.testBit t.val) →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + j) →
      gs.length ≤ k → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b →
      ∀ p q r, p < L + gs.length → q < L + gs.length → r < L + gs.length →
      (∀ t : Fin 5, (gs.foldl stepW (W t)).getD p false = A.testBit t.val ∧
        (gs.foldl stepW (W t)).getD q false = B.testBit t.val ∧
        (gs.foldl stepW (W t)).getD r false = C.testBit t.val) →
      reach A B C k b S = true := by
  intro gs
  induction gs with
  | nil =>
    intro W L S k b _ _ _ hinv _ _ _ _ p q r hp hq hr ht
    simp only [List.length_nil, Nat.add_zero, List.foldl_nil] at hp hq hr ht
    apply reach_hit
    obtain ⟨m1, h1, s1, w1⟩ := hinv p hp
    obtain ⟨m2, h2, s2, w2⟩ := hinv q hq
    obtain ⟨m3, h3, s3, w3⟩ := hinv r hr
    have e1 : m1 = A := uniq32 m1 h1 A hA (fun t => by rw [← w1 t, (ht t).1])
    have e2 : m2 = B := uniq32 m2 h2 B hB (fun t => by rw [← w2 t, (ht t).2.1])
    have e3 : m3 = C := uniq32 m3 h3 C hC (fun t => by rw [← w3 t, (ht t).2.2])
    subst e1 e2 e3
    simp [hit, s1, s2, s3]
  | cons g gs ih =>
    intro W L S k b hlen h31 h0 hinv hfan hrb hk hb p q r hp hq hr ht
    have hg := hfan g (by simp)
    have hin : ∀ i ∈ g.inputs, i < L := by
      intro i hi; have := hrb 0 (by simp) i (by simpa using hi); simpa using this
    obtain ⟨v, hv, hval, hcls⟩ := classify S L W g h31 h0 hinv hg.1 hg.2 hin
    let W' : Fin 5 → List Bool := fun t => stepW (W t) g
    have hlen' : ∀ t, (W' t).length = L + 1 := by intro t; simp [W', stepW, hlen t]
    have hinv' : ∀ i < L + 1, ∃ m, m < 32 ∧ (S ||| 2^v).testBit m = true ∧
        ∀ t, (W' t).getD i false = m.testBit t.val := by
      intro i hi
      by_cases hiL : i < L
      · obtain ⟨m, hm, hS, hw⟩ := hinv i hiL
        refine ⟨m, hm, by rw [testBit_or_pow, hS, Bool.true_or], fun t => ?_⟩
        simp only [W', stepW]
        rw [List.getD_append _ _ _ _ (by rw [hlen t]; exact hiL)]
        exact hw t
      · have hiE : i = L := by omega
        subst hiE
        refine ⟨v, hv, by rw [testBit_or_pow]; simp, fun t => ?_⟩
        simp only [W', stepW]
        rw [List.getD_append_right _ _ _ _ (by rw [hlen t]), hlen t, Nat.sub_self]
        exact hval t
    have hfan' : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + 1 + j := by
      intro j hj i hi
      have := hrb (j+1) (by simp; omega) i (by simpa using hi)
      omega
    have h31' : (S ||| 2^v).testBit 31 = true := by rw [testBit_or_pow, h31, Bool.true_or]
    have h00' : (S ||| 2^v).testBit 0 = true := by rw [testBit_or_pow, h0, Bool.true_or]
    simp only [List.length_cons] at hk hp hq hr
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have ht' : ∀ t : Fin 5, (gs.foldl stepW (W' t)).getD p false = A.testBit t.val ∧
        (gs.foldl stepW (W' t)).getD q false = B.testBit t.val ∧
        (gs.foldl stepW (W' t)).getD r false = C.testBit t.val := fun t => ht t
    have key : ∀ b', PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b' →
        reach A B C k b' (S ||| 2^v) = true := fun b' hb' =>
      ih W' (L+1) (S ||| 2^v) k b' hlen' h31' h00' hinv' hfan' hrb' (by omega) hb' p q r
        (by omega) (by omega) (by omega) ht'
    have hbn : g.op = GateOp.not →
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b - 1 ∧ 0 < b := by
      intro hn; simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hb ⊢; omega
    have hbo : g.op ≠ GateOp.not →
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b := by
      intro hn; simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hb ⊢; omega
    have miss_ok : ∀ b', reach A B C k b' (S ||| 2^v) = true → miss A B C S ≤ k + 1 := by
      intro b' hR
      have := miss_step A B C S v hAB hAC hBC
      rcases reach_miss hR with hh | hh
      · have := miss_of_hit hh; omega
      · omega
    simp only [reach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    by_cases hn : g.op = GateOp.not
    · have hR := key (b-1) (hbn hn).1
      refine ⟨miss_ok _ hR, ?_⟩
      by_cases hsv : S.testBit v = true
      · rw [or_pow_self hsv] at hR
        exact Or.inl (Or.inr ⟨(hbn hn).2, hR⟩)
      · right
        rw [List.any_eq_true]
        refine ⟨v, List.mem_range.mpr hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        refine ⟨by simpa using hsv, ?_⟩
        rcases hcls with h | ⟨hn', h⟩ | ⟨_, h⟩
        · exact absurd h hsv
        · exact absurd hn hn'
        · exact Or.inr ⟨⟨(hbn hn).2, h⟩, hR⟩
    · have hR := key b (hbo hn)
      refine ⟨miss_ok _ hR, ?_⟩
      by_cases hsv : S.testBit v = true
      · rw [or_pow_self hsv] at hR
        exact Or.inl (Or.inl hR)
      · right
        rw [List.any_eq_true]
        refine ⟨v, List.mem_range.mpr hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        refine ⟨by simpa using hsv, ?_⟩
        rcases hcls with h | ⟨_, h⟩ | ⟨hn', h⟩
        · exact absurd h hsv
        · exact Or.inl ⟨h, hR⟩
        · exact absurd hn' hn

def S0 : Nat := 2^30 ||| 2^28 ||| 2^24 ||| 2^16 ||| 2^0 ||| 2^31

def body (A B C k b S v : Nat) : Bool := !S.testBit v &&
  ((aoHas S v && reach A B C k b (S ||| 2^v)) ||
   (decide (0 < b) && notHas S v && reach A B C k (b-1) (S ||| 2^v)))

theorem reach_split (A B C k b S : Nat) (h1 : hit A B C S = false)
    (h2 : reach A B C k b S = false) (h3 : reach A B C k (b-1) S = false)
    (h4 : ∀ v < 32, body A B C k b S v = false) : reach A B C (k+1) b S = false := by
  have h5 : (List.range 32).any (fun v => !S.testBit v &&
         ((aoHas S v && reach A B C k b (S ||| 2^v)) ||
          (decide (0 < b) && notHas S v && reach A B C k (b-1) (S ||| 2^v)))) = false := by
    rw [List.any_eq_false]; intro v hv
    have := h4 v (List.mem_range.mp hv)
    simp only [body] at this
    simp [this]
  rw [reach, h1, h2, h3, h5]
  simp

theorem s1 : hit 2 4 8 S0 = false := by decide +kernel
theorem s2 : reach 2 4 8 5 2 S0 = false := by decide +kernel
theorem s3 : reach 2 4 8 5 1 S0 = false := by decide +kernel
theorem body_of (A B C k b S v : Nat) (h1 : reach A B C k b (S ||| 2^v) = false)
    (h2 : reach A B C k (b-1) (S ||| 2^v) = false) : body A B C k b S v = false := by
  simp [body, h1, h2]
theorem body_ao (A B C k b S v : Nat) (h0 : notHas S v = false) (h1 : reach A B C k b (S ||| 2^v) = false) :
    body A B C k b S v = false := by
  simp [body, h0, h1]
theorem body_nt (A B C k b S v : Nat) (h0 : aoHas S v = false) (h2 : reach A B C k (b-1) (S ||| 2^v) = false) :
    body A B C k b S v = false := by
  simp [body, h0, h2]

theorem c0 : body 2 4 8 5 2 S0 0 = false := by decide +kernel
theorem u1_1_h : hit 2 4 8 (S0 ||| 2^1) = false := by decide +kernel
theorem u1_1_r : reach 2 4 8 4 1 (S0 ||| 2^1) = false := by decide +kernel
theorem u1_1_q : reach 2 4 8 4 0 (S0 ||| 2^1) = false := by decide +kernel
theorem u1_1_c0 : body 2 4 8 4 1 (S0 ||| 2^1) 0 = false := by decide +kernel
theorem u1_1_c1 : body 2 4 8 4 1 (S0 ||| 2^1) 1 = false := by decide +kernel
theorem u1_1_c2 : body 2 4 8 4 1 (S0 ||| 2^1) 2 = false := by decide +kernel
theorem u1_1_c3 : body 2 4 8 4 1 (S0 ||| 2^1) 3 = false := by decide +kernel
theorem u1_1_c4 : body 2 4 8 4 1 (S0 ||| 2^1) 4 = false := by decide +kernel
theorem u1_1_c5 : body 2 4 8 4 1 (S0 ||| 2^1) 5 = false := by decide +kernel
theorem u1_1_c6 : body 2 4 8 4 1 (S0 ||| 2^1) 6 = false := by decide +kernel
theorem u1_1_c7 : body 2 4 8 4 1 (S0 ||| 2^1) 7 = false := by decide +kernel
theorem u1_1_c8 : body 2 4 8 4 1 (S0 ||| 2^1) 8 = false := by decide +kernel
theorem u1_1_c9 : body 2 4 8 4 1 (S0 ||| 2^1) 9 = false := by decide +kernel
theorem u1_1_c10 : body 2 4 8 4 1 (S0 ||| 2^1) 10 = false := by decide +kernel
theorem u1_1_c11 : body 2 4 8 4 1 (S0 ||| 2^1) 11 = false := by decide +kernel
theorem u1_1_c12 : body 2 4 8 4 1 (S0 ||| 2^1) 12 = false := by decide +kernel
theorem u1_1_c13 : body 2 4 8 4 1 (S0 ||| 2^1) 13 = false := by decide +kernel
theorem u1_1_c14 : body 2 4 8 4 1 (S0 ||| 2^1) 14 = false := by decide +kernel
theorem u1_1_c15 : body 2 4 8 4 1 (S0 ||| 2^1) 15 = false := by decide +kernel
theorem u1_1_c16 : body 2 4 8 4 1 (S0 ||| 2^1) 16 = false := by decide +kernel
theorem u1_1_c17 : body 2 4 8 4 1 (S0 ||| 2^1) 17 = false := by decide +kernel
theorem u1_1_c18 : body 2 4 8 4 1 (S0 ||| 2^1) 18 = false := by decide +kernel
theorem u1_1_c19 : body 2 4 8 4 1 (S0 ||| 2^1) 19 = false := by decide +kernel
theorem u1_1_c20 : body 2 4 8 4 1 (S0 ||| 2^1) 20 = false := by decide +kernel
theorem u1_1_c21 : body 2 4 8 4 1 (S0 ||| 2^1) 21 = false := by decide +kernel
theorem u1_1_c22 : body 2 4 8 4 1 (S0 ||| 2^1) 22 = false := by decide +kernel
theorem u1_1_c23 : body 2 4 8 4 1 (S0 ||| 2^1) 23 = false := by decide +kernel
theorem u1_1_c24 : body 2 4 8 4 1 (S0 ||| 2^1) 24 = false := by decide +kernel
theorem u1_1_c25 : body 2 4 8 4 1 (S0 ||| 2^1) 25 = false := by decide +kernel
theorem u1_1_c26 : body 2 4 8 4 1 (S0 ||| 2^1) 26 = false := by decide +kernel
theorem u1_1_c27 : body 2 4 8 4 1 (S0 ||| 2^1) 27 = false := by decide +kernel
theorem u1_1_c28 : body 2 4 8 4 1 (S0 ||| 2^1) 28 = false := by decide +kernel
theorem u1_1_c29 : body 2 4 8 4 1 (S0 ||| 2^1) 29 = false := by decide +kernel
theorem u1_1_c30 : body 2 4 8 4 1 (S0 ||| 2^1) 30 = false := by decide +kernel
theorem u1_1_c31 : body 2 4 8 4 1 (S0 ||| 2^1) 31 = false := by decide +kernel
theorem u1_1_a : ∀ w < 32, body 2 4 8 4 1 (S0 ||| 2^1) w = false := by
  intro w hw
  match w, hw with
  | 0, _ => exact u1_1_c0
  | 1, _ => exact u1_1_c1
  | 2, _ => exact u1_1_c2
  | 3, _ => exact u1_1_c3
  | 4, _ => exact u1_1_c4
  | 5, _ => exact u1_1_c5
  | 6, _ => exact u1_1_c6
  | 7, _ => exact u1_1_c7
  | 8, _ => exact u1_1_c8
  | 9, _ => exact u1_1_c9
  | 10, _ => exact u1_1_c10
  | 11, _ => exact u1_1_c11
  | 12, _ => exact u1_1_c12
  | 13, _ => exact u1_1_c13
  | 14, _ => exact u1_1_c14
  | 15, _ => exact u1_1_c15
  | 16, _ => exact u1_1_c16
  | 17, _ => exact u1_1_c17
  | 18, _ => exact u1_1_c18
  | 19, _ => exact u1_1_c19
  | 20, _ => exact u1_1_c20
  | 21, _ => exact u1_1_c21
  | 22, _ => exact u1_1_c22
  | 23, _ => exact u1_1_c23
  | 24, _ => exact u1_1_c24
  | 25, _ => exact u1_1_c25
  | 26, _ => exact u1_1_c26
  | 27, _ => exact u1_1_c27
  | 28, _ => exact u1_1_c28
  | 29, _ => exact u1_1_c29
  | 30, _ => exact u1_1_c30
  | 31, _ => exact u1_1_c31
  | n+32, h => exact absurd h (by omega)
theorem u1_1 : reach 2 4 8 5 1 (S0 ||| 2^1) = false := reach_split _ _ _ _ _ _ u1_1_h u1_1_r u1_1_q u1_1_a
theorem a1 : aoHas S0 1 = false := by decide +kernel
theorem c1 : body 2 4 8 5 2 S0 1 = false := body_nt _ _ _ _ _ _ _ a1 u1_1
theorem c2 : body 2 4 8 5 2 S0 2 = false := by decide +kernel
theorem u3_1_h : hit 2 4 8 (S0 ||| 2^3) = false := by decide +kernel
theorem u3_1_r : reach 2 4 8 4 1 (S0 ||| 2^3) = false := by decide +kernel
theorem u3_1_q : reach 2 4 8 4 0 (S0 ||| 2^3) = false := by decide +kernel
theorem u3_1_c0 : body 2 4 8 4 1 (S0 ||| 2^3) 0 = false := by decide +kernel
theorem u3_1_c1 : body 2 4 8 4 1 (S0 ||| 2^3) 1 = false := by decide +kernel
theorem u3_1_c2 : body 2 4 8 4 1 (S0 ||| 2^3) 2 = false := by decide +kernel
theorem u3_1_c3 : body 2 4 8 4 1 (S0 ||| 2^3) 3 = false := by decide +kernel
theorem u3_1_c4 : body 2 4 8 4 1 (S0 ||| 2^3) 4 = false := by decide +kernel
theorem u3_1_c5 : body 2 4 8 4 1 (S0 ||| 2^3) 5 = false := by decide +kernel
theorem u3_1_c6 : body 2 4 8 4 1 (S0 ||| 2^3) 6 = false := by decide +kernel
theorem u3_1_c7 : body 2 4 8 4 1 (S0 ||| 2^3) 7 = false := by decide +kernel
theorem u3_1_c8 : body 2 4 8 4 1 (S0 ||| 2^3) 8 = false := by decide +kernel
theorem u3_1_c9 : body 2 4 8 4 1 (S0 ||| 2^3) 9 = false := by decide +kernel
theorem u3_1_c10 : body 2 4 8 4 1 (S0 ||| 2^3) 10 = false := by decide +kernel
theorem u3_1_c11 : body 2 4 8 4 1 (S0 ||| 2^3) 11 = false := by decide +kernel
theorem u3_1_c12 : body 2 4 8 4 1 (S0 ||| 2^3) 12 = false := by decide +kernel
theorem u3_1_c13 : body 2 4 8 4 1 (S0 ||| 2^3) 13 = false := by decide +kernel
theorem u3_1_c14 : body 2 4 8 4 1 (S0 ||| 2^3) 14 = false := by decide +kernel
theorem u3_1_c15 : body 2 4 8 4 1 (S0 ||| 2^3) 15 = false := by decide +kernel
theorem u3_1_c16 : body 2 4 8 4 1 (S0 ||| 2^3) 16 = false := by decide +kernel
theorem u3_1_c17 : body 2 4 8 4 1 (S0 ||| 2^3) 17 = false := by decide +kernel
theorem u3_1_c18 : body 2 4 8 4 1 (S0 ||| 2^3) 18 = false := by decide +kernel
theorem u3_1_c19 : body 2 4 8 4 1 (S0 ||| 2^3) 19 = false := by decide +kernel
theorem u3_1_c20 : body 2 4 8 4 1 (S0 ||| 2^3) 20 = false := by decide +kernel
theorem u3_1_c21 : body 2 4 8 4 1 (S0 ||| 2^3) 21 = false := by decide +kernel
theorem u3_1_c22 : body 2 4 8 4 1 (S0 ||| 2^3) 22 = false := by decide +kernel
theorem u3_1_c23 : body 2 4 8 4 1 (S0 ||| 2^3) 23 = false := by decide +kernel
theorem u3_1_c24 : body 2 4 8 4 1 (S0 ||| 2^3) 24 = false := by decide +kernel
theorem u3_1_c25 : body 2 4 8 4 1 (S0 ||| 2^3) 25 = false := by decide +kernel
theorem u3_1_c26 : body 2 4 8 4 1 (S0 ||| 2^3) 26 = false := by decide +kernel
theorem u3_1_c27 : body 2 4 8 4 1 (S0 ||| 2^3) 27 = false := by decide +kernel
theorem u3_1_c28 : body 2 4 8 4 1 (S0 ||| 2^3) 28 = false := by decide +kernel
theorem u3_1_c29 : body 2 4 8 4 1 (S0 ||| 2^3) 29 = false := by decide +kernel
theorem u3_1_c30 : body 2 4 8 4 1 (S0 ||| 2^3) 30 = false := by decide +kernel
theorem u3_1_c31 : body 2 4 8 4 1 (S0 ||| 2^3) 31 = false := by decide +kernel
theorem u3_1_a : ∀ w < 32, body 2 4 8 4 1 (S0 ||| 2^3) w = false := by
  intro w hw
  match w, hw with
  | 0, _ => exact u3_1_c0
  | 1, _ => exact u3_1_c1
  | 2, _ => exact u3_1_c2
  | 3, _ => exact u3_1_c3
  | 4, _ => exact u3_1_c4
  | 5, _ => exact u3_1_c5
  | 6, _ => exact u3_1_c6
  | 7, _ => exact u3_1_c7
  | 8, _ => exact u3_1_c8
  | 9, _ => exact u3_1_c9
  | 10, _ => exact u3_1_c10
  | 11, _ => exact u3_1_c11
  | 12, _ => exact u3_1_c12
  | 13, _ => exact u3_1_c13
  | 14, _ => exact u3_1_c14
  | 15, _ => exact u3_1_c15
  | 16, _ => exact u3_1_c16
  | 17, _ => exact u3_1_c17
  | 18, _ => exact u3_1_c18
  | 19, _ => exact u3_1_c19
  | 20, _ => exact u3_1_c20
  | 21, _ => exact u3_1_c21
  | 22, _ => exact u3_1_c22
  | 23, _ => exact u3_1_c23
  | 24, _ => exact u3_1_c24
  | 25, _ => exact u3_1_c25
  | 26, _ => exact u3_1_c26
  | 27, _ => exact u3_1_c27
  | 28, _ => exact u3_1_c28
  | 29, _ => exact u3_1_c29
  | 30, _ => exact u3_1_c30
  | 31, _ => exact u3_1_c31
  | n+32, h => exact absurd h (by omega)
theorem u3_1 : reach 2 4 8 5 1 (S0 ||| 2^3) = false := reach_split _ _ _ _ _ _ u3_1_h u3_1_r u3_1_q u3_1_a
theorem a3 : aoHas S0 3 = false := by decide +kernel
theorem c3 : body 2 4 8 5 2 S0 3 = false := body_nt _ _ _ _ _ _ _ a3 u3_1
theorem c4 : body 2 4 8 5 2 S0 4 = false := by decide +kernel
theorem c5 : body 2 4 8 5 2 S0 5 = false := by decide +kernel
theorem c6 : body 2 4 8 5 2 S0 6 = false := by decide +kernel
theorem u7_1_h : hit 2 4 8 (S0 ||| 2^7) = false := by decide +kernel
theorem u7_1_r : reach 2 4 8 4 1 (S0 ||| 2^7) = false := by decide +kernel
theorem u7_1_q : reach 2 4 8 4 0 (S0 ||| 2^7) = false := by decide +kernel
theorem u7_1_c0 : body 2 4 8 4 1 (S0 ||| 2^7) 0 = false := by decide +kernel
theorem u7_1_c1 : body 2 4 8 4 1 (S0 ||| 2^7) 1 = false := by decide +kernel
theorem u7_1_c2 : body 2 4 8 4 1 (S0 ||| 2^7) 2 = false := by decide +kernel
theorem u7_1_c3 : body 2 4 8 4 1 (S0 ||| 2^7) 3 = false := by decide +kernel
theorem u7_1_c4 : body 2 4 8 4 1 (S0 ||| 2^7) 4 = false := by decide +kernel
theorem u7_1_c5 : body 2 4 8 4 1 (S0 ||| 2^7) 5 = false := by decide +kernel
theorem u7_1_c6 : body 2 4 8 4 1 (S0 ||| 2^7) 6 = false := by decide +kernel
theorem u7_1_c7 : body 2 4 8 4 1 (S0 ||| 2^7) 7 = false := by decide +kernel
theorem u7_1_c8 : body 2 4 8 4 1 (S0 ||| 2^7) 8 = false := by decide +kernel
theorem u7_1_c9 : body 2 4 8 4 1 (S0 ||| 2^7) 9 = false := by decide +kernel
theorem u7_1_c10 : body 2 4 8 4 1 (S0 ||| 2^7) 10 = false := by decide +kernel
theorem u7_1_c11 : body 2 4 8 4 1 (S0 ||| 2^7) 11 = false := by decide +kernel
theorem u7_1_c12 : body 2 4 8 4 1 (S0 ||| 2^7) 12 = false := by decide +kernel
theorem u7_1_c13 : body 2 4 8 4 1 (S0 ||| 2^7) 13 = false := by decide +kernel
theorem u7_1_c14 : body 2 4 8 4 1 (S0 ||| 2^7) 14 = false := by decide +kernel
theorem u7_1_c15 : body 2 4 8 4 1 (S0 ||| 2^7) 15 = false := by decide +kernel
theorem u7_1_c16 : body 2 4 8 4 1 (S0 ||| 2^7) 16 = false := by decide +kernel
theorem u7_1_c17 : body 2 4 8 4 1 (S0 ||| 2^7) 17 = false := by decide +kernel
theorem u7_1_c18 : body 2 4 8 4 1 (S0 ||| 2^7) 18 = false := by decide +kernel
theorem u7_1_c19 : body 2 4 8 4 1 (S0 ||| 2^7) 19 = false := by decide +kernel
theorem u7_1_c20 : body 2 4 8 4 1 (S0 ||| 2^7) 20 = false := by decide +kernel
theorem u7_1_c21 : body 2 4 8 4 1 (S0 ||| 2^7) 21 = false := by decide +kernel
theorem u7_1_c22 : body 2 4 8 4 1 (S0 ||| 2^7) 22 = false := by decide +kernel
theorem u7_1_c23 : body 2 4 8 4 1 (S0 ||| 2^7) 23 = false := by decide +kernel
theorem u7_1_c24 : body 2 4 8 4 1 (S0 ||| 2^7) 24 = false := by decide +kernel
theorem u7_1_c25 : body 2 4 8 4 1 (S0 ||| 2^7) 25 = false := by decide +kernel
theorem u7_1_c26 : body 2 4 8 4 1 (S0 ||| 2^7) 26 = false := by decide +kernel
theorem u7_1_c27 : body 2 4 8 4 1 (S0 ||| 2^7) 27 = false := by decide +kernel
theorem u7_1_c28 : body 2 4 8 4 1 (S0 ||| 2^7) 28 = false := by decide +kernel
theorem u7_1_c29 : body 2 4 8 4 1 (S0 ||| 2^7) 29 = false := by decide +kernel
theorem u7_1_c30 : body 2 4 8 4 1 (S0 ||| 2^7) 30 = false := by decide +kernel
theorem u7_1_c31 : body 2 4 8 4 1 (S0 ||| 2^7) 31 = false := by decide +kernel
theorem u7_1_a : ∀ w < 32, body 2 4 8 4 1 (S0 ||| 2^7) w = false := by
  intro w hw
  match w, hw with
  | 0, _ => exact u7_1_c0
  | 1, _ => exact u7_1_c1
  | 2, _ => exact u7_1_c2
  | 3, _ => exact u7_1_c3
  | 4, _ => exact u7_1_c4
  | 5, _ => exact u7_1_c5
  | 6, _ => exact u7_1_c6
  | 7, _ => exact u7_1_c7
  | 8, _ => exact u7_1_c8
  | 9, _ => exact u7_1_c9
  | 10, _ => exact u7_1_c10
  | 11, _ => exact u7_1_c11
  | 12, _ => exact u7_1_c12
  | 13, _ => exact u7_1_c13
  | 14, _ => exact u7_1_c14
  | 15, _ => exact u7_1_c15
  | 16, _ => exact u7_1_c16
  | 17, _ => exact u7_1_c17
  | 18, _ => exact u7_1_c18
  | 19, _ => exact u7_1_c19
  | 20, _ => exact u7_1_c20
  | 21, _ => exact u7_1_c21
  | 22, _ => exact u7_1_c22
  | 23, _ => exact u7_1_c23
  | 24, _ => exact u7_1_c24
  | 25, _ => exact u7_1_c25
  | 26, _ => exact u7_1_c26
  | 27, _ => exact u7_1_c27
  | 28, _ => exact u7_1_c28
  | 29, _ => exact u7_1_c29
  | 30, _ => exact u7_1_c30
  | 31, _ => exact u7_1_c31
  | n+32, h => exact absurd h (by omega)
theorem u7_1 : reach 2 4 8 5 1 (S0 ||| 2^7) = false := reach_split _ _ _ _ _ _ u7_1_h u7_1_r u7_1_q u7_1_a
theorem a7 : aoHas S0 7 = false := by decide +kernel
theorem c7 : body 2 4 8 5 2 S0 7 = false := body_nt _ _ _ _ _ _ _ a7 u7_1
theorem c8 : body 2 4 8 5 2 S0 8 = false := by decide +kernel
theorem c9 : body 2 4 8 5 2 S0 9 = false := by decide +kernel
theorem c10 : body 2 4 8 5 2 S0 10 = false := by decide +kernel
theorem c11 : body 2 4 8 5 2 S0 11 = false := by decide +kernel
theorem c12 : body 2 4 8 5 2 S0 12 = false := by decide +kernel
theorem c13 : body 2 4 8 5 2 S0 13 = false := by decide +kernel
theorem c14 : body 2 4 8 5 2 S0 14 = false := by decide +kernel
theorem u15_1_h : hit 2 4 8 (S0 ||| 2^15) = false := by decide +kernel
theorem u15_1_r : reach 2 4 8 4 1 (S0 ||| 2^15) = false := by decide +kernel
theorem u15_1_q : reach 2 4 8 4 0 (S0 ||| 2^15) = false := by decide +kernel
theorem u15_1_c0 : body 2 4 8 4 1 (S0 ||| 2^15) 0 = false := by decide +kernel
theorem u15_1_c1 : body 2 4 8 4 1 (S0 ||| 2^15) 1 = false := by decide +kernel
theorem u15_1_c2 : body 2 4 8 4 1 (S0 ||| 2^15) 2 = false := by decide +kernel
theorem u15_1_c3 : body 2 4 8 4 1 (S0 ||| 2^15) 3 = false := by decide +kernel
theorem u15_1_c4 : body 2 4 8 4 1 (S0 ||| 2^15) 4 = false := by decide +kernel
theorem u15_1_c5 : body 2 4 8 4 1 (S0 ||| 2^15) 5 = false := by decide +kernel
theorem u15_1_c6 : body 2 4 8 4 1 (S0 ||| 2^15) 6 = false := by decide +kernel
theorem u15_1_c7 : body 2 4 8 4 1 (S0 ||| 2^15) 7 = false := by decide +kernel
theorem u15_1_c8 : body 2 4 8 4 1 (S0 ||| 2^15) 8 = false := by decide +kernel
theorem u15_1_c9 : body 2 4 8 4 1 (S0 ||| 2^15) 9 = false := by decide +kernel
theorem u15_1_c10 : body 2 4 8 4 1 (S0 ||| 2^15) 10 = false := by decide +kernel
theorem u15_1_c11 : body 2 4 8 4 1 (S0 ||| 2^15) 11 = false := by decide +kernel
theorem u15_1_c12 : body 2 4 8 4 1 (S0 ||| 2^15) 12 = false := by decide +kernel
theorem u15_1_c13 : body 2 4 8 4 1 (S0 ||| 2^15) 13 = false := by decide +kernel
theorem u15_1_c14 : body 2 4 8 4 1 (S0 ||| 2^15) 14 = false := by decide +kernel
theorem u15_1_c15 : body 2 4 8 4 1 (S0 ||| 2^15) 15 = false := by decide +kernel
theorem u15_1_c16 : body 2 4 8 4 1 (S0 ||| 2^15) 16 = false := by decide +kernel
theorem u15_1_c17 : body 2 4 8 4 1 (S0 ||| 2^15) 17 = false := by decide +kernel
theorem u15_1_c18 : body 2 4 8 4 1 (S0 ||| 2^15) 18 = false := by decide +kernel
theorem u15_1_c19 : body 2 4 8 4 1 (S0 ||| 2^15) 19 = false := by decide +kernel
theorem u15_1_c20 : body 2 4 8 4 1 (S0 ||| 2^15) 20 = false := by decide +kernel
theorem u15_1_c21 : body 2 4 8 4 1 (S0 ||| 2^15) 21 = false := by decide +kernel
theorem u15_1_c22 : body 2 4 8 4 1 (S0 ||| 2^15) 22 = false := by decide +kernel
theorem u15_1_c23 : body 2 4 8 4 1 (S0 ||| 2^15) 23 = false := by decide +kernel
theorem u15_1_c24 : body 2 4 8 4 1 (S0 ||| 2^15) 24 = false := by decide +kernel
theorem u15_1_c25 : body 2 4 8 4 1 (S0 ||| 2^15) 25 = false := by decide +kernel
theorem u15_1_c26 : body 2 4 8 4 1 (S0 ||| 2^15) 26 = false := by decide +kernel
theorem u15_1_c27 : body 2 4 8 4 1 (S0 ||| 2^15) 27 = false := by decide +kernel
theorem u15_1_c28 : body 2 4 8 4 1 (S0 ||| 2^15) 28 = false := by decide +kernel
theorem u15_1_c29 : body 2 4 8 4 1 (S0 ||| 2^15) 29 = false := by decide +kernel
theorem u15_1_c30 : body 2 4 8 4 1 (S0 ||| 2^15) 30 = false := by decide +kernel
theorem u15_1_c31 : body 2 4 8 4 1 (S0 ||| 2^15) 31 = false := by decide +kernel
theorem u15_1_a : ∀ w < 32, body 2 4 8 4 1 (S0 ||| 2^15) w = false := by
  intro w hw
  match w, hw with
  | 0, _ => exact u15_1_c0
  | 1, _ => exact u15_1_c1
  | 2, _ => exact u15_1_c2
  | 3, _ => exact u15_1_c3
  | 4, _ => exact u15_1_c4
  | 5, _ => exact u15_1_c5
  | 6, _ => exact u15_1_c6
  | 7, _ => exact u15_1_c7
  | 8, _ => exact u15_1_c8
  | 9, _ => exact u15_1_c9
  | 10, _ => exact u15_1_c10
  | 11, _ => exact u15_1_c11
  | 12, _ => exact u15_1_c12
  | 13, _ => exact u15_1_c13
  | 14, _ => exact u15_1_c14
  | 15, _ => exact u15_1_c15
  | 16, _ => exact u15_1_c16
  | 17, _ => exact u15_1_c17
  | 18, _ => exact u15_1_c18
  | 19, _ => exact u15_1_c19
  | 20, _ => exact u15_1_c20
  | 21, _ => exact u15_1_c21
  | 22, _ => exact u15_1_c22
  | 23, _ => exact u15_1_c23
  | 24, _ => exact u15_1_c24
  | 25, _ => exact u15_1_c25
  | 26, _ => exact u15_1_c26
  | 27, _ => exact u15_1_c27
  | 28, _ => exact u15_1_c28
  | 29, _ => exact u15_1_c29
  | 30, _ => exact u15_1_c30
  | 31, _ => exact u15_1_c31
  | n+32, h => exact absurd h (by omega)
theorem u15_1 : reach 2 4 8 5 1 (S0 ||| 2^15) = false := reach_split _ _ _ _ _ _ u15_1_h u15_1_r u15_1_q u15_1_a
theorem a15 : aoHas S0 15 = false := by decide +kernel
theorem c15 : body 2 4 8 5 2 S0 15 = false := body_nt _ _ _ _ _ _ _ a15 u15_1
theorem c16 : body 2 4 8 5 2 S0 16 = false := by decide +kernel
theorem c17 : body 2 4 8 5 2 S0 17 = false := by decide +kernel
theorem c18 : body 2 4 8 5 2 S0 18 = false := by decide +kernel
theorem c19 : body 2 4 8 5 2 S0 19 = false := by decide +kernel
theorem c20 : body 2 4 8 5 2 S0 20 = false := by decide +kernel
theorem c21 : body 2 4 8 5 2 S0 21 = false := by decide +kernel
theorem c22 : body 2 4 8 5 2 S0 22 = false := by decide +kernel
theorem c23 : body 2 4 8 5 2 S0 23 = false := by decide +kernel
theorem c24 : body 2 4 8 5 2 S0 24 = false := by decide +kernel
theorem c25 : body 2 4 8 5 2 S0 25 = false := by decide +kernel
theorem c26 : body 2 4 8 5 2 S0 26 = false := by decide +kernel
theorem c27 : body 2 4 8 5 2 S0 27 = false := by decide +kernel
theorem c28 : body 2 4 8 5 2 S0 28 = false := by decide +kernel
theorem c29 : body 2 4 8 5 2 S0 29 = false := by decide +kernel
theorem c30 : body 2 4 8 5 2 S0 30 = false := by decide +kernel
theorem c31 : body 2 4 8 5 2 S0 31 = false := by decide +kernel
theorem s4 : ∀ v < 32, body 2 4 8 5 2 S0 v = false := by
  intro v hv
  match v, hv with
  | 0, _ => exact c0
  | 1, _ => exact c1
  | 2, _ => exact c2
  | 3, _ => exact c3
  | 4, _ => exact c4
  | 5, _ => exact c5
  | 6, _ => exact c6
  | 7, _ => exact c7
  | 8, _ => exact c8
  | 9, _ => exact c9
  | 10, _ => exact c10
  | 11, _ => exact c11
  | 12, _ => exact c12
  | 13, _ => exact c13
  | 14, _ => exact c14
  | 15, _ => exact c15
  | 16, _ => exact c16
  | 17, _ => exact c17
  | 18, _ => exact c18
  | 19, _ => exact c19
  | 20, _ => exact c20
  | 21, _ => exact c21
  | 22, _ => exact c22
  | 23, _ => exact c23
  | 24, _ => exact c24
  | 25, _ => exact c25
  | 26, _ => exact c26
  | 27, _ => exact c27
  | 28, _ => exact c28
  | 29, _ => exact c29
  | 30, _ => exact c30
  | 31, _ => exact c31
  | n+32, h => exact absurd h (by omega)

theorem cert : reach 2 4 8 6 2 S0 = false := reach_split _ _ _ _ _ _ s1 s2 s3 s4

theorem init : ∀ i < 6, ∃ m, m < 32 ∧ S0.testBit m = true ∧ ∀ t : Fin 5,
    ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]).getD i false =
      m.testBit t.val := by
  intro i hi
  refine ⟨[30, 28, 24, 16, 0, 31].getD i 0, ?_⟩
  revert i
  decide +kernel

theorem main : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (4 : Nat).testBit t.val ∧
    w.getD r.val false = (8 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hf, hr, hn, hs, ht⟩
  have := sound 2 4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    D.gates (fun t => (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true])
    6 S0 6 2 (fun t => by simp) (by decide) (by decide) init hf hr hs hn p.val q.val r.val
    p.isLt q.isLt r.isLt (fun t => ht t)
  rw [cert] at this
  exact absurd this (by decide)

def D3 : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩], 0⟩

theorem fan3 : PEqualNP.MetaComplexity.FanInTwo D3 := by
  intro g hg
  simp only [D3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_53132

theorem PEqualNP.Outside.L_meta_53132 :
let fits := fun (b : Nat) =>
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
    PEqualNP.NotBracket.notCount D ≤ b ∧ D.size ≤ 6 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (2 : Nat).testBit t.val ∧
      w.getD q.val false = (4 : Nat).testBit t.val ∧
      w.getD r.val false = (8 : Nat).testBit t.val
fits 3 ∧ ¬ fits 2 := by
  intro fits
  refine ⟨⟨PEqualNP.Outside.L_meta_53132.D3, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨10, by decide⟩, PEqualNP.Outside.L_meta_53132.fan3, ?_, ?_, ?_, ?_⟩, PEqualNP.Outside.L_meta_53132.main⟩
  · decide
  · decide
  · decide
  · decide

