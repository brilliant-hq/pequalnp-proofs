import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29725

open PEqualNP.CircuitLowerBounds

abbrev F2 := ZMod 2

def inp {k : ℕ} (x : Fin k → F2) : List Bool := List.ofFn (fun i => decide (x i = 1))

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W {k : ℕ} (gs : List Gate) (x : Fin k → F2) : List Bool := gs.foldl stp (inp x)

def val {k : ℕ} (gs : List Gate) (w : ℕ) (x : Fin k → F2) : Bool := (W gs x).getD w false

theorem fold_pre (hs : List Gate) : ∀ w : List Bool, ∃ t, hs.foldl stp w = w ++ t := by
  induction hs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g hs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stp w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht, stp, List.append_assoc]

theorem W_len {k : ℕ} (gs : List Gate) (x : Fin k → F2) : (W gs x).length = k + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W, inp]
  | append_singleton gs g ih =>
    simp only [W, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    simp [stp, ih]; omega

theorem val_app {k : ℕ} (gs hs : List Gate) (w : ℕ) (hw : w < k + gs.length) (x : Fin k → F2) :
    val (gs ++ hs) w x = val gs w x := by
  unfold val W
  rw [List.foldl_append]
  obtain ⟨t, ht⟩ := fold_pre hs (gs.foldl stp (inp x))
  rw [ht]
  have hl : w < (gs.foldl stp (inp x)).length := by
    have := W_len gs x; unfold W at this; omega
  rw [List.getD_append _ _ _ _ hl]

theorem val_new {k : ℕ} (gs : List Gate) (g : Gate) (x : Fin k → F2) :
    val (gs ++ [g]) (k + gs.length) x = g.op.eval (g.inputs.map fun i => val gs i x) := by
  unfold val W
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, stp]
  have hl := W_len gs x
  unfold W at hl
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hl]

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∧ g.inputs.length = 2) ∨
  (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
  (g.op = .not ∧ g.inputs.length = 1)

def Ok (k : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), Allowed gs[j] ∧ ∀ i ∈ gs[j].inputs, i < k + j

noncomputable def nand (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))

def Step (k : ℕ) (gs gs' : List Gate) (a s : ℕ) : Prop :=
  Ok k gs' ∧ ∃ hs, gs' = gs ++ hs ∧ hs.length ≤ s ∧ nand hs ≤ a

def Comp (k : ℕ) (gs : List Gate) (w : ℕ) (f : (Fin k → F2) → Bool) : Prop :=
  w < k + gs.length ∧ ∀ x, val gs w x = f x

def cnt {k : ℕ} (P : List (ℕ × ((Fin k → F2) → Bool))) (x : Fin k → F2) : ℕ :=
  (P.map (fun q => (q.2 x).toNat)).sum

theorem cnt_nil {k : ℕ} (x : Fin k → F2) : cnt ([] : List (ℕ × ((Fin k → F2) → Bool))) x = 0 := rfl

theorem cnt_cons {k : ℕ} (q : ℕ × ((Fin k → F2) → Bool)) (P : List (ℕ × ((Fin k → F2) → Bool)))
    (x : Fin k → F2) : cnt (q :: P) x = (q.2 x).toNat + cnt P x := by
  simp [cnt]

theorem cnt_le {k : ℕ} (P : List (ℕ × ((Fin k → F2) → Bool))) (x : Fin k → F2) :
    cnt P x ≤ P.length := by
  induction P with
  | nil => simp [cnt]
  | cons q P ih => rw [cnt_cons]; have := Bool.toNat_le (q.2 x); simp; omega

theorem ok_nil (k : ℕ) : Ok k [] := fun j h => absurd h (by simp)

theorem step_refl {k : ℕ} {gs : List Gate} (h : Ok k gs) : Step k gs gs 0 0 :=
  ⟨h, [], by simp, by simp, by simp [nand]⟩

theorem step_trans {k : ℕ} {g0 g1 g2 : List Gate} {a1 s1 a2 s2 : ℕ}
    (h1 : Step k g0 g1 a1 s1) (h2 : Step k g1 g2 a2 s2) : Step k g0 g2 (a1 + a2) (s1 + s2) := by
  obtain ⟨_, hs1, rfl, hl1, hn1⟩ := h1
  obtain ⟨hok2, hs2, rfl, hl2, hn2⟩ := h2
  refine ⟨hok2, hs1 ++ hs2, by simp, by simp; omega, ?_⟩
  simp only [nand, List.countP_append] at hn1 hn2 ⊢
  omega

theorem step_mono {k : ℕ} {g0 g1 : List Gate} {a s a' s' : ℕ}
    (h : Step k g0 g1 a s) (ha : a ≤ a') (hs : s ≤ s') : Step k g0 g1 a' s' := by
  obtain ⟨hok, hs1, rfl, hl1, hn1⟩ := h
  exact ⟨hok, hs1, rfl, by omega, by omega⟩

theorem comp_mono {k : ℕ} {gs gs' : List Gate} {a s w : ℕ} {f : (Fin k → F2) → Bool}
    (h : Step k gs gs' a s) (hc : Comp k gs w f) : Comp k gs' w f := by
  obtain ⟨_, hs, rfl, _, _⟩ := h
  refine ⟨by rw [List.length_append]; have := hc.1; omega, fun x => ?_⟩
  rw [val_app gs hs w hc.1 x]
  exact hc.2 x

theorem comps_mono {k : ℕ} {gs gs' : List Gate} {a s : ℕ}
    {P : List (ℕ × ((Fin k → F2) → Bool))}
    (h : Step k gs gs' a s) (hc : ∀ q ∈ P, Comp k gs q.1 q.2) : ∀ q ∈ P, Comp k gs' q.1 q.2 :=
  fun q hq => comp_mono h (hc q hq)

theorem comp_ext {k : ℕ} {gs : List Gate} {w : ℕ} {f g : (Fin k → F2) → Bool}
    (hc : Comp k gs w f) (he : ∀ x, f x = g x) : Comp k gs w g :=
  ⟨hc.1, fun x => (hc.2 x).trans (he x)⟩

theorem ok_snoc {k : ℕ} {gs : List Gate} {g : Gate} (hok : Ok k gs) (ha : Allowed g)
    (hi : ∀ i ∈ g.inputs, i < k + gs.length) : Ok k (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]
    exact hok j hlt
  · have hj' : j = gs.length := by omega
    subst hj'
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_singleton]
    exact ⟨ha, hi⟩

theorem emit {k : ℕ} {gs : List Gate} (g : Gate) (hok : Ok k gs) (ha : Allowed g)
    (hi : ∀ i ∈ g.inputs, i < k + gs.length) :
    Step k gs (gs ++ [g]) (nand [g]) 1 ∧
      Comp k (gs ++ [g]) (k + gs.length) (fun x => g.op.eval (g.inputs.map fun i => val gs i x)) :=
  ⟨⟨ok_snoc hok ha hi, [g], rfl, by simp, le_refl _⟩,
    ⟨by simp, fun x => val_new gs g x⟩⟩

theorem nand_and (a b : ℕ) : nand [⟨GateOp.and, [a, b]⟩] = 1 := by
  simp [nand]

theorem nand_mod (l : List ℕ) : nand [⟨GateOp.mod 2, l⟩] = 0 := by
  simp [nand]

theorem nand_not (l : List ℕ) : nand [⟨GateOp.not, l⟩] = 0 := by
  simp [nand]

theorem mk_and {k : ℕ} {gs : List Gate} {a b : ℕ} {fa fb : (Fin k → F2) → Bool}
    (hok : Ok k gs) (ha : Comp k gs a fa) (hb : Comp k gs b fb) :
    ∃ gs' w, Step k gs gs' 1 1 ∧ Comp k gs' w (fun x => fa x && fb x) := by
  obtain ⟨h1, h2⟩ := emit (k := k) ⟨GateOp.and, [a, b]⟩ hok (Or.inl ⟨rfl, rfl⟩)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  rw [nand_and] at h1
  refine ⟨_, _, h1, comp_ext h2 (fun x => ?_)⟩
  simp [GateOp.eval, ha.2 x, hb.2 x]

theorem mk_not {k : ℕ} {gs : List Gate} {a : ℕ} {fa : (Fin k → F2) → Bool}
    (hok : Ok k gs) (ha : Comp k gs a fa) :
    ∃ gs' w, Step k gs gs' 0 1 ∧ Comp k gs' w (fun x => !fa x) := by
  obtain ⟨h1, h2⟩ := emit (k := k) ⟨GateOp.not, [a]⟩ hok (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (by intro i hi; simp at hi; rcases hi with rfl; exact ha.1)
  rw [nand_not] at h1
  refine ⟨_, _, h1, comp_ext h2 (fun x => ?_)⟩
  simp [GateOp.eval, ha.2 x]

theorem mk_true {k : ℕ} {gs : List Gate} (hok : Ok k gs) :
    ∃ gs' w, Step k gs gs' 0 1 ∧ Comp k gs' w (fun _ => true) := by
  obtain ⟨h1, h2⟩ := emit (k := k) ⟨GateOp.mod 2, []⟩ hok (Or.inr (Or.inl ⟨rfl, by simp⟩))
    (by simp)
  rw [nand_mod] at h1
  refine ⟨_, _, h1, comp_ext h2 (fun x => ?_)⟩
  simp [GateOp.eval]

theorem mk_xnor {k : ℕ} {gs : List Gate} {a b : ℕ} {fa fb : (Fin k → F2) → Bool}
    (hok : Ok k gs) (ha : Comp k gs a fa) (hb : Comp k gs b fb) :
    ∃ gs' w, Step k gs gs' 0 1 ∧ Comp k gs' w (fun x => !(xor (fa x) (fb x))) := by
  obtain ⟨h1, h2⟩ := emit (k := k) ⟨GateOp.mod 2, [a, b]⟩ hok (Or.inr (Or.inl ⟨rfl, by simp⟩))
    (by intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1)
  rw [nand_mod] at h1
  refine ⟨_, _, h1, comp_ext h2 (fun x => ?_)⟩
  simp only [GateOp.eval, List.map_cons, List.map_nil, ha.2 x, hb.2 x]
  cases fa x <;> cases fb x <;> decide

theorem mk_xor {k : ℕ} {gs : List Gate} {a b : ℕ} {fa fb : (Fin k → F2) → Bool}
    (hok : Ok k gs) (ha : Comp k gs a fa) (hb : Comp k gs b fb) :
    ∃ gs' w, Step k gs gs' 0 2 ∧ Comp k gs' w (fun x => xor (fa x) (fb x)) := by
  obtain ⟨g1, w1, s1, c1⟩ := mk_xnor hok ha hb
  obtain ⟨g2, w2, s2, c2⟩ := mk_not s1.1 c1
  exact ⟨g2, w2, step_trans s1 s2, comp_ext c2 (fun x => by simp)⟩

theorem mk_false {k : ℕ} {gs : List Gate} (hok : Ok k gs) :
    ∃ gs' w, Step k gs gs' 0 2 ∧ Comp k gs' w (fun _ => false) := by
  obtain ⟨g1, w1, s1, c1⟩ := mk_true hok
  obtain ⟨g2, w2, s2, c2⟩ := mk_not s1.1 c1
  exact ⟨g2, w2, step_trans s1 s2, comp_ext c2 (fun x => by simp)⟩

theorem comp_inp {k : ℕ} (gs : List Gate) (i : Fin k) :
    Comp k gs i.val (fun x => decide (x i = 1)) := by
  refine ⟨by omega, fun x => ?_⟩
  have h0 : val gs i.val x = val ([] ++ gs) i.val x := by simp
  rw [h0, val_app [] gs i.val (by simp) x]
  simp [val, W, inp, List.getD_eq_getElem?_getD]

theorem maj (u y z : Bool) : u.toNat + y.toNat + z.toNat =
    (xor (xor u y) z).toNat + 2 * (xor u ((xor u y) && (xor u z))).toNat := by
  cases u <;> cases y <;> cases z <;> rfl

theorem half (u y : Bool) : u.toNat + y.toNat = (xor u y).toNat + 2 * (u && y).toNat := by
  cases u <;> cases y <;> rfl

abbrev Sig (k : ℕ) := ℕ × ((Fin k → F2) → Bool)

theorem chain (k : ℕ) : ∀ (rest : List (Sig k)) (gs : List Gate) (u : ℕ)
    (U : (Fin k → F2) → Bool), Ok k gs → Comp k gs u U → (∀ q ∈ rest, Comp k gs q.1 q.2) →
    ∃ gs' u' U' cs, Step k gs gs' ((rest.length + 1) / 2) (9 * ((rest.length + 1) / 2)) ∧
      Comp k gs' u' U' ∧ (∀ q ∈ cs, Comp k gs' q.1 q.2) ∧
      cs.length = (rest.length + 1) / 2 ∧
      ∀ x, (U x).toNat + cnt rest x = (U' x).toNat + 2 * cnt cs x
  | [], gs, u, U, hok, hu, _ => ⟨gs, u, U, [], step_mono (step_refl hok) (by simp) (by simp), hu,
      by simp, by simp,
      fun x => by simp [cnt]⟩
  | [y], gs, u, U, hok, hu, hr => by
    have hy := hr y (by simp)
    obtain ⟨g1, c, s1, hc⟩ := mk_and hok hu hy
    obtain ⟨g2, u', s2, hu'⟩ := mk_xor s1.1 (comp_mono s1 hu) (comp_mono s1 hy)
    refine ⟨g2, u', _, [(c, fun x => U x && y.2 x)], step_mono (step_trans s1 s2)
      (by simp) (by simp), hu', ?_, by simp, fun x => ?_⟩
    · intro q hq; simp at hq; subst hq; exact comp_mono s2 hc
    · simp only [cnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := half (U x) (y.2 x); omega
  | y :: z :: rest, gs, u, U, hok, hu, hr => by
    have hy := hr y (by simp)
    have hz := hr z (by simp)
    have hrest : ∀ q ∈ rest, Comp k gs q.1 q.2 := fun q hq => hr q (by simp [hq])
    obtain ⟨g1, a1, s1, c1⟩ := mk_xor hok hu hy
    obtain ⟨g2, a2, s2, c2⟩ := mk_xor s1.1 (comp_mono s1 hu) (comp_mono s1 hz)
    obtain ⟨g3, a3, s3, c3⟩ := mk_and s2.1 (comp_mono s2 c1) c2
    obtain ⟨g4, a4, s4, c4⟩ := mk_xor s3.1 (comp_mono (step_trans s2 s3) (comp_mono s1 hu)) c3
    obtain ⟨g5, a5, s5, c5⟩ := mk_xor s4.1 (comp_mono s4 (comp_mono s3 (comp_mono s2 c1)))
      (comp_mono s4 (comp_mono s3 (comp_mono s2 (comp_mono s1 hz))))
    have s15 := step_trans (step_trans (step_trans (step_trans s1 s2) s3) s4) s5
    obtain ⟨g6, u', U', cs, s6, hu', hcs, hlen, hid⟩ :=
      chain k rest g5 a5 _ s5.1 c5 (comps_mono s15 hrest)
    refine ⟨g6, u', U', (a4, fun x => xor (U x) ((xor (U x) (y.2 x)) && (xor (U x) (z.2 x))))
      :: cs, step_mono (step_trans s15 s6) ?_ ?_, hu', ?_, ?_, fun x => ?_⟩
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact comp_mono s6 (comp_mono s5 c4)
      · exact hcs q hq
    · simp only [List.length_cons]; omega
    · have h1 := hid x
      have h2 := maj (U x) (y.2 x) (z.2 x)
      simp only [cnt, List.map_cons, List.sum_cons] at h1 ⊢
      omega

theorem thr (k : ℕ) : ∀ r : ℕ, ∀ (P : List (Sig k)) (gs : List Gate), P.length = r → Ok k gs →
    (∀ q ∈ P, Comp k gs q.1 q.2) → ∀ T : ℕ,
    ∃ gs' w, Step k gs gs' (r - 1) (13 * (r - 1) + 2) ∧
      Comp k gs' w (fun x => decide (T ≤ cnt P x)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro P gs hlen hok hP T
  by_cases hT0 : T = 0
  · obtain ⟨g1, w, s1, c1⟩ := mk_true hok
    exact ⟨g1, w, step_mono s1 (by omega) (by omega), comp_ext c1 (fun x => by simp [hT0])⟩
  by_cases hTr : r < T
  · obtain ⟨g1, w, s1, c1⟩ := mk_false hok
    refine ⟨g1, w, step_mono s1 (by omega) (by omega), comp_ext c1 (fun x => ?_)⟩
    have := cnt_le P x
    simp; omega
  match P, hlen with
  | [], hlen => simp at hlen; omega
  | [q], hlen =>
    simp at hlen
    have hT1 : T = 1 := by omega
    subst hT1
    refine ⟨gs, q.1, step_mono (step_refl hok) (by omega) (by omega),
      comp_ext (hP q (by simp)) (fun x => ?_)⟩
    simp only [cnt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    cases q.2 x <;> simp
  | q :: q2 :: P', hlen =>
    simp only [List.length_cons] at hlen
    have hq := hP q (by simp)
    have hP' : ∀ q' ∈ q2 :: P', Comp k gs q'.1 q'.2 := fun q' h => hP q' (by simp [h])
    rcases Nat.even_or_odd T with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- even threshold: start the parity at the first bit
      obtain ⟨g1, u', U', cs, s1, hu', hcs, hcl, hid⟩ := chain k (q2 :: P') gs q.1 q.2 hok hq hP'
      simp only [List.length_cons] at hcl s1
      obtain ⟨g2, w, s2, c2⟩ := ih cs.length (by omega) cs g1 rfl s1.1 hcs t
      refine ⟨g2, w, step_mono (step_trans s1 s2) (by omega) (by omega), comp_ext c2 ?_⟩
      intro x
      have h1 := hid x
      have h2 := Bool.toNat_le (U' x)
      rw [cnt_cons]
      apply decide_eq_decide.mpr
      omega
    · rcases Nat.even_or_odd r with ⟨r2, hr2⟩ | ⟨r2, hr2⟩
      · -- odd threshold, even count: a constant one starts the parity
        obtain ⟨g0, u0, s0, c0⟩ := mk_true hok
        obtain ⟨g1, u', U', cs, s1, hu', hcs, hcl, hid⟩ :=
          chain k (q :: q2 :: P') g0 u0 _ s0.1 c0 (comps_mono s0 hP)
        simp only [List.length_cons] at hcl s1
        obtain ⟨g2, w, s2, c2⟩ := ih cs.length (by omega) cs g1 rfl s1.1 hcs (t + 1)
        refine ⟨g2, w, step_mono (step_trans (step_trans s0 s1) s2) (by omega) (by omega),
          comp_ext c2 ?_⟩
        intro x
        have h1 := hid x
        have h2 := Bool.toNat_le (U' x)
        simp only [Bool.toNat_true] at h1
        apply decide_eq_decide.mpr
        omega
      · -- odd threshold, odd count: the first bit is a free carry
        obtain ⟨g0, u0, s0, c0⟩ := mk_not hok hq
        obtain ⟨g1, u', U', cs, s1, hu', hcs, hcl, hid⟩ :=
          chain k (q2 :: P') g0 u0 _ s0.1 c0 (comps_mono s0 hP')
        simp only [List.length_cons] at hcl s1
        have hall : ∀ q' ∈ q :: cs, Comp k g1 q'.1 q'.2 := by
          intro q' h
          simp only [List.mem_cons] at h
          rcases h with rfl | h
          · exact comp_mono s1 (comp_mono s0 hq)
          · exact hcs q' h
        obtain ⟨g2, w, s2, c2⟩ := ih (q :: cs).length (by simp; omega) (q :: cs) g1 rfl s1.1
          hall (t + 1)
        refine ⟨g2, w, step_mono (step_trans (step_trans s0 s1) s2) ?_ ?_, comp_ext c2 ?_⟩
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
        intro x
        have h1 := hid x
        have h2 := Bool.toNat_le (U' x)
        have h3 : (!(q.2 x)).toNat + (q.2 x).toNat = 1 := by cases q.2 x <;> rfl
        rw [cnt_cons q (q2 :: P'), cnt_cons q cs]
        apply decide_eq_decide.mpr
        omega

theorem bx (p q : F2) : xor (decide (p = 1)) (decide (q = 1)) = decide (p + q = 1) := by
  revert p q; decide

theorem two_vals (t : F2) : t = 0 ∨ t = 1 := by
  revert t; decide

theorem par (k : ℕ) (a : Fin k → F2) (c : F2) : ∀ (l : List (Fin k)) (gs : List Gate), Ok k gs →
    ∃ gs' w, Step k gs gs' 0 (2 + 2 * l.length) ∧
      Comp k gs' w (fun x => decide (c + (l.map (fun i => a i * x i)).sum = 1)) := by
  intro l
  induction l with
  | nil =>
    intro gs hok
    rcases two_vals c with hc | hc
    · obtain ⟨g1, w, s1, c1⟩ := mk_false hok
      exact ⟨g1, w, step_mono s1 le_rfl (by simp), comp_ext c1 (fun x => by simp [hc])⟩
    · obtain ⟨g1, w, s1, c1⟩ := mk_true hok
      exact ⟨g1, w, step_mono s1 le_rfl (by simp), comp_ext c1 (fun x => by simp [hc])⟩
  | cons i l ih =>
    intro gs hok
    obtain ⟨g1, w1, s1, c1⟩ := ih gs hok
    rcases two_vals (a i) with hai | hai
    · refine ⟨g1, w1, step_mono s1 le_rfl (by simp only [List.length_cons]; omega),
        comp_ext c1 (fun x => ?_)⟩
      simp [hai]
    · obtain ⟨g2, w2, s2, c2⟩ := mk_xor s1.1 c1 (comp_inp g1 i)
      refine ⟨g2, w2, step_mono (step_trans s1 s2) le_rfl (by simp only [List.length_cons]; omega),
        comp_ext c2 (fun x => ?_)⟩
      have e3 : ∀ p q r : F2, p + (q + r) = p + r + q := by intros; ring
      rw [bx]
      simp only [List.map_cons, List.sum_cons, hai, one_mul]
      rw [e3]

theorem pars (k m : ℕ) (v : Fin m → Fin k → F2) (e : Fin m → F2) : ∀ (l : List (Fin m)),
    ∃ gs, ∃ P : List (Sig k), Step k [] gs 0 (l.length * (2 + 2 * k)) ∧ P.length = l.length ∧
      (∀ q ∈ P, Comp k gs q.1 q.2) ∧
      ∀ x, cnt P x = (l.map (fun j => (decide (dotProduct (v j) x + e j = 1)).toNat)).sum := by
  intro l
  induction l with
  | nil => exact ⟨[], [], step_mono (step_refl (ok_nil k)) le_rfl (by simp), rfl, by simp,
    fun x => rfl⟩
  | cons j l ih =>
    obtain ⟨gs, P, s1, hl, hP, hc⟩ := ih
    obtain ⟨g2, w, s2, c2⟩ := par k (v j) (e j) (List.finRange k) gs s1.1
    refine ⟨g2, (w, fun x => decide (dotProduct (v j) x + e j = 1)) :: P,
      step_mono (step_trans s1 s2) le_rfl ?_, by simp [hl], ?_, fun x => ?_⟩
    · simp only [List.length_cons, List.length_finRange, Nat.succ_mul]; omega
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · refine comp_ext c2 (fun x => ?_)
        simp only [dotProduct, Fin.sum_univ_def]
        rw [add_comm (e j)]
      · exact comp_mono s2 (hP q hq)
    · rw [cnt_cons, hc x]
      simp

end PEqualNP.Outside.L_meta_29725

open PEqualNP.Outside.L_meta_29725 in
theorem PEqualNP.Outside.L_meta_29725 : ∀ (k m T : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  ∀ (v : Fin m → V) (e : Fin m → F),
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack k C ∧
      C.output < k+C.size ∧ C.size ≤ (2*k+20)*(m+1) ∧
      (∀ g ∈ C.gates,
        (g.op = .and ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)) ∧
      C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _)) ≤ m-1 ∧
      ∀ x : V, C.eval (List.ofFn (fun i : Fin k => decide (x i = 1))) =
        decide (T ≤ ((Finset.univ : Finset (Fin m)).filter
          (fun j => dotProduct (v j) x + e j = 1)).card) := by
  intro k m T
  dsimp only
  intro v e
  obtain ⟨gs, P, s1, hl, hP, hc⟩ := pars k m v e (List.finRange m)
  rw [List.length_finRange] at hl s1
  obtain ⟨gs', w, s2, c2⟩ := thr k m P gs hl s1.1 hP T
  have s12 := step_trans s1 s2
  obtain ⟨hok, hs0, hgs, hlen, hn⟩ := s12
  simp only [List.nil_append] at hgs
  subst hgs
  refine ⟨⟨gs', w⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs', w⟩ j = gs'[j] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg] at hi
    exact (hok j hj).2 i hi
  · exact c2.1
  · show gs'.length ≤ _
    nlinarith [Nat.sub_le m 1]
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    exact (hok j hj).1
  · show nand gs' ≤ m - 1
    omega
  · intro x
    show val gs' w x = _
    rw [c2.2 x]
    dsimp only
    have key : ∀ j, (decide (dotProduct (v j) x + e j = 1)).toNat =
        if dotProduct (v j) x + e j = 1 then 1 else 0 := by
      intro j; by_cases h : dotProduct (v j) x + e j = 1 <;> simp [h]
    rw [hc x, Finset.card_filter, Fin.sum_univ_def]
    simp only [key]
