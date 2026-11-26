import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19451_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stp]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega, by rw [h6, hl]; congr 1; omega⟩

def val (n u v k : ℕ) : Bool :=
  if k = 0 then decide (u = 0 ∨ v = 0)
  else if k % 3 = 0 then decide (1 ≤ v ∧ v ≤ (k + 3) / 3)
  else if k % 3 = 1 then decide (u + (k + 3) / 3 + 1 = n ∧ 1 ≤ v ∧ v ≤ (k + 3) / 3)
  else decide (u = 0 ∨ v = 0 ∨ (n ≤ u + (k + 3) / 3 + 1 ∧ 1 ≤ v ∧ u + v + 1 ≤ n))

def fw (n u v : ℕ) (e1 e2 : Bool) (w : ℕ) : Bool :=
  if w < n then (if w = n - 1 then e1 else decide (u = w))
  else if w < 2 * n then (if w = 2 * n - 1 then e2 else decide (v + n = w)) else val n u v (w - 2 * n)

def gate (n k : ℕ) : Gate :=
  if k = 0 then ⟨GateOp.or, [0, n]⟩
  else if k = 2 then ⟨GateOp.or, [2 * n + 0, 2 * n + 1]⟩
  else if k % 3 = 0 then ⟨GateOp.or, [if k = 3 then n + 1 else 2 * n + (k - 3), n + (k + 3) / 3]⟩
  else if k % 3 = 1 then ⟨GateOp.and, [n - 1 - (k + 3) / 3, if k = 1 then n + 1 else 2 * n + (k - 1)]⟩
  else ⟨GateOp.or, [2 * n + (k - 3), 2 * n + (k - 1)]⟩

theorem v0 (n u v : ℕ) : val n u v 0 = decide (u = 0 ∨ v = 0) := by simp [val]

theorem vQ (n u v k : ℕ) (h1 : k ≠ 0) (h2 : k % 3 = 0) :
    val n u v k = decide (1 ≤ v ∧ v ≤ (k + 3) / 3) := by simp [val, h1, h2]

theorem vA (n u v k : ℕ) (h : k % 3 = 1) :
    val n u v k = decide (u + (k + 3) / 3 + 1 = n ∧ 1 ≤ v ∧ v ≤ (k + 3) / 3) := by
  simp [val, h, show k ≠ 0 by omega]

theorem vZ (n u v k : ℕ) (h : k % 3 = 2) :
    val n u v k = decide (u = 0 ∨ v = 0 ∨ (n ≤ u + (k + 3) / 3 + 1 ∧ 1 ≤ v ∧ u + v + 1 ≤ n)) := by
  simp [val, h, show k ≠ 0 by omega]

theorem fX (n u v : ℕ) (e1 e2 : Bool) (w : ℕ) (h : w < n) (h' : w ≠ n - 1) :
    fw n u v e1 e2 w = decide (u = w) := by simp [fw, h, h']

theorem fY (n u v : ℕ) (e1 e2 : Bool) (w : ℕ) (h1 : n ≤ w) (h2 : w < 2 * n) (h3 : w ≠ 2 * n - 1) :
    fw n u v e1 e2 w = decide (v + n = w) := by
  simp [fw, h2, h3, show ¬ w < n by omega]

theorem fG (n u v : ℕ) (e1 e2 : Bool) (k : ℕ) : fw n u v e1 e2 (2 * n + k) = val n u v k := by
  simp [fw, show ¬ 2 * n + k < n by omega, show ¬ 2 * n + k < 2 * n by omega]

theorem gate_ok (n u v : ℕ) (e1 e2 : Bool) (k : ℕ) (hn : 3 ≤ n) (hk : k < 3 * n - 6) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (fw n u v e1 e2)) = fw n u v e1 e2 (2 * n + k) := by
  unfold gate
  split_ifs with h0 h2 h3 h4 h5 h6 <;> refine ⟨by simp; omega, ?_⟩ <;>
    simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
      Bool.or_false, Bool.and_true, fG]
  · subst h0; rw [fX n u v e1 e2 0 (by omega) (by omega), fY n u v e1 e2 n le_rfl (by omega) (by omega), v0]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · subst h2; rw [v0, vA n u v 1 (by norm_num), vZ n u v 2 (by norm_num)]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [fY n u v e1 e2 (n + 1) (by omega) (by omega) (by omega), fY n u v e1 e2 _ (by omega) (by omega) (by omega), vQ n u v k h0 h3]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [vQ n u v (k - 3) (by omega) (by omega), fY n u v e1 e2 _ (by omega) (by omega) (by omega), vQ n u v k h0 h3]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [fX n u v e1 e2 _ (by omega) (by omega), fY n u v e1 e2 (n + 1) (by omega) (by omega) (by omega), vA n u v k h5]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [fX n u v e1 e2 _ (by omega) (by omega), vQ n u v (k - 1) (by omega) (by omega), vA n u v k h5]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [vZ n u v (k - 3) (by omega), vA n u v (k - 1) (by omega), vZ n u v k (by omega)]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem stair (n : ℕ) (hn : 3 ≤ n) : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 3 * n - 6 ∧
    ∀ (u v : Fin n) (x : List Bool), x.length = 2 * n →
      (∀ i < 2 * n, i ≠ n - 1 → i ≠ 2 * n - 1 → x.getD i false = (oneEach u v).getD i false) →
      C.eval x = decide ((u : ℕ) + (v : ℕ) ≤ n - 1) := by
  refine ⟨⟨(List.range (3 * n - 6)).map (gate n), 2 * n + (3 * n - 7)⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs <;> simp
  · intro u v x hl hxo
    have hx : ∀ i < x.length, x.getD i false =
        fw n u v (x.getD (n - 1) false) (x.getD (2 * n - 1) false) i := by
      intro i hi
      rw [hl] at hi
      by_cases h1 : i = n - 1
      · subst h1; simp [fw, show n - 1 < n by omega]
      by_cases h2 : i = 2 * n - 1
      · subst h2; simp [fw, show ¬ 2 * n - 1 < n by omega, show 2 * n - 1 < 2 * n by omega]
      rw [hxo i hi h1 h2]
      apply Bool.eq_iff_iff.2
      simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, List.getElem?_ofFn, fw, val]
      split_ifs <;> simp [Fin.ext_iff] <;> omega
    show (List.foldl stp x ((List.range (3 * n - 6)).map (gate n))).getD
      (2 * n + (3 * n - 7)) false = decide ((u : ℕ) + (v : ℕ) ≤ n - 1)
    rw [spec _ _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n u v _ _ k hn hk) _ (by simp [hl]; omega), fG, vZ n u v _ (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega

def rl (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem copy (f : ℕ → ℕ) (n0 B : ℕ) (h2 : ∀ k, n0 ≤ k → f k = B + (k - n0)) :
    ∀ (gs : List Gate) (S W : List Bool), n0 ≤ S.length → W.length + n0 = S.length + B →
    (∀ k < n0, f k < B ∨ W.length + gs.length ≤ f k) →
    (∀ k, W.getD (f k) false = S.getD k false) →
    ∀ k, ((gs.map (rl f)).foldl stp W).getD (f k) false = (gs.foldl stp S).getD k false
  | [], S, W, _, _, _, hI => by simpa using hI
  | g :: gs, S, W, hS, hL, h1, hI => by
    have hv : g.op.eval ((g.inputs.map f).map fun i => W.getD i false) =
        g.op.eval (g.inputs.map fun i => S.getD i false) := by
      rw [List.map_map]; congr 1; exact List.map_congr_left (fun i _ => hI i)
    have e1 : stp W (rl f g) = W ++ [g.op.eval (g.inputs.map fun i => S.getD i false)] := by
      show W ++ [g.op.eval ((g.inputs.map f).map fun i => W.getD i false)] = _
      rw [hv]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e1]
    apply copy f n0 B h2 gs
    · simp [stp]; omega
    · simp [stp]; omega
    · intro k hk
      rcases h1 k hk with h | h
      · exact Or.inl h
      · right; simp at h ⊢; omega
    · intro k
      rw [stp, getD_snoc, getD_snoc]
      rcases lt_trichotomy k S.length with hk | hk | hk
      · have hne : f k ≠ W.length := by
          by_cases hk0 : k < n0
          · rcases h1 k hk0 with h | h <;> (try simp only [List.length_cons] at h) <;> omega
          · rw [h2 k (by omega)]; omega
        rw [if_pos hk, ← hI k]
        by_cases ha : f k < W.length
        · rw [if_pos ha]
        · rw [if_neg ha, if_neg hne, getD_ge _ _ (by omega)]
      · subst hk
        have : f S.length = W.length := by rw [h2 _ hS]; omega
        rw [this]; simp
      · rw [h2 k (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]

def build (cls : ℕ → ℕ) : List ℕ → (ℕ → Option ℕ) → ℕ → List Gate × (ℕ → Option ℕ)
  | [], cur, _ => ([], cur)
  | w :: L, cur, nx =>
    match cur (cls w) with
    | none => build cls L (Function.update cur (cls w) (some w)) nx
    | some a => (⟨GateOp.or, [a, w]⟩ :: (build cls L (Function.update cur (cls w) (some nx)) (nx + 1)).1,
        (build cls L (Function.update cur (cls w) (some nx)) (nx + 1)).2)

theorem build_good (cls : ℕ → ℕ) : ∀ (L : List ℕ) (cur : ℕ → Option ℕ) (nx : ℕ),
    ∀ g ∈ (build cls L cur nx).1, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro L
  induction L with
  | nil => intro cur nx g hg; simp [build] at hg
  | cons w L ih =>
    intro cur nx g hg
    cases hc : cur (cls w) with
    | none => simp only [build, hc] at hg; exact ih _ _ g hg
    | some a =>
      simp only [build, hc, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp
      · exact ih _ _ g hg

theorem build_len (cls : ℕ → ℕ) (K : ℕ) : ∀ (L : List ℕ) (cur : ℕ → Option ℕ) (nx : ℕ),
    (∀ w ∈ L, cls w < K) →
    (build cls L cur nx).1.length + ((Finset.range K).filter fun c => (build cls L cur nx).2 c ≠ none).card =
      L.length + ((Finset.range K).filter fun c => cur c ≠ none).card := by
  intro L
  induction L with
  | nil => intro cur nx _; rfl
  | cons w L ih =>
    intro cur nx hL
    have hw := hL w (by simp)
    have hL' : ∀ w' ∈ L, cls w' < K := fun w' h => hL w' (by simp [h])
    cases hc : cur (cls w) with
    | none =>
      simp only [build, hc]
      rw [ih _ _ hL']
      have e : (Finset.range K).filter (fun c => Function.update cur (cls w) (some w) c ≠ none) =
          insert (cls w) ((Finset.range K).filter fun c => cur c ≠ none) := by
        ext c
        by_cases h : c = cls w
        · subst h; simp [hw]
        · simp [Function.update_apply, h]
      rw [e, Finset.card_insert_of_notMem (by simp [hc])]
      simp only [List.length_cons]
      omega
    | some a =>
      simp only [build, hc, List.length_cons]
      have := ih (Function.update cur (cls w) (some nx)) (nx + 1) hL'
      have e : (Finset.range K).filter (fun c => Function.update cur (cls w) (some nx) c ≠ none) =
          (Finset.range K).filter fun c => cur c ≠ none := by
        ext c
        by_cases h : c = cls w
        · subst h; simp [hc]
        · simp [Function.update_apply, h]
      rw [e] at this
      omega

theorem build_val (cls : ℕ → ℕ) (N : ℕ) (x0 : List Bool) : ∀ (L D : List ℕ) (cur : ℕ → Option ℕ)
    (x : List Bool) (G : List Gate) (cur' : ℕ → Option ℕ),
    build cls L cur x.length = (G, cur') → N ≤ x.length →
    (∀ i < N, x.getD i false = x0.getD i false) → (∀ w ∈ L, w < N) →
    (∀ c a, cur c = some a → a < x.length ∧
      (x.getD a false = true ↔ ∃ w ∈ D, cls w = c ∧ x0.getD w false = true)) →
    (∀ c, cur c = none → ∀ w ∈ D, cls w ≠ c) →
    (∀ c a, cur' c = some a → a < (G.foldl stp x).length ∧
      ((G.foldl stp x).getD a false = true ↔ ∃ w ∈ D ++ L, cls w = c ∧ x0.getD w false = true)) ∧
    (∀ c, cur' c = none → ∀ w ∈ D ++ L, cls w ≠ c) := by
  intro L
  induction L with
  | nil =>
    intro D cur x G cur' hb _ _ _ h1 h2
    simp only [build, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simpa using ⟨h1, h2⟩
  | cons w L ih =>
    intro D cur x G cur' hb hN hx hL h1 h2
    have hw : w < N := hL w (by simp)
    have hL' : ∀ w' ∈ L, w' < N := fun w' h => hL w' (by simp [h])
    have e : D ++ w :: L = (D ++ [w]) ++ L := by simp
    rw [e]
    cases hc : cur (cls w) with
    | none =>
      simp only [build, hc] at hb
      apply ih (D ++ [w]) _ x G cur' hb hN hx hL'
      · intro c a h
        rw [Function.update_apply] at h
        split_ifs at h with hcw
        · obtain rfl := Option.some.inj h
          subst hcw
          refine ⟨by omega, ?_⟩
          rw [hx w hw]
          constructor
          · intro h'; exact ⟨w, by simp, rfl, h'⟩
          · rintro ⟨w', hw', hc', h'⟩
            simp only [List.mem_append, List.mem_singleton] at hw'
            rcases hw' with hw' | rfl
            · exact absurd hc' (h2 _ hc w' hw')
            · exact h'
        · obtain ⟨ha, hiff⟩ := h1 c a h
          refine ⟨ha, hiff.trans ?_⟩
          constructor
          · rintro ⟨w', hw', hc', h'⟩; exact ⟨w', by simp [hw'], hc', h'⟩
          · rintro ⟨w', hw', hc', h'⟩
            simp only [List.mem_append, List.mem_singleton] at hw'
            rcases hw' with hw' | rfl
            · exact ⟨w', hw', hc', h'⟩
            · exact absurd hc'.symm hcw
      · intro c h w' hw'
        rw [Function.update_apply] at h
        split_ifs at h with hcw
        simp only [List.mem_append, List.mem_singleton] at hw'
        rcases hw' with hw' | rfl
        · exact h2 c h w' hw'
        · exact fun e => hcw e.symm
    | some a =>
      simp only [build, hc, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨ha, hai⟩ := h1 _ a hc
      have hl : (stp x ⟨GateOp.or, [a, w]⟩).length = x.length + 1 := by simp [stp]
      have hv : (stp x ⟨GateOp.or, [a, w]⟩).getD x.length false = (x.getD a false || x.getD w false) := by
        rw [stp, getD_snoc, if_neg (lt_irrefl _), if_pos rfl]; simp [GateOp.eval]
      have hp : ∀ i < x.length, (stp x ⟨GateOp.or, [a, w]⟩).getD i false = x.getD i false :=
        fun i hi => by rw [stp, getD_snoc, if_pos hi]
      have hb0 : build cls L (Function.update cur (cls w) (some x.length))
          (stp x ⟨GateOp.or, [a, w]⟩).length =
          ((build cls L (Function.update cur (cls w) (some x.length)) (x.length + 1)).1,
           (build cls L (Function.update cur (cls w) (some x.length)) (x.length + 1)).2) := by
        rw [hl]
      rw [List.foldl_cons]
      refine ih (D ++ [w]) _ _ _ _ hb0 (by omega) (fun i hi => by rw [hp i (by omega)]; exact hx i hi)
        hL' ?_ ?_
      · intro c a' h
        rw [Function.update_apply] at h
        split_ifs at h with hcw
        · obtain rfl := Option.some.inj h
          subst hcw
          refine ⟨by omega, ?_⟩
          rw [hv, Bool.or_eq_true, hai, hx w hw]
          constructor
          · rintro (⟨w', hw', hc', h'⟩ | h')
            · exact ⟨w', by simp [hw'], hc', h'⟩
            · exact ⟨w, by simp, rfl, h'⟩
          · rintro ⟨w', hw', hc', h'⟩
            simp only [List.mem_append, List.mem_singleton] at hw'
            rcases hw' with hw' | rfl
            · exact Or.inl ⟨w', hw', hc', h'⟩
            · exact Or.inr h'
        · obtain ⟨ha', hiff⟩ := h1 c a' h
          refine ⟨by omega, ?_⟩
          rw [hp a' ha']
          refine hiff.trans ?_
          constructor
          · rintro ⟨w', hw', hc', h'⟩; exact ⟨w', by simp [hw'], hc', h'⟩
          · rintro ⟨w', hw', hc', h'⟩
            simp only [List.mem_append, List.mem_singleton] at hw'
            rcases hw' with hw' | rfl
            · exact ⟨w', hw', hc', h'⟩
            · exact absurd hc'.symm hcw
      · intro c h w' hw'
        rw [Function.update_apply] at h
        split_ifs at h with hcw
        simp only [List.mem_append, List.mem_singleton] at hw'
        rcases hw' with hw' | rfl
        · exact h2 c h w' hw'
        · exact fun e => hcw e.symm


theorem build_len0 (cls : ℕ → ℕ) (K : ℕ) (L : List ℕ) (nx : ℕ) (h : ∀ w ∈ L, cls w < K) :
    (build cls L (fun _ => none) nx).1.length +
      ((Finset.range K).filter fun c => (build cls L (fun _ => none) nx).2 c ≠ none).card = L.length := by
  have := build_len cls K L (fun _ => none) nx h
  simpa using this

end PEqualNP.Outside.L_meta_19451_aux

open PEqualNP.Outside.L_meta_19451_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19451 : ∀ n k a b : ℕ, 3 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) (2 * n + k - 4 - a - b) := by
  intro n k a b hk t ht ⟨u1, hu1⟩ hS haa hbb
  set S := Finset.univ.image t with hSdef
  obtain ⟨C, hM, hs, hC⟩ := stair k hk
  have hmem : ∀ d ∈ S, 1 ≤ d ∧ d ≤ n := by
    intro d hd
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hd
    exact ht u
  have hnS : n ∈ S := Finset.mem_image.2 ⟨u1, Finset.mem_univ _, hu1⟩
  let r : ℕ → ℕ := fun d => (S.filter (· < d)).card
  let q : ℕ → ℕ := fun v => (S.filter (· ≤ v)).card
  have r_lt : ∀ d ∈ S, r d < k := by
    intro d hd
    rw [← hS]
    exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨d, hd, by simp⟩)
  have q_lt : ∀ v < n, q v < k := by
    intro v hv
    rw [← hS]
    exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨n, hnS, by simp; omega⟩)
  have rmono : ∀ d ∈ S, ∀ d', d < d' → r d < r d' := by
    intro d hd d' hl
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset (fun x hx => by
      simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩)).2
      ⟨d, by simp [hd, hl], by simp⟩)
  have hrn : k - 1 ≤ r n := by
    have : (S.erase n).card ≤ r n := Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_erase, Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, lt_of_le_of_ne (hmem x hx.2).2 hx.1⟩)
    rw [Finset.card_erase_of_mem hnS, hS] at this
    exact this
  have key : ∀ d ∈ S, ∀ v, v < d ↔ q v ≤ r d := by
    intro d hd v
    constructor
    · intro h
      exact Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩)
    · intro h
      by_contra h'
      have : r d < q v := Finset.card_lt_card ((Finset.ssubset_iff_of_subset (fun x hx => by
        simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩)).2
        ⟨d, by simp [hd]; omega, by simp⟩)
      omega
  have hR : S.image r = Finset.range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (r_lt d hd)
    · rw [Finset.card_image_of_injOn, hS, Finset.card_range]
      intro d hd d' hd' h
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := rmono d hd d' hl; omega
      · have := rmono d' hd' d hl; omega
  have rsurj : ∀ c < k, ∃ d ∈ S, r d = c := by
    intro c hc
    have : c ∈ S.image r := by rw [hR]; exact Finset.mem_range.2 hc
    exact Finset.mem_image.1 this
  have qsurj : ∀ i < k, ∃ v < n, q v = i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine ⟨0, by have := u1.isLt; omega, ?_⟩
      exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x hx => by
        have := (hmem x hx).1; simp; omega)
    · obtain ⟨d, hd, hrd⟩ := rsurj (i - 1) (by omega)
      have hdn : d < n := by
        rcases Nat.lt_or_ge d n with h | h
        · exact h
        · have hdn : d = n := le_antisymm (hmem d hd).2 h
          subst hdn
          have : (S.erase d).card ≤ r d := Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_erase, Finset.mem_filter] at hx ⊢
            exact ⟨hx.2, lt_of_le_of_ne (hmem x hx.2).2 hx.1⟩)
          rw [Finset.card_erase_of_mem hd, hS] at this
          omega
      refine ⟨d, hdn, ?_⟩
      have e : S.filter (· ≤ d) = insert d (S.filter (· < d)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_eq_of_le h2 with h | h
          · exact Or.inr ⟨h1, h⟩
          · exact Or.inl h
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hd, le_rfl⟩
          · exact ⟨h1, h2.le⟩
      show (S.filter (· ≤ d)).card = i
      rw [e, Finset.card_insert_of_notMem (by simp)]
      show r d + 1 = i
      omega
  let tt : ℕ → ℕ := fun w => if h : w < n then t ⟨w, h⟩ else 0
  let cls : ℕ → ℕ := fun w => if w < n then k - 1 - r (tt w) else k + q (w - n)
  have cU : ∀ u : Fin n, cls u.val = k - 1 - r (t u) := by
    intro u
    show (if u.val < n then k - 1 - r (if h : u.val < n then t ⟨u.val, h⟩ else 0) else _) = _
    rw [if_pos u.isLt, dif_pos u.isLt]
  have cV : ∀ v : Fin n, cls (n + v.val) = k + q v.val := by
    intro v
    show (if n + v.val < n then _ else k + q (n + v.val - n)) = _
    rw [if_neg (by omega)]
    congr 2
    omega
  have tS : ∀ u : Fin n, t u ∈ S := fun u => Finset.mem_image.2 ⟨u, Finset.mem_univ _, rfl⟩
  have rowmin : ∀ u : Fin n, (∀ u', t u ≤ t u') → cls u.val = k - 1 := by
    intro u hu
    rw [cU]
    have : r (t u) = 0 := Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x hx => by
      obtain ⟨u', -, rfl⟩ := Finset.mem_image.1 hx
      exact Nat.not_lt.2 (hu u'))
    omega
  have colmin : ∀ v : Fin n, (∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
      (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card) → cls (n + v.val) = 2 * k - 1 := by
    intro v hv
    rw [cV]
    have hq := q_lt v.val v.isLt
    by_contra hne
    obtain ⟨d, hd, hrd⟩ := rsurj (q v.val) hq
    have hvd : v.val < d := (key d hd v.val).2 (by omega)
    have hdn : d < n := by
      rcases Nat.lt_or_ge d n with h | h
      · exact h
      · have e : d = n := le_antisymm (hmem d hd).2 h
        rw [e] at hrd
        omega
    obtain ⟨u0, -, rfl⟩ := Finset.mem_image.1 hd
    have h1 := hv ⟨n - 1, by omega⟩
    have h2 : (Finset.univ.filter (fun u => ((⟨n - 1, by omega⟩ : Fin n) : ℕ) < t u)) ⊂
        Finset.univ.filter (fun u => (v : ℕ) < t u) :=
      (Finset.ssubset_iff_of_subset (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; have := v.isLt; omega)).2
        ⟨u0, by simp; omega, by simp; omega⟩
    have := Finset.card_lt_card h2
    omega
  let L : List ℕ := (Finset.univ.filter (fun u : Fin n => ¬ ∀ u', t u ≤ t u')).toList.map (fun u => u.val) ++
    (Finset.univ.filter (fun v : Fin n => ¬ ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
      (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).toList.map (fun v => n + v.val)
  have memL : ∀ w ∈ L, w < 2 * n := by
    intro w hw
    simp only [L, List.mem_append, List.mem_map, Finset.mem_toList] at hw
    rcases hw with ⟨u, -, rfl⟩ | ⟨v, -, rfl⟩
    · have := u.isLt; omega
    · have := v.isLt; omega
  have memL' : ∀ w < 2 * n, cls w ≠ k - 1 → cls w ≠ 2 * k - 1 → w ∈ L := by
    intro w hw h1 h2
    simp only [L, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases Nat.lt_or_ge w n with h | h
    · left; exact ⟨⟨w, h⟩, fun hm => h1 (rowmin ⟨w, h⟩ hm), rfl⟩
    · right
      refine ⟨⟨w - n, by omega⟩, fun hm => h2 ?_, show n + (w - n) = w by omega⟩
      have := colmin ⟨w - n, by omega⟩ hm
      simp only at this
      rwa [show n + (w - n) = w by omega] at this
  have hLlen : L.length + a + b = 2 * n := by
    have e1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun u : Fin n => ∀ u', t u ≤ t u')
    have e2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
        (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)
    simp only [Finset.card_univ, Fintype.card_fin] at e1 e2
    simp only [L, List.length_append, List.length_map, Finset.length_toList]
    omega
  have hcls : ∀ w ∈ L, cls w < 2 * k := by
    intro w hw
    have hw := memL w hw
    rcases Nat.lt_or_ge w n with h | h
    · have := cU ⟨w, h⟩
      simp only at this
      rw [this]; omega
    · have := cV ⟨w - n, by omega⟩
      simp only at this
      rw [show n + (w - n) = w by omega] at this
      rw [this]
      have := q_lt (w - n) (by omega)
      omega
  have seen : ∀ c < 2 * k, ∃ w ∈ List.range (2 * n), cls w = c := by
    intro c hc
    rcases Nat.lt_or_ge c k with h | h
    · obtain ⟨d, hd, hrd⟩ := rsurj (k - 1 - c) (by omega)
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hd
      refine ⟨u.val, List.mem_range.2 (by have := u.isLt; omega), ?_⟩
      rw [cU, hrd]; omega
    · obtain ⟨v, hv, hqv⟩ := qsurj (c - k) (by omega)
      refine ⟨n + v, List.mem_range.2 (by omega), ?_⟩
      rw [cV ⟨v, hv⟩]
      simp only
      omega
  have seenL : ∀ c < 2 * k, c ≠ k - 1 → c ≠ 2 * k - 1 → ∃ w ∈ L, cls w = c := by
    intro c hc h1 h2
    obtain ⟨w, hw, hcw⟩ := seen c hc
    exact ⟨w, memL' w (List.mem_range.1 hw) (by omega) (by omega), hcw⟩
  set bd := build cls L (fun _ => none) (2 * n) with hbd
  have hlen0 : ∀ (u : Fin n) (v : Fin n), (oneEach u v).length = 2 * n := by
    intro u v; simp [oneEach]; omega
  have hval : ∀ (u : Fin n) (v : Fin n),
      (∀ c a, bd.2 c = some a → a < (bd.1.foldl stp (oneEach u v)).length ∧
        ((bd.1.foldl stp (oneEach u v)).getD a false = true ↔
          ∃ w ∈ [] ++ L, cls w = c ∧ (oneEach u v).getD w false = true)) ∧
      (∀ c, bd.2 c = none → ∀ w ∈ [] ++ L, cls w ≠ c) := by
    intro u v
    exact build_val cls (2 * n) (oneEach u v) L [] (fun _ => none) (oneEach u v)
      bd.1 bd.2 (by rw [hlen0]) (by rw [hlen0]) (fun _ _ => rfl)
      memL (fun c a h => by simp at h) (fun c _ w hw => by simp at hw)
  have hsee : ∀ c < 2 * k, c ≠ k - 1 → c ≠ 2 * k - 1 → bd.2 c ≠ none := by
    intro c hc h1 h2 hn
    obtain ⟨w, hw, hcw⟩ := seenL c hc h1 h2
    exact (hval u1 u1).2 c hn w (by simpa using hw) hcw
  have hGlen : bd.1.length + (2 * k - 2) ≤ L.length := by
    have := build_len0 cls (2 * k) L (2 * n) hcls
    rw [← hbd] at this
    have e1 : (((Finset.range (2 * k)).erase (k - 1)).erase (2 * k - 1)) ⊆
        (Finset.range (2 * k)).filter (fun c => bd.2 c ≠ none) := by
      intro c hc
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_filter] at hc ⊢
      exact ⟨hc.2.2, hsee c hc.2.2 hc.2.1 hc.1⟩
    have e2 := Finset.card_le_card e1
    rw [Finset.card_erase_of_mem (by simp; omega), Finset.card_erase_of_mem (by simp; omega),
      Finset.card_range] at e2
    omega
  let B := 2 * n + bd.1.length
  let E := B + C.gates.length
  let f : ℕ → ℕ := fun p => if p < 2 * k then (bd.2 p).getD E else B + (p - 2 * k)
  refine ⟨⟨bd.1 ++ C.gates.map (rl f), f C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · have := build_good cls _ _ _ g hg; simp [this.1, this.2]
    · obtain ⟨h1, h2⟩ := hM g0 hg0
      exact ⟨h1, by simpa [rl] using h2⟩
  · simp only [Circuit.size, List.length_append, List.length_map]
    simp only [Circuit.size] at hs
    omega
  · intro u v
    have hrk := r_lt (t u) (tS u)
    let φ : Fin k := ⟨k - 1 - r (t u), by omega⟩
    let ψ : Fin k := ⟨q v.val, q_lt v.val v.isLt⟩
    obtain ⟨hv1, hv2⟩ := hval u v
    set W := bd.1.foldl stp (oneEach u v) with hW
    have hWl : W.length = B := by rw [hW, len, hlen0]
    set S' : List Bool := (List.range (2 * k)).map (fun p => W.getD (f p) false) with hS'
    have hS'l : S'.length = 2 * k := by rw [hS']; simp
    have hS'g : ∀ p < 2 * k, S'.getD p false = W.getD (f p) false := by
      intro p hp; rw [hS']; simp [List.getD_eq_getElem?_getD, hp]
    have hc : C.eval S' = decide ((φ : ℕ) + (ψ : ℕ) ≤ k - 1) := hC φ ψ S' hS'l (fun p hp h1 h2 => by
      rw [hS'g p hp]
      simp only [f, if_pos hp]
      cases hcp : bd.2 p with
      | none => exact absurd hcp (hsee p hp h1 h2)
      | some a' =>
        simp only [Option.getD_some]
        apply Bool.eq_iff_iff.2
        rw [(hv1 p a' hcp).2, oe]
        simp only [List.nil_append, oe]
        constructor
        · rintro ⟨w, -, hcw, rfl | rfl⟩
          · left; rw [← hcw, cU]
          · right; rw [← hcw, cV]
        · rintro (h | h)
          · have hcu : cls u.val = p := by rw [cU, h]
            exact ⟨u.val, memL' u.val (by omega) (by rw [hcu]; exact h1) (by rw [hcu]; exact h2),
              hcu, Or.inl rfl⟩
          · have hcv : cls (n + v.val) = p := by rw [cV, h]
            exact ⟨n + v.val, memL' _ (by omega) (by rw [hcv]; exact h1) (by rw [hcv]; exact h2),
              hcv, Or.inr rfl⟩)
    have key2 : decide ((φ : ℕ) + (ψ : ℕ) ≤ k - 1) = decide ((v : ℕ) < t u) := by
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq, φ, ψ]
      rw [key (t u) (tS u) v.val]
      omega
    show Circuit.eval _ _ = decide ((v : ℕ) < t u)
    rw [← key2, ← hc]
    simp only [Circuit.eval, Circuit.wires]
    change ((bd.1 ++ C.gates.map (rl f)).foldl stp (oneEach u v)).getD (f C.output) false =
      (C.gates.foldl stp S').getD C.output false
    rw [List.foldl_append]
    refine copy f (2 * k) B (fun p hp => by simp only [f]; rw [if_neg (by omega)]) C.gates
      S' W (by omega) (by omega) ?_ ?_ C.output
    · intro p hp
      simp only [f, if_pos hp]
      cases hcp : bd.2 p with
      | none => right; simp only [Option.getD_none, E]; omega
      | some a' => left; simp only [Option.getD_some]; rw [← hWl]; exact (hv1 p a' hcp).1
    · intro p
      by_cases hp : p < 2 * k
      · exact (hS'g p hp).symm
      · simp only [f, if_neg hp]
        rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
