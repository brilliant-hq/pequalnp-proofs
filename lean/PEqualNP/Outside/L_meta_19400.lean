import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19400.Ext

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem ifp {c : Prop} [Decidable c] (hc : c) {α : Type} {t e : α} : (if c then t else e) = t := by
  simp [hc]

theorem ifn {c : Prop} [Decidable c] (hc : ¬ c) {α : Type} {t e : α} : (if c then t else e) = e := by
  simp [hc]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem step_ne (w : List Bool) (g : Gate) (j : ℕ) (hj : j ≠ w.length) :
    (step w g).getD j false = w.getD j false := by
  by_cases h : j < w.length
  · exact step_lt w g j h
  · rw [getD_ge _ _ (by rw [step_len]; omega), getD_ge _ _ (by omega)]

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ext_getD (a b : List Bool) (h : a.length = b.length)
    (h2 : ∀ i, i < a.length → a.getD i false = b.getD i false) : a = b := by
  apply List.ext_getElem h
  intro i h1 h3
  have := h2 i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h3] at this

theorem any_congr2 (f g : ℕ → Bool) : ∀ (l : List ℕ), (∀ a ∈ l, f a = g a) → l.any f = l.any g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

def ren (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

theorem sim (N k B : ℕ) (P : List Gate) (σ : ℕ → ℕ) (x x' : List Bool)
    (hx : x.length = N) (hx' : x'.length = N) (hP : P.length = k)
    (h1 : ∀ i, i < N → (W P x).getD (σ i) false = x'.getD i false)
    (h2 : ∀ i, i < N → σ i < N + k ∨ N + k + B ≤ σ i)
    (h3 : ∀ i, N ≤ i → σ i = i + k) (gs : List Gate) :
    gs.length ≤ B →
      ∀ i, (W (P ++ gs.map (ren σ)) x).getD (σ i) false = (W gs x').getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i
    rw [List.map_nil, List.append_nil, W_nil]
    by_cases hi : i < N
    · exact h1 i hi
    · rw [h3 i (by omega), getD_ge _ _ (by rw [W_length]; omega), getD_ge _ _ (by omega)]
  | append_singleton gs g ih =>
    intro hB i
    rw [List.length_append, List.length_singleton] at hB
    have ih' := ih (by omega)
    rw [List.map_append, ← List.append_assoc, List.map_singleton, W_snoc, W_snoc]
    have hl1 : (W (P ++ gs.map (ren σ)) x).length = N + k + gs.length := by
      rw [W_length, List.length_append, List.length_map]; omega
    have hl2 : (W gs x').length = N + gs.length := by rw [W_length]; omega
    by_cases hi : i = N + gs.length
    · rw [step_last _ _ _ (by rw [hl1, h3 i (by omega)]; omega),
        step_last _ _ _ (by rw [hl2]; exact hi)]
      show g.op.eval ((g.inputs.map σ).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih' j
    · rw [step_ne _ _ _ ?_, step_ne _ _ _ (by rw [hl2]; exact hi)]
      · exact ih' i
      · rw [hl1]
        by_cases hN : i < N
        · have := h2 i hN; omega
        · have := h3 i (by omega); omega

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | prev, pos, a :: as => ⟨GateOp.or, [prev, a]⟩ :: chain pos (pos + 1) as

def last : ℕ → ℕ → List ℕ → ℕ
  | prev, _, [] => prev
  | _, pos, _ :: as => last pos (pos + 1) as

theorem chain_length : ∀ (as : List ℕ) (prev pos : ℕ), (chain prev pos as).length = as.length := by
  intro as
  induction as with
  | nil => intro _ _; rfl
  | cons a as ih =>
    intro prev pos
    show (chain pos (pos + 1) as).length + 1 = as.length + 1
    rw [ih]

theorem chain_mono : ∀ (as : List ℕ) (prev pos : ℕ), ∀ g ∈ chain prev pos as,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro as
  induction as with
  | nil => intro _ _ g hg; cases hg
  | cons a as ih =>
    intro prev pos g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h
      exact ⟨Or.inr rfl, Nat.le_refl 2⟩
    · exact ih pos (pos + 1) g h

theorem last_lt : ∀ (as : List ℕ) (prev pos : ℕ), prev < pos →
    last prev pos as < pos + as.length := by
  intro as
  induction as with
  | nil => intro prev pos h; exact h
  | cons a as ih =>
    intro prev pos _
    have := ih pos (pos + 1) (Nat.lt_succ_self pos)
    show last pos (pos + 1) as < pos + (as.length + 1)
    omega

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem chain_val : ∀ (as : List ℕ) (prev pos : ℕ) (w : List Bool), w.length = pos → prev < pos →
    (∀ a ∈ as, a < pos) →
    (W (chain prev pos as) w).getD (last prev pos as) false =
      (w.getD prev false || as.any (fun a => w.getD a false)) := by
  intro as
  induction as with
  | nil =>
    intro prev pos w _ _ _
    show w.getD prev false = (w.getD prev false || false)
    rw [Bool.or_false]
  | cons a as ih =>
    intro prev pos w hw hp ha
    show (W (chain pos (pos + 1) as) (step w ⟨GateOp.or, [prev, a]⟩)).getD
      (last pos (pos + 1) as) false = _
    rw [ih pos (pos + 1) _ (by rw [step_len, hw]) (Nat.lt_succ_self pos)
      (fun b hb => Nat.lt_succ_of_lt (ha b (List.mem_cons_of_mem a hb)))]
    rw [step_last _ _ _ hw.symm, List.any_cons]
    rw [any_congr2 (fun b => (step w ⟨GateOp.or, [prev, a]⟩).getD b false)
      (fun b => w.getD b false) as
      (fun b hb => step_lt _ _ _ (by rw [hw]; exact ha b (List.mem_cons_of_mem a hb)))]
    show (GateOp.or.eval [w.getD prev false, w.getD a false] || _) = _
    rw [eval_or2, Bool.or_assoc]

def mergeIn (N : ℕ) (l : List ℕ) (t0 : ℕ) (x : List Bool) : List Bool :=
  List.ofFn (fun i : Fin N => if i.val = t0 then l.any (fun a => x.getD a false)
    else if i.val ∈ l then false else x.getD i.val false)

theorem mergeIn_length (N : ℕ) (l : List ℕ) (t0 : ℕ) (x : List Bool) :
    (mergeIn N l t0 x).length = N := by
  simp [mergeIn]

theorem mergeIn_getD (N : ℕ) (l : List ℕ) (t0 : ℕ) (x : List Bool) (i : ℕ) (hi : i < N) :
    (mergeIn N l t0 x).getD i false = if i = t0 then l.any (fun a => x.getD a false)
      else if i ∈ l then false else x.getD i false := by
  unfold mergeIn
  rw [ofFn_getD _ i hi]

def sig (N k M F t0 : ℕ) (l : List ℕ) (i : ℕ) : ℕ :=
  if i < N then (if i = t0 then M else if i ∈ l then F else i) else i + k

theorem merge (N : ℕ) (C : Circuit) (hC : Monotone2 C) (l : List ℕ) (t0 : ℕ)
    (hl : ∀ a ∈ l, a < N) (ht : t0 ∈ l) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size + (l.length - 1) ∧
      ∀ x : List Bool, x.length = N → C'.eval x = C.eval (mergeIn N l t0 x) := by
  cases l with
  | nil => cases ht
  | cons a0 rest =>
    have ha0 : a0 < N := hl a0 List.mem_cons_self
    have hM : last a0 N rest < N + rest.length := last_lt rest a0 N ha0
    refine ⟨⟨chain a0 N rest ++ C.gates.map
      (ren (sig N rest.length (last a0 N rest) (N + rest.length + C.gates.length) t0 (a0 :: rest))),
      sig N rest.length (last a0 N rest) (N + rest.length + C.gates.length) t0 (a0 :: rest)
        C.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact chain_mono rest a0 N g h
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp h
        have := hC g' hg'
        refine ⟨this.1, ?_⟩
        show (g'.inputs.map _).length ≤ 2
        rw [List.length_map]
        exact this.2
    · show (chain a0 N rest ++ C.gates.map _).length ≤ C.gates.length + ((a0 :: rest).length - 1)
      rw [List.length_append, List.length_map, chain_length, List.length_cons]
      omega
    · intro x hx
      rw [eval_W, eval_W]
      refine sim N rest.length C.gates.length (chain a0 N rest) _ x (mergeIn N (a0 :: rest) t0 x)
        hx (mergeIn_length _ _ _ _) (chain_length _ _ _) ?_ ?_ ?_ C.gates (Nat.le_refl _) C.output
      · intro i hi
        rw [mergeIn_getD _ _ _ _ _ hi]
        unfold sig
        rw [ifp hi]
        by_cases h1 : i = t0
        · rw [ifp h1, ifp h1, chain_val rest a0 N x hx ha0
            (fun b hb => hl b (List.mem_cons_of_mem a0 hb)), List.any_cons]
        · rw [ifn h1, ifn h1]
          by_cases h2 : i ∈ a0 :: rest
          · rw [ifp h2, ifp h2]
            exact W_ge _ _ _ (by rw [chain_length, hx]; omega)
          · rw [ifn h2, ifn h2]
            exact W_prefix _ _ _ (by rw [hx]; exact hi)
      · intro i hi
        unfold sig
        rw [ifp hi]
        by_cases h1 : i = t0
        · rw [ifp h1]; left; exact hM
        · rw [ifn h1]
          by_cases h2 : i ∈ a0 :: rest
          · rw [ifp h2]; right; exact Nat.le_refl _
          · rw [ifn h2]; left; omega
      · intro i hi
        unfold sig
        rw [ifn (by omega)]

theorem getD_app_ge (l l2 : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l2).getD i false = l2.getD (i - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

def one2 (N p q : ℕ) : List Bool :=
  List.ofFn (fun i : Fin N => decide (i.val = p) || decide (i.val = q))

theorem one2_length (N p q : ℕ) : (one2 N p q).length = N := by
  simp [one2]

theorem one2_getD (N p q i : ℕ) (hi : i < N) :
    (one2 N p q).getD i false = (decide (i = p) || decide (i = q)) := by
  unfold one2
  rw [ofFn_getD _ i hi]

theorem one2_comm (N p q : ℕ) : one2 N p q = one2 N q p := by
  unfold one2
  congr 1
  funext i
  exact Bool.or_comm _ _

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = one2 (n + m) u.val (n + v.val) := by
  apply ext_getD
  · rw [oneEach_length, one2_length]
  · intro i hi
    rw [oneEach_length] at hi
    rw [one2_getD _ _ _ _ hi]
    unfold oneEach
    have hu := u.isLt
    by_cases h : i < n
    · rw [getD_app_lt _ _ _ (by simpa using h), ofFn_getD _ i h]
      have h2 : i ≠ n + v.val := by omega
      simp [Fin.ext_iff, h2]
    · rw [getD_app_ge _ _ _ (by simpa using h), List.length_ofFn, ofFn_getD _ (i - n) (by omega)]
      have h1 : i ≠ u.val := by omega
      have h2 : (i - n = v.val) ↔ (i = n + v.val) := by omega
      simp [Fin.ext_iff, h1, h2]

theorem merge_in (N : ℕ) (l : List ℕ) (t0 p q : ℕ) (hl : ∀ a ∈ l, a < N)
    (hp : p ∈ l) (hq : q ∉ l) :
    mergeIn N l t0 (one2 N p q) = one2 N t0 q := by
  apply ext_getD
  · rw [mergeIn_length, one2_length]
  · intro i hi
    rw [mergeIn_length] at hi
    rw [mergeIn_getD _ _ _ _ _ hi, one2_getD N t0 q i hi]
    have hany : l.any (fun a => (one2 N p q).getD a false) = true := by
      rw [List.any_eq_true]
      exact ⟨p, hp, by rw [one2_getD _ _ _ _ (hl p hp)]; simp⟩
    by_cases h1 : i = t0
    · rw [ifp h1, hany]
      simp [h1]
    · rw [ifn h1]
      by_cases h2 : i ∈ l
      · rw [ifp h2]
        have h3 : i ≠ q := by intro h; rw [h] at h2; exact hq h2
        simp [h1, h3]
      · rw [ifn h2, one2_getD N p q i hi]
        have h3 : i ≠ p := by intro h; rw [h] at h2; exact h2 hp
        simp [h1, h3]

theorem merge_out (N : ℕ) (l : List ℕ) (t0 p q : ℕ) (hl : ∀ a ∈ l, a < N) (ht : t0 ∈ l)
    (hp : p ∉ l) (hq : q ∉ l) :
    mergeIn N l t0 (one2 N p q) = one2 N p q := by
  apply ext_getD
  · rw [mergeIn_length, one2_length]
  · intro i hi
    rw [mergeIn_length] at hi
    rw [mergeIn_getD _ _ _ _ _ hi, one2_getD _ _ _ _ hi]
    have hany : l.any (fun a => (one2 N p q).getD a false) = false := by
      rw [List.any_eq_false]
      intro a ha
      rw [one2_getD _ _ _ _ (hl a ha)]
      have h1 : a ≠ p := by intro h; rw [h] at ha; exact hp ha
      have h2 : a ≠ q := by intro h; rw [h] at ha; exact hq ha
      simp [h1, h2]
    by_cases h1 : i = t0
    · rw [ifp h1, hany]
      rw [← h1] at ht
      have h3 : i ≠ p := by intro h; rw [h] at ht; exact hp ht
      have h4 : i ≠ q := by intro h; rw [h] at ht; exact hq ht
      simp [h3, h4]
    · rw [ifn h1]
      by_cases h2 : i ∈ l
      · rw [ifp h2]
        have h3 : i ≠ p := by intro h; rw [h] at h2; exact hp h2
        have h4 : i ≠ q := by intro h; rw [h] at h2; exact hq h2
        simp [h3, h4]
      · rw [ifn h2]

theorem rowL_lt {n : ℕ} (m : ℕ) (U : Finset (Fin n)) :
    ∀ a ∈ U.toList.map Fin.val, a < n + m := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  have := b.isLt
  omega

theorem rowL_mem {n : ℕ} (U : Finset (Fin n)) (w : Fin n) :
    w.val ∈ U.toList.map Fin.val ↔ w ∈ U := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, hbw⟩
    rw [Fin.ext hbw] at hb
    exact Finset.mem_toList.mp hb
  · intro h
    exact ⟨w, Finset.mem_toList.mpr h, rfl⟩

theorem rowL_not {n : ℕ} (U : Finset (Fin n)) (j : ℕ) :
    n + j ∉ U.toList.map Fin.val := by
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp h
  have := b.isLt
  omega

theorem colL_lt {m : ℕ} (n : ℕ) (V : Finset (Fin m)) :
    ∀ a ∈ V.toList.map (fun v : Fin m => n + v.val), a < n + m := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  have := b.isLt
  omega

theorem colL_mem {m : ℕ} (n : ℕ) (V : Finset (Fin m)) (w : Fin m) :
    n + w.val ∈ V.toList.map (fun v : Fin m => n + v.val) ↔ w ∈ V := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, hbw⟩
    rw [Fin.ext (Nat.add_left_cancel hbw)] at hb
    exact Finset.mem_toList.mp hb
  · intro h
    exact ⟨w, Finset.mem_toList.mpr h, rfl⟩

theorem colL_not {n m : ℕ} (V : Finset (Fin m)) (u : Fin n) :
    u.val ∉ V.toList.map (fun v : Fin m => n + v.val) := by
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp h
  have := u.isLt
  omega

theorem row_merge {n m : ℕ} (U : Finset (Fin n)) (u0 : Fin n) (hu0 : u0 ∈ U) (u : Fin n)
    (v : Fin m) :
    mergeIn (n + m) (U.toList.map Fin.val) u0.val (oneEach u v) =
      oneEach (if u ∈ U then u0 else u) v := by
  by_cases h : u ∈ U
  · rw [ifp h, oneEach_eq, oneEach_eq]
    exact merge_in _ _ _ _ _ (rowL_lt m U) ((rowL_mem U u).mpr h) (rowL_not U _)
  · rw [ifn h, oneEach_eq]
    exact merge_out _ _ _ _ _ (rowL_lt m U) ((rowL_mem U u0).mpr hu0)
      (fun h' => h ((rowL_mem U u).mp h')) (rowL_not U _)

theorem col_merge {n m : ℕ} (V : Finset (Fin m)) (v0 : Fin m) (hv0 : v0 ∈ V) (u : Fin n)
    (v : Fin m) :
    mergeIn (n + m) (V.toList.map (fun v : Fin m => n + v.val)) (n + v0.val) (oneEach u v) =
      oneEach u (if v ∈ V then v0 else v) := by
  by_cases h : v ∈ V
  · rw [ifp h, oneEach_eq, oneEach_eq, one2_comm (n + m) u.val (n + v.val),
      one2_comm (n + m) u.val (n + v0.val)]
    exact merge_in _ _ _ _ _ (colL_lt n V) ((colL_mem n V v).mpr h) (colL_not V u)
  · rw [ifn h, oneEach_eq, one2_comm (n + m) u.val (n + v.val)]
    exact merge_out _ _ _ _ _ (colL_lt n V) ((colL_mem n V v0).mpr hv0)
      (fun h' => h ((colL_mem n V v).mp h')) (colL_not V u)

theorem ext_main : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m), u0 ∈ U → v0 ∈ W → (∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) → (∀ v ∈ W, ∀ u : Fin n, A u v = A u v0) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (PEqualNP.Represents.oneEach u v) = A u v) → PEqualNP.Represents.RepSizeAtMost A (s + (U.card - 1) + (W.card - 1)) := by
  intro n m s A U V u0 v0 hu0 hv0 hU hV h
  obtain ⟨C, hC, hs, hr⟩ := h
  obtain ⟨C1, hC1, hs1, he1⟩ := merge (n + m) C hC (U.toList.map Fin.val) u0.val (rowL_lt m U)
    ((rowL_mem U u0).mpr hu0)
  obtain ⟨C2, hC2, hs2, he2⟩ := merge (n + m) C1 hC1 (V.toList.map (fun v : Fin m => n + v.val))
    (n + v0.val) (colL_lt n V) ((colL_mem n V v0).mpr hv0)
  refine ⟨C2, hC2, ?_, ?_⟩
  · rw [List.length_map, Finset.length_toList] at hs1 hs2
    omega
  · intro u v
    rw [he2 _ (oneEach_length u v), col_merge V v0 hv0 u v, he1 _ (oneEach_length _ _),
      row_merge U u0 hu0]
    have hcu : (if u ∈ U then u0 else u) ∉ U ∨ (if u ∈ U then u0 else u) = u0 := by
      by_cases h : u ∈ U
      · right; rw [ifp h]
      · left; rw [ifn h]; exact h
    have hcv : (if v ∈ V then v0 else v) ∉ V ∨ (if v ∈ V then v0 else v) = v0 := by
      by_cases h : v ∈ V
      · right; rw [ifp h]
      · left; rw [ifn h]; exact h
    rw [hr _ _ hcu hcv]
    have a1 : A (if u ∈ U then u0 else u) (if v ∈ V then v0 else v) =
        A u (if v ∈ V then v0 else v) := by
      by_cases h : u ∈ U
      · rw [ifp h]; exact (hU u h _).symm
      · rw [ifn h]
    have a2 : A u (if v ∈ V then v0 else v) = A u v := by
      by_cases h : v ∈ V
      · rw [ifp h]; exact (hV v h u).symm
      · rw [ifn h]
    rw [a1, a2]

end PEqualNP.Outside.L_meta_19400.Ext

namespace PEqualNP.Outside.L_meta_19400
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem ext_main : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m), u0 ∈ U → v0 ∈ W → (∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) → (∀ v ∈ W, ∀ u : Fin n, A u v = A u v0) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (PEqualNP.Represents.oneEach u v) = A u v) → PEqualNP.Represents.RepSizeAtMost A (s + (U.card - 1) + (W.card - 1)) :=
  Ext.ext_main

theorem mono {n m : ℕ} (A : Fin n → Fin m → Bool) (s t : ℕ) (h : s ≤ t)
    (H : RepSizeAtMost A s) : RepSizeAtMost A t := by
  obtain ⟨C, h1, h2, h3⟩ := H
  exact ⟨C, h1, h2.trans h, h3⟩

theorem gL {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (u.val = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, Fin.ext_iff, eq_comm]

theorem gR {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (v.val = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, hj, Fin.ext_iff, eq_comm]

theorem gB (l vs : List Bool) (t : ℕ) : (l ++ vs).getD (l.length + t) false = vs.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem gB0 (l vs : List Bool) : (l ++ vs).getD l.length false = vs.getD 0 false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

end PEqualNP.Outside.L_meta_19400

open PEqualNP.Outside.L_meta_19400 PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19400 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (u.val = 1 ∧ ¬ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (2 ≤ u.val ∧ v.val + 1 ≠ n))) (2 * n + 1) := by
  intro n hn
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n),
      U = (Finset.univ.erase ⟨0, by omega⟩).erase ⟨1, by omega⟩ := ⟨_, rfl⟩
  have mU : ∀ u : Fin n, u ∈ U ↔ (u.val ≠ 0 ∧ u.val ≠ 1) := by
    intro u
    simp only [hU, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
    omega
  have cU : U.card = n - 1 - 1 := by
    rw [hU, Finset.card_erase_of_mem (by simp [Fin.ext_iff]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  obtain ⟨W, hW⟩ : ∃ W : Finset (Fin n),
      W = (Finset.univ.erase ⟨n - 1, by omega⟩).erase ⟨n - 2, by omega⟩ := ⟨_, rfl⟩
  have mW : ∀ v : Fin n, v ∈ W ↔ (v.val + 1 ≠ n ∧ v.val + 2 ≠ n) := by
    intro v
    simp only [hW, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
    omega
  have cW : W.card = n - 1 - 1 := by
    rw [hW, Finset.card_erase_of_mem (by simp [Fin.ext_iff]; omega),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  refine mono _ (7 + (U.card - 1) + (W.card - 1)) _ (by omega)
    (ext_main n n 7 _ U W ⟨2, by omega⟩ ⟨0, by omega⟩ ((mU _).mpr (by simp))
      ((mW _).mpr (by simp; omega)) ?_ ?_
      ⟨⟨[⟨.or, [n + (n - 1), n + (n - 2)]⟩, ⟨.or, [n + 0, n + (n - 2)]⟩, ⟨.and, [0, n + n]⟩,
        ⟨.and, [1, n + 0]⟩, ⟨.and, [2, n + n + 1]⟩, ⟨.or, [n + n + 2, n + n + 3]⟩,
        ⟨.or, [n + n + 5, n + n + 4]⟩], n + n + 6⟩, ?_, le_rfl, ?_⟩)
  · intro u hu v
    have := (mU u).mp hu
    apply decide_eq_decide.mpr
    dsimp only
    omega
  · intro v hv u
    have := (mW v).mp hv
    apply decide_eq_decide.mpr
    dsimp only
    omega
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v hu hv
    have hu' : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 := by
      rw [mU, Fin.ext_iff] at hu
      dsimp only at hu
      omega
    have hv' : v.val + 1 = n ∨ v.val + 2 = n ∨ v.val = 0 := by
      rw [mW, Fin.ext_iff] at hv
      dsimp only at hv
      omega
    have hl : (oneEach u v).length = n + n := by simp [oneEach]
    have h0 := gL u v 0 (by omega)
    have h1 := gL u v 1 (by omega)
    have h2 := gL u v 2 (by omega)
    have hc := gR u v 0 (by omega)
    have ha : (oneEach u v).getD (n + (n - 1)) false = decide (v.val + 1 = n) :=
      (gR u v (n - 1) (by omega)).trans (decide_eq_decide.mpr (by omega))
    have hb : (oneEach u v).getD (n + (n - 2)) false = decide (v.val + 2 = n) :=
      (gR u v (n - 2) (by omega)).trans (decide_eq_decide.mpr (by omega))
    generalize oneEach u v = l at hl h0 h1 h2 hc ha hb
    have i0 : 0 < l.length := by omega
    have i1 : 1 < l.length := by omega
    have i2 : 2 < l.length := by omega
    have ic : n + 0 < l.length := by omega
    have ib : n + (n - 2) < l.length := by omega
    rw [show n + n = l.length from hl.symm]
    simp only [Circuit.eval, Circuit.wires, List.foldl, List.map, List.append_assoc, List.cons_append,
      List.nil_append, List.getD_append _ _ _ _ i0, List.getD_append _ _ _ _ i1,
      List.getD_append _ _ _ _ i2, List.getD_append _ _ _ _ ic, List.getD_append _ _ _ _ ib, gB, gB0,
      h0, h1, h2, hc, ha, hb, GateOp.eval,
      List.getD_cons_zero, List.getD_cons_succ, List.all_cons, List.all_nil, List.any_cons,
      List.any_nil, id, Bool.and_true, Bool.or_false]
    by_cases k0 : u.val = 0 <;> by_cases k1 : u.val = 1 <;> by_cases k2 : u.val = 2 <;>
      by_cases ka : v.val + 1 = n <;> by_cases kb : v.val + 2 = n <;> by_cases kc : v.val = 0 <;>
      simp [k0, k1, k2, ka, kb, kc] <;> omega
