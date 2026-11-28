import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32027

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def z (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem z_true : z true = 1 := rfl
@[simp] theorem z_false : z false = 0 := rfl

def G0 : Gate := ⟨GateOp.or, []⟩

def Fo {α : Type} (d : α) (H : Gate → List α → α) (w : List α) (gs : List Gate) : List α :=
  gs.foldl (fun ds g => ds ++ [H g (g.inputs.map fun a => ds.getD a d)]) w

theorem Fo_nil {α : Type} (d : α) (H : Gate → List α → α) (w : List α) : Fo d H w [] = w := rfl

theorem Fo_cons {α : Type} (d : α) (H : Gate → List α → α) (w : List α) (g : Gate) (gs : List Gate) :
    Fo d H w (g :: gs) = Fo d H (w ++ [H g (g.inputs.map fun a => w.getD a d)]) gs := rfl

theorem Fo_append {α : Type} (d : α) (H : Gate → List α → α) (w : List α) (gs1 gs2 : List Gate) :
    Fo d H w (gs1 ++ gs2) = Fo d H (Fo d H w gs1) gs2 := by
  unfold Fo; rw [List.foldl_append]

theorem Fo_ext {α : Type} (d : α) (H : Gate → List α → α) (gs : List Gate) :
    ∀ w : List α, ∃ t, Fo d H w gs = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [Fo_nil]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [H g (g.inputs.map fun a => w.getD a d)])
    refine ⟨H g (g.inputs.map fun a => w.getD a d) :: t, ?_, ?_⟩
    · rw [Fo_cons, ht]; simp
    · simp [hl]

theorem Fo_len {α : Type} (d : α) (H : Gate → List α → α) (w : List α) (gs : List Gate) :
    (Fo d H w gs).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := Fo_ext d H gs w
  rw [ht]; simp [hl]

theorem Fo_pre {α : Type} (d : α) (H : Gate → List α → α) (w : List α) (gs : List Gate) (i : ℕ)
    (hi : i < w.length) : (Fo d H w gs).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := Fo_ext d H gs w
  rw [ht, List.getD_append _ _ _ _ hi]

theorem Fo_gate {α : Type} (d : α) (H : Gate → List α → α) (gs : List Gate) :
    ∀ (w : List α) (k : ℕ), k < gs.length →
    (∀ i ∈ (gs.getD k G0).inputs, i < w.length + k) →
    (Fo d H w gs).getD (w.length + k) d =
      H (gs.getD k G0) ((gs.getD k G0).inputs.map fun a => (Fo d H w gs).getD a d) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk hrb
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero] at hrb ⊢
      rw [Fo_cons, Fo_pre _ _ _ _ _ (by simp)]
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro a ha
      rw [Fo_pre _ _ _ _ _ (by simp; have := hrb a ha; omega)]
      rw [List.getD_append _ _ _ _ (hrb a ha)]
    | succ k =>
      simp only [List.getD_cons_succ] at hrb ⊢
      simp only [List.length_cons] at hk
      have := ih (w ++ [H g (g.inputs.map fun a => w.getD a d)]) k (by omega)
        (by intro i hi; have := hrb i hi; simp; omega)
      rw [Fo_cons]
      simp only [List.length_append, List.length_singleton] at this
      rw [show w.length + (k + 1) = w.length + 1 + k by omega]
      exact this

def ev (g : Gate) (l : List Bool) : Bool := g.op.eval l

def nl (g : Gate) : Bool := (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def Hd (g : Gate) (l : List ℕ) : ℕ := l.foldr max 0 + (nl g).toNat

theorem ev2 (f : List Bool → Bool) (a b : Bool) :
    z (f [a, b]) = z (f [false, false]) + (z (f [false, false]) + z (f [true, false])) * z a +
      (z (f [false, false]) + z (f [false, true])) * z b +
      (z (f [false, false]) + z (f [false, true]) + z (f [true, false]) + z (f [true, true])) * z a * z b := by
  generalize h1 : f [false, false] = p1
  generalize h2 : f [false, true] = p2
  generalize h3 : f [true, false] = p3
  generalize h4 : f [true, true] = p4
  cases a <;> cases b <;> simp only [h1, h2, h3, h4] <;>
    cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;> decide

theorem ev1 (f : List Bool → Bool) (a : Bool) :
    z (f [a]) = z (f [false]) + (z (f [false]) + z (f [true])) * z a := by
  generalize h1 : f [false] = p1
  generalize h2 : f [true] = p2
  cases a <;> simp only [h1, h2] <;> cases p1 <;> cases p2 <;> decide

theorem z_xor4 (p q r s : Bool) : z (xor (xor p q) (xor r s)) = z p + z q + z r + z s := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

theorem nl_two (g : Gate) (h : g.inputs.length = 2) :
    z (nl g) = z (g.op.eval [false, false]) + z (g.op.eval [false, true]) +
      z (g.op.eval [true, false]) + z (g.op.eval [true, true]) := by
  unfold nl; rw [h]; simp only [beq_self_eq_true, Bool.true_and]; exact z_xor4 _ _ _ _

theorem z_sq (b : Bool) : z b * z b = z b := by cases b <;> decide

theorem zz (c : ZMod 2) : c + c = 0 := by fin_cases c <;> decide

def chainAux : ℕ → List ℕ → List Gate
  | _, [] => []
  | p, w :: ws => ⟨GateOp.mod 2, [p, w]⟩ :: ⟨GateOp.not, [p + 1]⟩ :: chainAux (p + 2) ws

def chain (p : ℕ) (ws : List ℕ) : List Gate := G0 :: chainAux p ws

theorem chainAux_len (ws : List ℕ) : ∀ p, (chainAux p ws).length = 2 * ws.length := by
  induction ws with
  | nil => intro p; rfl
  | cons w ws ih => intro p; simp only [chainAux, List.length_cons, ih]; ring

theorem chain_len (p : ℕ) (ws : List ℕ) : (chain p ws).length = 2 * ws.length + 1 := by
  simp [chain, chainAux_len]

theorem xorgate (a b : Bool) :
    z (GateOp.eval GateOp.not [GateOp.eval (GateOp.mod 2) [a, b]]) = z a + z b := by
  cases a <;> cases b <;> decide

theorem app2_pre {α : Type} (W : List α) (a b : α) (d : α) (i : ℕ) (hi : i < W.length) :
    (W ++ [a] ++ [b]).getD i d = W.getD i d := by
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem app2_last {α : Type} (W : List α) (a b : α) (d : α) :
    (W ++ [a] ++ [b]).getD (W.length + 1) d = b := by
  rw [List.getD_append_right _ _ _ _ (by simp)]; simp

theorem app1_last {α : Type} (W : List α) (a : α) (d : α) :
    (W ++ [a]).getD W.length d = a := by
  rw [List.getD_append_right _ _ _ _ (by simp)]; simp

theorem chainAux_val (ws : List ℕ) : ∀ (p : ℕ) (W : List Bool), W.length = p + 1 →
    (∀ w ∈ ws, w < p + 1) →
    z ((Fo false ev W (chainAux p ws)).getD (p + 2 * ws.length) false) =
      z (W.getD p false) + (ws.map fun w => z (W.getD w false)).sum := by
  induction ws with
  | nil => intro p W _ _; simp [chainAux, Fo_nil]
  | cons w ws ih =>
    intro p W hW hws
    simp only [chainAux, Fo_cons]
    have hw : w < p + 1 := hws w (by simp)
    set W1 := W ++ [ev ⟨GateOp.mod 2, [p, w]⟩ (([p, w] : List ℕ).map fun a => W.getD a false)] with hW1
    set W2 := W1 ++ [ev ⟨GateOp.not, [p + 1]⟩ (([p + 1] : List ℕ).map fun a => W1.getD a false)] with hW2
    have hl : W2.length = (p + 2) + 1 := by simp [hW2, hW1, hW]
    have hpre : ∀ i < p + 1, W2.getD i false = W.getD i false := by
      intro i hi; rw [hW2, hW1]; exact app2_pre _ _ _ _ _ (by omega)
    have hv : W2.getD (p + 2) false =
        GateOp.eval GateOp.not [GateOp.eval (GateOp.mod 2) [W.getD p false, W.getD w false]] := by
      rw [hW2, hW1, show p + 2 = W.length + 1 by omega, app2_last]
      simp only [ev, List.map_cons, List.map_nil]
      rw [show p + 1 = W.length by omega, app1_last]
    rw [show p + 2 * (w :: ws).length = (p + 2) + 2 * ws.length by simp; ring]
    rw [ih (p + 2) W2 hl (by intro w' hw'; have := hws w' (by simp [hw']); omega)]
    rw [List.map_congr_left (fun w' hw' => by
      rw [hpre w' (hws w' (by simp [hw']))])]
    rw [hv, xorgate]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem chainAux_dep (ws : List ℕ) : ∀ (p : ℕ) (W : List ℕ) (c : ℕ), W.length = p + 1 →
    (∀ w ∈ ws, w < p + 1) → W.getD p 0 ≤ c → (∀ w ∈ ws, W.getD w 0 ≤ c) →
    (Fo 0 Hd W (chainAux p ws)).getD (p + 2 * ws.length) 0 ≤ c := by
  induction ws with
  | nil => intro p W c _ _ h _; simpa [chainAux, Fo_nil] using h
  | cons w ws ih =>
    intro p W c hW hws hp hc
    simp only [chainAux, Fo_cons]
    have hw : w < p + 1 := hws w (by simp)
    set W1 := W ++ [Hd ⟨GateOp.mod 2, [p, w]⟩ (([p, w] : List ℕ).map fun a => W.getD a 0)] with hW1
    set W2 := W1 ++ [Hd ⟨GateOp.not, [p + 1]⟩ (([p + 1] : List ℕ).map fun a => W1.getD a 0)] with hW2
    have hl : W2.length = (p + 2) + 1 := by simp [hW2, hW1, hW]
    have hpre : ∀ i < p + 1, W2.getD i 0 = W.getD i 0 := by
      intro i hi; rw [hW2, hW1]; exact app2_pre _ _ _ _ _ (by omega)
    have hv : W2.getD (p + 2) 0 = max (W.getD p 0) (W.getD w 0) := by
      rw [hW2, hW1, show p + 2 = W.length + 1 by omega, app2_last]
      simp only [Hd, List.map_cons, List.map_nil]
      rw [show p + 1 = W.length by omega, app1_last]
      simp [Hd, nl, GateOp.eval, List.foldr]
    rw [show p + 2 * (w :: ws).length = (p + 2) + 2 * ws.length by simp; ring]
    apply ih (p + 2) W2 c hl (by intro w' hw'; have := hws w' (by simp [hw']); omega)
    · rw [hv]; exact max_le hp (hc w (by simp))
    · intro w' hw'
      rw [hpre w' (hws w' (by simp [hw']))]
      exact hc w' (by simp [hw'])

theorem onehot (n m : ℕ) (u : Fin n) (v : Fin m) (a : ℕ) :
    z ((oneEach u v).getD a false) = (if a = u.val then 1 else 0) + (if a = n + v.val then 1 else 0) := by
  unfold oneEach
  rcases Nat.lt_or_ge a n with h | h
  · rw [List.getD_append _ _ _ _ (by simp; omega)]
    have : a ≠ n + v.val := by omega
    simp only [this, if_false, add_zero]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_ofFn]
    by_cases hu : a = u.val
    · simp [hu]
    · have : (⟨a, h⟩ : Fin n) ≠ u := fun e => hu (by rw [← e])
      simp [hu, this]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have : a ≠ u.val := by omega
    simp only [this, if_false, zero_add, List.length_ofFn]
    rcases Nat.lt_or_ge (a - n) m with h2 | h2
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      by_cases hv : a = n + v.val
      · have : (⟨a - n, h2⟩ : Fin m) = v := by ext; simp; omega
        simp [hv, this]
      · have : (⟨a - n, h2⟩ : Fin m) ≠ v := fun e => hv (by rw [← e]; simp; omega)
        simp [hv, this]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have : a ≠ n + v.val := by omega
      simp [this]

def mask (N p : ℕ) (ν : ℕ → ZMod 2) : List ℕ := (List.range N).map (fun i => if ν i = 1 then i else p)

theorem mask_len (N p : ℕ) (ν : ℕ → ZMod 2) : (mask N p ν).length = N := by simp [mask]

theorem mask_le (N p : ℕ) (ν : ℕ → ZMod 2) (h : N ≤ p) : ∀ w ∈ mask N p ν, w ≤ p := by
  intro w hw
  simp only [mask, List.mem_map, List.mem_range] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  split_ifs <;> omega

theorem z01 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  exacts [Or.inl rfl, Or.inr rfl]

theorem mask_sum (N p : ℕ) (ν : ℕ → ZMod 2) (V : ℕ → ZMod 2) (hp : V p = 0) :
    ((mask N p ν).map V).sum = ∑ i ∈ Finset.range N, ν i * V i := by
  induction N with
  | zero => simp [mask]
  | succ N ih =>
    simp only [mask] at ih ⊢
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    congr 1
    rcases z01 (ν N) with h | h <;> simp [h, hp]

theorem onehot_sum (n m : ℕ) (u : Fin n) (v : Fin m) (ν : ℕ → ZMod 2) :
    ∑ i ∈ Finset.range (n + m), ν i * z ((oneEach u v).getD i false) = ν u.val + ν (n + v.val) := by
  simp only [onehot, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega)]

theorem chain_val (p : ℕ) (ws : List ℕ) (W : List Bool) (hW : W.length = p) (hws : ∀ w ∈ ws, w ≤ p) :
    z ((Fo false ev W (chain p ws)).getD (p + 2 * ws.length) false) =
      (ws.map fun w => z ((W ++ [false]).getD w false)).sum := by
  unfold chain; rw [Fo_cons]
  have h0 : ev G0 (G0.inputs.map fun a => W.getD a false) = false := rfl
  rw [h0, chainAux_val ws p (W ++ [false]) (by simp [hW]) (by intro w hw; have := hws w hw; omega)]
  rw [← hW, app1_last]; simp

theorem chain_dep (p : ℕ) (ws : List ℕ) (W : List ℕ) (c : ℕ) (hW : W.length = p)
    (hws : ∀ w ∈ ws, w ≤ p) (hc : ∀ w ∈ ws, w < p → W.getD w 0 ≤ c) :
    (Fo 0 Hd W (chain p ws)).getD (p + 2 * ws.length) 0 ≤ c := by
  unfold chain; rw [Fo_cons]
  have h0 : Hd G0 (G0.inputs.map fun a => W.getD a 0) = 0 := rfl
  rw [h0]
  apply chainAux_dep ws p (W ++ [0]) c (by simp [hW]) (by intro w hw; have := hws w hw; omega)
  · rw [← hW, app1_last]; omega
  · intro w hw
    rcases Nat.lt_or_ge w p with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]; exact hc w hw h
    · have : w = p := le_antisymm (hws w hw) h
      rw [this, ← hW, app1_last]; omega

def RB (N : ℕ) (gs : List Gate) : Prop := ∀ k < gs.length, ∀ i ∈ (gs.getD k G0).inputs, i < N + k

theorem RB_nil (N : ℕ) : RB N [] := by intro k hk; simp at hk

theorem RB_cons (N : ℕ) (g : Gate) (gs : List Gate) (h1 : ∀ i ∈ g.inputs, i < N) (h2 : RB (N + 1) gs) :
    RB N (g :: gs) := by
  intro k hk i hi
  cases k with
  | zero => simpa using h1 i hi
  | succ k =>
    simp only [List.getD_cons_succ] at hi
    have := h2 k (by simp at hk; omega) i hi; omega

theorem RB_append (N : ℕ) (gs1 gs2 : List Gate) (h1 : RB N gs1) (h2 : RB (N + gs1.length) gs2) :
    RB N (gs1 ++ gs2) := by
  intro k hk i hi
  rcases Nat.lt_or_ge k gs1.length with h | h
  · rw [List.getD_append _ _ _ _ h] at hi; exact h1 k h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    have := h2 (k - gs1.length) (by simp at hk; omega) i hi; omega

theorem RB_chainAux (ws : List ℕ) : ∀ p, (∀ w ∈ ws, w ≤ p) → RB (p + 1) (chainAux p ws) := by
  induction ws with
  | nil => intro p _; exact RB_nil _
  | cons w ws ih =>
    intro p hws
    apply RB_cons
    · intro i hi; simp at hi; rcases hi with rfl | rfl
      · omega
      · have := hws i (by simp); omega
    apply RB_cons
    · intro i hi; simp at hi; omega
    have := ih (p + 2) (by intro w' hw'; have := hws w' (by simp [hw']); omega)
    simpa [show p + 1 + 1 + 1 = p + 2 + 1 by omega] using this

theorem RB_chain (p : ℕ) (ws : List ℕ) (hws : ∀ w ∈ ws, w ≤ p) : RB p (chain p ws) := by
  apply RB_cons
  · intro i hi; simp [G0] at hi
  · exact RB_chainAux ws p hws

theorem chainAux_gates (ws : List ℕ) : ∀ p, ∀ g ∈ chainAux p ws, g.inputs.length ≤ 2 ∧ nl g = false := by
  induction ws with
  | nil => intro p g hg; simp [chainAux] at hg
  | cons w ws ih =>
    intro p g hg
    simp only [chainAux, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · refine ⟨by simp, rfl⟩
    · refine ⟨by simp, by simp [nl]⟩
    · exact ih (p + 2) g hg

theorem chain_gates (p : ℕ) (ws : List ℕ) : ∀ g ∈ chain p ws, g.inputs.length ≤ 2 ∧ nl g = false := by
  intro g hg
  simp only [chain, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact ⟨by simp [G0], by simp [nl, G0]⟩
  · exact chainAux_gates ws p g hg

def blocks (f : ℕ → List Gate) : ℕ → List Gate
  | 0 => []
  | k + 1 => blocks f k ++ f k

theorem blocks_len (f : ℕ → List Gate) (b : ℕ) (hb : ∀ a, (f a).length = b) :
    ∀ k, (blocks f k).length = k * b := by
  intro k; induction k with
  | zero => simp [blocks]
  | succ k ih => simp [blocks, ih, hb]; ring

theorem blocks_mem (f : ℕ → List Gate) (P : Gate → Prop) (hP : ∀ a, ∀ g ∈ f a, P g) :
    ∀ k, ∀ g ∈ blocks f k, P g := by
  intro k; induction k with
  | zero => intro g hg; simp [blocks] at hg
  | succ k ih =>
    intro g hg; simp only [blocks, List.mem_append] at hg
    rcases hg with h | h
    · exact ih g h
    · exact hP k g h

theorem blocks_RB (f : ℕ → List Gate) (N b : ℕ) (hb : ∀ a, (f a).length = b)
    (hr : ∀ a, RB (N + a * b) (f a)) : ∀ k, RB N (blocks f k) := by
  intro k; induction k with
  | zero => exact RB_nil _
  | succ k ih =>
    apply RB_append _ _ _ ih
    rw [blocks_len f b hb]; exact hr k

theorem blocks_out {α : Type} (d : α) (H : Gate → List α → α) (f : ℕ → List Gate) (b : ℕ)
    (hb : ∀ a, (f a).length = b) (W : List α) (o : ℕ) (ho : o < b) :
    ∀ K, ∀ a < K, (Fo d H W (blocks f K)).getD (W.length + a * b + o) d =
      (Fo d H (Fo d H W (blocks f a)) (f a)).getD (W.length + a * b + o) d := by
  intro K; induction K with
  | zero => intro a ha; omega
  | succ K ih =>
    intro a ha
    simp only [blocks]; rw [Fo_append]
    rcases Nat.lt_or_ge a K with h | h
    · rw [Fo_pre _ _ _ _ _ (by rw [Fo_len, blocks_len f b hb]; nlinarith)]
      exact ih a h
    · have : a = K := by omega
      subst this; rfl

theorem blocks_Fo_len {α : Type} (d : α) (H : Gate → List α → α) (f : ℕ → List Gate) (b : ℕ)
    (hb : ∀ a, (f a).length = b) (W : List α) (a : ℕ) :
    (Fo d H W (blocks f a)).length = W.length + a * b := by
  rw [Fo_len, blocks_len f b hb]

theorem blocks_countP (f : ℕ → List Gate) (hf : ∀ a, ∀ g ∈ f a, nl g = false) :
    ∀ k, (blocks f k).countP nl = 0 := by
  intro k
  rw [List.countP_eq_zero]
  intro g hg
  have := blocks_mem f (fun g => nl g = false) hf k g hg
  simp [this]

section Sim

variable {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m))

def Pz (M : Fin n → Fin m → ZMod 2) (x : Fin n') (y : Fin m') : ZMod 2 :=
  ∑ i ∈ R x, ∑ j ∈ Cc y, M i j

def LA (A : Fin n → ZMod 2) (x : Fin n') : ZMod 2 := ∑ i ∈ R x, A i

def LB (B : Fin m → ZMod 2) (y : Fin m') : ZMod 2 := ∑ j ∈ Cc y, B j

theorem Pz_lin (c0 c1 c2 c3 : ZMod 2) (M1 M2 : Fin n → Fin m → ZMod 2) (x : Fin n') (y : Fin m') :
    Pz R Cc (fun u v => c0 + c1 * M1 u v + c2 * M2 u v + c3 * (M1 u v * M2 u v)) x y =
      c0 * (((R x).card : ZMod 2) * ((Cc y).card : ZMod 2)) + c1 * Pz R Cc M1 x y +
      c2 * Pz R Cc M2 x y + c3 * Pz R Cc (fun u v => M1 u v * M2 u v) x y := by
  simp only [Pz, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem Pz_lin1 (c0 c1 : ZMod 2) (M1 : Fin n → Fin m → ZMod 2) (x : Fin n') (y : Fin m') :
    Pz R Cc (fun u v => c0 + c1 * M1 u v) x y =
      c0 * (((R x).card : ZMod 2) * ((Cc y).card : ZMod 2)) + c1 * Pz R Cc M1 x y := by
  simp only [Pz, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem Pz_aff (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (x : Fin n') (y : Fin m') :
    Pz R Cc (fun u v => A u + B v) x y =
      ((Cc y).card : ZMod 2) * LA R A x + ((R x).card : ZMod 2) * LB Cc B y := by
  simp only [Pz, LA, LB, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]

theorem Pz_prod (A1 A2 : Fin n → ZMod 2) (B1 B2 : Fin m → ZMod 2) (x : Fin n') (y : Fin m') :
    Pz R Cc (fun u v => (A1 u + B1 v) * (A2 u + B2 v)) x y =
      ((Cc y).card : ZMod 2) * LA R (fun i => A1 i * A2 i) x + LA R A1 x * LB Cc B2 y +
      LA R A2 x * LB Cc B1 y + ((R x).card : ZMod 2) * LB Cc (fun j => B1 j * B2 j) y := by
  have e : ∀ u v, (A1 u + B1 v) * (A2 u + B2 v) =
      A1 u * A2 u + A1 u * B2 v + A2 u * B1 v + B1 v * B2 v := fun u v => by ring
  simp only [Pz, LA, LB, e, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h1 : ∑ i ∈ R x, ((Cc y).card : ZMod 2) * (A1 i * A2 i) =
      ((Cc y).card : ZMod 2) * ∑ i ∈ R x, A1 i * A2 i := by rw [Finset.mul_sum]
  rw [h1, Finset.sum_mul_sum, Finset.sum_mul_sum]

theorem LA_aff (c d : ZMod 2) (A : Fin n → ZMod 2) (x : Fin n') :
    LA R (fun i => c + d * A i) x = c * ((R x).card : ZMod 2) + d * LA R A x := by
  simp only [LA, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; ring

theorem LB_aff (c d : ZMod 2) (B : Fin m → ZMod 2) (y : Fin m') :
    LB Cc (fun j => c + d * B j) y = c * ((Cc y).card : ZMod 2) + d * LB Cc B y := by
  simp only [LB, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; ring

end Sim

def nu {n' m' : ℕ} (A : Fin n' → ZMod 2) (B : Fin m' → ZMod 2) (i : ℕ) : ZMod 2 :=
  if h : i < n' then A ⟨i, h⟩ else if h2 : i - n' < m' then B ⟨i - n', h2⟩ else 0

theorem nu_l {n' m' : ℕ} (A : Fin n' → ZMod 2) (B : Fin m' → ZMod 2) (x : Fin n') :
    nu A B x.val = A x := by simp [nu]

theorem nu_r {n' m' : ℕ} (A : Fin n' → ZMod 2) (B : Fin m' → ZMod 2) (y : Fin m') :
    nu A B (n' + y.val) = B y := by
  simp [nu]

theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem z_inj (a b : Bool) (h : z a = z b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def V {n m : ℕ} (gs : List Gate) (a : ℕ) (u : Fin n) (v : Fin m) : ZMod 2 :=
  z ((Fo false ev (oneEach u v) gs).getD a false)

def Dp (N : ℕ) (gs : List Gate) (a : ℕ) : ℕ := (Fo 0 Hd (List.replicate N 0) gs).getD a 0

def tapBlk (N P : ℕ) (ν : ℕ → ℕ → ZMod 2) (ψ : ℕ → ℕ) (j : ℕ) : List Gate :=
  chain (P + j * (2 * (N + 1) + 1)) (mask N (P + j * (2 * (N + 1) + 1)) (ν j) ++ [ψ j])

theorem tapBlk_len (N P : ℕ) (ν : ℕ → ℕ → ZMod 2) (ψ : ℕ → ℕ) (j : ℕ) :
    (tapBlk N P ν ψ j).length = 2 * (N + 1) + 1 := by
  simp [tapBlk, chain_len, mask_len]

def Fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ),
    ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nl ≤ t ∧
    ∀ j : Fin q, (Fo 0 Hd (List.replicate (n+m) 0) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates, tap j⟩

theorem tapsFit (n' m' q s : ℕ) (hn : 0 < n') (base : List Gate) (hRB : RB (n' + m') base)
    (hfan : ∀ g ∈ base, g.inputs.length ≤ 2) (hcnt : base.countP nl ≤ s)
    (ψ : Fin q → ℕ) (hψ : ∀ j, ψ j < n' + m' + base.length) (hD : ∀ j, Dp (n' + m') base (ψ j) ≤ 1)
    (A : Fin q → Fin n' → ZMod 2) (B : Fin q → Fin m' → ZMod 2) (H : Fin q → Fin n' → Fin m' → Bool)
    (hval : ∀ j x y, z (H j x y) = A j x + B j y + V base (ψ j) x y) : Fits n' m' q H s := by
  set N := n' + m' with hN
  set P := N + base.length with hP
  set b2 := 2 * (N + 1) + 1 with hb2
  let νN : ℕ → ℕ → ZMod 2 := fun j => if h : j < q then nu (A ⟨j, h⟩) (B ⟨j, h⟩) else fun _ => 0
  let ψN : ℕ → ℕ := fun j => if h : j < q then ψ ⟨j, h⟩ else 0
  have hψN : ∀ j, ψN j < P := by
    intro j; simp only [ψN]; split_ifs
    · exact hψ _
    · omega
  have hlen : ∀ j, (tapBlk N P νN ψN j).length = b2 := fun j => tapBlk_len N P νN ψN j
  have hws : ∀ j, ∀ w ∈ mask N (P + j * b2) (νN j) ++ [ψN j], w ≤ P + j * b2 := by
    intro j w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | hw
    · exact mask_le N _ _ (by omega) w hw
    · have := hψN j; rw [hw]; omega
  refine ⟨⟨base ++ blocks (tapBlk N P νN ψN) q, 0⟩, fun j => P + j.val * b2 + 2 * (N + 1), ?_, ?_, ?_, ?_⟩
  · show RB N (base ++ blocks (tapBlk N P νN ψN) q)
    apply RB_append _ _ _ hRB
    apply blocks_RB _ _ b2 hlen
    intro a
    exact RB_chain _ _ (hws a)
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hfan g hg
    · exact (blocks_mem _ (fun g => g.inputs.length ≤ 2 ∧ nl g = false)
        (fun a g hg => chain_gates _ _ g (by unfold tapBlk at hg; exact hg)) q g hg).1
  · show (base ++ blocks (tapBlk N P νN ψN) q).countP nl ≤ s
    rw [List.countP_append, blocks_countP (tapBlk N P νN ψN)
      (fun a g hg => (chain_gates _ _ g (by unfold tapBlk at hg; exact hg)).2) q]; omega
  · intro j
    have hj := j.isLt
    constructor
    · show (Fo 0 Hd (List.replicate N 0) (base ++ blocks (tapBlk N P νN ψN) q)).getD _ 0 ≤ 1
      rw [Fo_append]
      have hl0 : (Fo 0 Hd (List.replicate N 0) base).length = P := by
        rw [Fo_len]; simp [hP]
      have := blocks_out 0 Hd (tapBlk N P νN ψN) b2 hlen (Fo 0 Hd (List.replicate N 0) base)
        (2 * (N + 1)) (by omega) q j.val hj
      rw [hl0] at this
      rw [this]
      have hlj := blocks_Fo_len 0 Hd (tapBlk N P νN ψN) b2 hlen (Fo 0 Hd (List.replicate N 0) base) j.val
      rw [hl0] at hlj
      have := chain_dep (P + j.val * b2) (mask N (P + j.val * b2) (νN j.val) ++ [ψN j.val]) _ 1 hlj
        (hws j.val)
      simp only [List.length_append, mask_len, List.length_singleton] at this
      apply this
      intro w hw hwp
      have hwlt : w < P := by
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | hw
        · simp only [mask, List.mem_map, List.mem_range] at hw
          obtain ⟨i, hi, rfl⟩ := hw; split_ifs at hwp ⊢ <;> omega
        · rw [hw]; exact hψN _
      rw [Fo_pre _ _ _ _ _ (by rw [hl0]; exact hwlt)]
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · simp only [mask, List.mem_map, List.mem_range] at hw
        obtain ⟨i, hi, rfl⟩ := hw
        split_ifs at hwp ⊢ with h1
        · rw [Fo_pre _ _ _ _ _ (by simp; omega)]; simp [List.getD_replicate, hi]
        · omega
      · rw [hw]; simp only [ψN, dif_pos hj]; exact hD j
    · intro x y
      apply z_inj
      rw [hval j x y]
      show z ((Fo false ev (oneEach x y) (base ++ blocks (tapBlk N P νN ψN) q)).getD _ false) = _
      rw [Fo_append]
      have hl0 : (Fo false ev (oneEach x y) base).length = P := by
        rw [Fo_len, oneEach_len]
      have := blocks_out false ev (tapBlk N P νN ψN) b2 hlen (Fo false ev (oneEach x y) base)
        (2 * (N + 1)) (by omega) q j.val hj
      rw [hl0] at this
      rw [this]
      have hlj := blocks_Fo_len false ev (tapBlk N P νN ψN) b2 hlen (Fo false ev (oneEach x y) base) j.val
      rw [hl0] at hlj
      have := chain_val (P + j.val * b2) (mask N (P + j.val * b2) (νN j.val) ++ [ψN j.val]) _ hlj
        (hws j.val)
      simp only [List.length_append, mask_len, List.length_singleton] at this
      rw [show tapBlk N P νN ψN j.val = chain (P + j.val * b2)
        (mask N (P + j.val * b2) (νN j.val) ++ [ψN j.val]) from rfl]
      rw [this, List.map_append, List.sum_append]
      rw [mask_sum _ _ _ _ (by rw [← hlj, app1_last]; rfl)]
      have e1 : ∀ i ∈ Finset.range N, νN j.val i *
          z ((Fo false ev (Fo false ev (oneEach x y) base) (blocks (tapBlk N P νN ψN) j.val) ++
            [false]).getD i false) = nu (A j) (B j) i * z ((oneEach x y).getD i false) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [List.getD_append _ _ _ _ (by rw [hlj]; omega), Fo_pre _ _ _ _ _ (by rw [hl0]; omega),
          Fo_pre _ _ _ _ _ (by rw [oneEach_len]; omega)]
        simp only [νN, dif_pos hj]
      rw [Finset.sum_congr rfl e1, onehot_sum, nu_l, nu_r]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [List.getD_append _ _ _ _ (by rw [hlj]; have := hψN j.val; omega),
        Fo_pre _ _ _ _ _ (by rw [hl0]; exact hψN _)]
      simp only [ψN, dif_pos hj, V]

theorem two0 : (2 : ZMod 2) = 0 := rfl

section Alg

variable {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m))
  (ρ σ : ZMod 2) (hρ : ∀ x, ((R x).card : ZMod 2) = ρ) (hσ : ∀ y, ((Cc y).card : ZMod 2) = σ)
include hρ hσ

theorem I0_I1 (f : Fin n → Fin m → ZMod 2) (g : Fin n' → Fin m' → ZMod 2) (A : Fin n → ZMod 2)
    (B : Fin m → ZMod 2) (k : ZMod 2) (hf : ∀ u v, f u v = A u + B v)
    (hg : ∀ x y, g x y = LA R A x + LB Cc B y + k) :
    ∃ (A' : Fin n' → ZMod 2) (B' : Fin m' → ZMod 2), ∀ x y, Pz R Cc f x y + g x y = A' x + B' y := by
  refine ⟨fun x => σ * LA R A x + LA R A x + k, fun y => ρ * LB Cc B y + LB Cc B y, fun x y => ?_⟩
  have : f = fun u v => A u + B v := funext fun u => funext fun v => hf u v
  rw [this, Pz_aff, hg, hρ, hσ]; ring

theorem lin_I0 (c0 c1 c2 : ZMod 2) (fb fc : Fin n → Fin m → ZMod 2) (gb gc : Fin n' → Fin m' → ZMod 2)
    (Ab Ac : Fin n → ZMod 2) (Bb Bc : Fin m → ZMod 2) (kb kc : ZMod 2)
    (hfb : ∀ u v, fb u v = Ab u + Bb v) (hgb : ∀ x y, gb x y = LA R Ab x + LB Cc Bb y + kb)
    (hfc : ∀ u v, fc u v = Ac u + Bc v) (hgc : ∀ x y, gc x y = LA R Ac x + LB Cc Bc y + kc) :
    ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (k : ZMod 2),
      (∀ u v, c0 + c1 * fb u v + c2 * fc u v = A u + B v) ∧
      ∀ x y, c0 + c1 * gb x y + c2 * gc x y = LA R A x + LB Cc B y + k := by
  refine ⟨fun i => c0 + c1 * Ab i + c2 * Ac i, fun j => c1 * Bb j + c2 * Bc j,
    c0 + c0 * ρ + c1 * kb + c2 * kc, fun u v => ?_, fun x y => ?_⟩
  · rw [hfb, hfc]; ring
  · rw [hgb, hgc]
    simp only [LA, LB, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      mul_zero, add_zero]
    rw [hρ]
    ring_nf
    simp only [two0, mul_zero, zero_mul, add_zero, zero_add]

theorem lin_I1 (c0 c1 c2 : ZMod 2) (fb fc : Fin n → Fin m → ZMod 2) (gb gc : Fin n' → Fin m' → ZMod 2)
    (Ab Ac : Fin n' → ZMod 2) (Bb Bc : Fin m' → ZMod 2)
    (hb : ∀ x y, Pz R Cc fb x y + gb x y = Ab x + Bb y)
    (hc : ∀ x y, Pz R Cc fc x y + gc x y = Ac x + Bc y) :
    ∃ (A' : Fin n' → ZMod 2) (B' : Fin m' → ZMod 2), ∀ x y,
      Pz R Cc (fun u v => c0 + c1 * fb u v + c2 * fc u v) x y + (c0 + c1 * gb x y + c2 * gc x y) =
        A' x + B' y := by
  refine ⟨fun x => c0 * (ρ * σ) + c0 + c1 * Ab x + c2 * Ac x, fun y => c1 * Bb y + c2 * Bc y,
    fun x y => ?_⟩
  have e := Pz_lin R Cc c0 c1 c2 0 fb fc x y
  simp only [zero_mul, add_zero] at e
  rw [e, hρ, hσ]
  have h1 := hb x y
  have h2 := hc x y
  linear_combination c1 * h1 + c2 * h2

theorem prod_I1 (c0 c1 c2 : ZMod 2) (fb fc : Fin n → Fin m → ZMod 2) (gb gc : Fin n' → Fin m' → ZMod 2)
    (Ab Ac : Fin n → ZMod 2) (Bb Bc : Fin m → ZMod 2) (kb kc : ZMod 2)
    (hfb : ∀ u v, fb u v = Ab u + Bb v) (hgb : ∀ x y, gb x y = LA R Ab x + LB Cc Bb y + kb)
    (hfc : ∀ u v, fc u v = Ac u + Bc v) (hgc : ∀ x y, gc x y = LA R Ac x + LB Cc Bc y + kc) :
    ∃ (A' : Fin n' → ZMod 2) (B' : Fin m' → ZMod 2), ∀ x y,
      Pz R Cc (fun u v => c0 + c1 * fb u v + c2 * fc u v + 1 * (fb u v * fc u v)) x y +
        (c0 + c1 * gb x y + c2 * gc x y + 1 * (gb x y * gc x y)) = A' x + B' y := by
  refine ⟨fun x => c0 * (ρ * σ) + c0 + c1 * (σ * LA R Ab x + LA R Ab x + kb) +
      c2 * (σ * LA R Ac x + LA R Ac x + kc) + σ * LA R (fun i => Ab i * Ac i) x +
      LA R Ab x * LA R Ac x + kc * LA R Ab x + kb * LA R Ac x + kb * kc,
    fun y => c1 * (ρ * LB Cc Bb y + LB Cc Bb y) + c2 * (ρ * LB Cc Bc y + LB Cc Bc y) +
      ρ * LB Cc (fun j => Bb j * Bc j) y + LB Cc Bb y * LB Cc Bc y + kc * LB Cc Bb y +
      kb * LB Cc Bc y, fun x y => ?_⟩
  have efb : fb = fun u v => Ab u + Bb v := funext fun u => funext fun v => hfb u v
  have efc : fc = fun u v => Ac u + Bc v := funext fun u => funext fun v => hfc u v
  rw [Pz_lin]
  subst efb efc
  beta_reduce
  rw [Pz_aff, Pz_aff, Pz_prod, hgb, hgc, hρ, hσ]
  ring_nf
  simp only [two0, mul_zero, zero_mul, add_zero, zero_add]

end Alg

def indA (n : ℕ) (a : ℕ) : Fin n → ZMod 2 := fun i => if i.val = a then 1 else 0
def indB (n m : ℕ) (a : ℕ) : Fin m → ZMod 2 := fun j => if n + j.val = a then 1 else 0

def liftBlk (n m n' m' : ℕ) (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m)) (a : ℕ) :
    List Gate :=
  chain (n' + m' + a * (2 * (n' + m') + 1))
    (mask (n' + m') (n' + m' + a * (2 * (n' + m') + 1)) (nu (LA R (indA n a)) (LB Cc (indB n m a))))

theorem liftBlk_len (n m n' m' : ℕ) (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m)) (a : ℕ) :
    (liftBlk n m n' m' R Cc a).length = 2 * (n' + m') + 1 := by
  simp [liftBlk, chain_len, mask_len]

def phi (K N : ℕ) (a : ℕ) : ℕ := if a < K then N + a * (2 * N + 1) + 2 * N else N + K * (2 * N + 1) + (a - K)

def simG (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

def baseC (n m n' m' : ℕ) (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m)) (gs : List Gate) :
    List Gate :=
  blocks (liftBlk n m n' m' R Cc) (n + m) ++ gs.map (simG (phi (n + m) (n' + m')))

section Simu

variable {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m)) (gs : List Gate)

theorem lift_core {α : Type} (d : α) (H : Gate → List α → α) (W : List α) (hW : W.length = n' + m')
    (a : ℕ) (ha : a < n + m) :
    (Fo d H W (baseC n m n' m' R Cc gs)).getD (phi (n + m) (n' + m') a) d =
      (Fo d H (Fo d H W (blocks (liftBlk n m n' m' R Cc) a)) (liftBlk n m n' m' R Cc a)).getD
        (n' + m' + a * (2 * (n' + m') + 1) + 2 * (n' + m')) d := by
  have hb := liftBlk_len n m n' m' R Cc
  unfold baseC; rw [Fo_append]
  have hph : phi (n + m) (n' + m') a = n' + m' + a * (2 * (n' + m') + 1) + 2 * (n' + m') := by
    simp [phi, ha]
  rw [hph, Fo_pre _ _ _ _ _ (by
    rw [blocks_Fo_len _ _ _ _ hb, hW]
    have : (a + 1) * (2 * (n' + m') + 1) ≤ (n + m) * (2 * (n' + m') + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith)]
  have := blocks_out d H (liftBlk n m n' m' R Cc) _ hb W (2 * (n' + m')) (by omega) (n + m) a ha
  rw [hW] at this; exact this

theorem lift_val (a : ℕ) (ha : a < n + m) (x : Fin n') (y : Fin m') :
    V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') a) x y =
      LA R (indA n a) x + LB Cc (indB n m a) y := by
  unfold V
  rw [lift_core R Cc gs false ev (oneEach x y) (oneEach_len x y) a ha]
  have hlj := blocks_Fo_len false ev (liftBlk n m n' m' R Cc) _ (liftBlk_len n m n' m' R Cc)
    (oneEach x y) a
  rw [oneEach_len] at hlj
  have := chain_val _ (mask (n' + m') (n' + m' + a * (2 * (n' + m') + 1))
    (nu (LA R (indA n a)) (LB Cc (indB n m a)))) _ hlj (mask_le _ _ _ (by omega))
  rw [mask_len] at this
  rw [show liftBlk n m n' m' R Cc a = chain (n' + m' + a * (2 * (n' + m') + 1))
    (mask (n' + m') (n' + m' + a * (2 * (n' + m') + 1)) (nu (LA R (indA n a)) (LB Cc (indB n m a))))
    from rfl]
  rw [this, mask_sum _ _ _ _ (by rw [← hlj, app1_last]; rfl)]
  have e1 : ∀ i ∈ Finset.range (n' + m'), nu (LA R (indA n a)) (LB Cc (indB n m a)) i *
      z ((Fo false ev (oneEach x y) (blocks (liftBlk n m n' m' R Cc) a) ++ [false]).getD i false) =
      nu (LA R (indA n a)) (LB Cc (indB n m a)) i * z ((oneEach x y).getD i false) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [List.getD_append _ _ _ _ (by rw [hlj]; omega), Fo_pre _ _ _ _ _ (by rw [oneEach_len]; omega)]
  rw [Finset.sum_congr rfl e1, onehot_sum, nu_l, nu_r]

theorem lift_dep (a : ℕ) (ha : a < n + m) :
    Dp (n' + m') (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') a) = 0 := by
  unfold Dp
  rw [lift_core R Cc gs 0 Hd (List.replicate (n' + m') 0) (by simp) a ha]
  have hlj := blocks_Fo_len 0 Hd (liftBlk n m n' m' R Cc) _ (liftBlk_len n m n' m' R Cc)
    (List.replicate (n' + m') 0) a
  simp only [List.length_replicate] at hlj
  have := chain_dep _ (mask (n' + m') (n' + m' + a * (2 * (n' + m') + 1))
    (nu (LA R (indA n a)) (LB Cc (indB n m a)))) _ 0 hlj (mask_le _ _ _ (by omega))
  rw [mask_len] at this
  apply Nat.le_zero.mp
  apply this
  intro w hw hwp
  simp only [mask, List.mem_map, List.mem_range] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  split_ifs at hwp ⊢
  · rw [Fo_pre _ _ _ _ _ (by simp; omega)]; simp [hi]
  · omega

theorem wireN_core {α : Type} (d dv : α) (H : Gate → List α → α) (hG0 : H G0 [] = dv) (W : List α)
    (hW : W.length = n' + m') (hK : 0 < n + m) :
    (Fo d H W (baseC n m n' m' R Cc gs)).getD (n' + m') d = dv := by
  have hb := liftBlk_len n m n' m' R Cc
  unfold baseC; rw [Fo_append]
  rw [Fo_pre _ _ _ _ _ (by
    rw [blocks_Fo_len _ _ _ _ hb, hW]
    have : 1 * (2 * (n' + m') + 1) ≤ (n + m) * (2 * (n' + m') + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith)]
  have := blocks_out d H (liftBlk n m n' m' R Cc) _ hb W 0 (by omega) (n + m) 0 hK
  simp only [zero_mul, add_zero, hW] at this
  rw [this]
  simp only [blocks, Fo_nil]
  unfold liftBlk chain
  rw [Fo_cons, Fo_pre _ _ _ _ _ (by simp [hW]), ← hW, app1_last]
  exact hG0

theorem wireN_val (hK : 0 < n + m) (x : Fin n') (y : Fin m') :
    V (baseC n m n' m' R Cc gs) (n' + m') x y = 0 := by
  unfold V; rw [wireN_core R Cc gs false false ev rfl (oneEach x y) (oneEach_len x y) hK]; rfl

theorem wireN_dep (hK : 0 < n + m) : Dp (n' + m') (baseC n m n' m' R Cc gs) (n' + m') = 0 :=
  wireN_core R Cc gs 0 0 Hd rfl _ (by simp) hK

theorem simG_nl (φ : ℕ → ℕ) (g : Gate) : nl (simG φ g) = nl g := by simp [nl, simG]

theorem old_core {α : Type} (d : α) (H : Gate → List α → α) (W : List α) (hW : W.length = n + m)
    (hrb : RB (n + m) gs) (k : ℕ) (hk : k < gs.length) :
    (Fo d H W gs).getD (n + m + k) d =
      H (gs.getD k G0) ((gs.getD k G0).inputs.map fun i => (Fo d H W gs).getD i d) := by
  have := Fo_gate d H gs W k hk (by rw [hW]; exact hrb k hk)
  rw [hW] at this; exact this

theorem phi_lt (hrb : RB (n + m) gs) (k : ℕ) (hk : k < gs.length) (i : ℕ) (hi : i ∈ (gs.getD k G0).inputs) :
    phi (n + m) (n' + m') i < n' + m' + (n + m) * (2 * (n' + m') + 1) + k := by
  have := hrb k hk i hi
  unfold phi
  split_ifs with h
  · have : (i + 1) * (2 * (n' + m') + 1) ≤ (n + m) * (2 * (n' + m') + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · omega

theorem new_core {α : Type} (d : α) (H : Gate → List α → α) (hH : ∀ g l, H (simG (phi (n + m) (n' + m')) g) l = H g l)
    (W : List α) (hW : W.length = n' + m')
    (hrb : RB (n + m) gs) (k : ℕ) (hk : k < gs.length) :
    (Fo d H W (baseC n m n' m' R Cc gs)).getD (phi (n + m) (n' + m') (n + m + k)) d =
      H (gs.getD k G0) ((gs.getD k G0).inputs.map fun i =>
        (Fo d H W (baseC n m n' m' R Cc gs)).getD (phi (n + m) (n' + m') i) d) := by
  have hb := liftBlk_len n m n' m' R Cc
  unfold baseC; rw [Fo_append]
  have hl1 : (Fo d H W (blocks (liftBlk n m n' m' R Cc) (n + m))).length =
      n' + m' + (n + m) * (2 * (n' + m') + 1) := by rw [blocks_Fo_len _ _ _ _ hb, hW]
  have hph : phi (n + m) (n' + m') (n + m + k) = n' + m' + (n + m) * (2 * (n' + m') + 1) + k := by
    simp [phi]
  have hgk : (gs.map (simG (phi (n + m) (n' + m')))).getD k G0 = simG (phi (n + m) (n' + m')) (gs.getD k G0) := by
    simp [List.getD_eq_getElem, hk]
  have := Fo_gate d H (gs.map (simG (phi (n + m) (n' + m'))))
    (Fo d H W (blocks (liftBlk n m n' m' R Cc) (n + m))) k (by simp [hk]) (by
      rw [hgk, hl1]; intro i hi
      simp only [simG, List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact phi_lt gs hrb k hk j hj)
  rw [hl1, hgk, hH] at this
  rw [hph, this]
  simp only [simG, List.map_map]
  rfl

end Simu

section Inv

variable {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m))
  (ρ σ : ZMod 2) (hρ : ∀ x, ((R x).card : ZMod 2) = ρ) (hσ : ∀ y, ((Cc y).card : ZMod 2) = σ)
  (gs : List Gate) (hrb : RB (n + m) gs) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
include hρ hσ hrb hfan

theorem Vold (k : ℕ) (hk : k < gs.length) (u : Fin n) (v : Fin m) :
    V gs (n + m + k) u v = z ((gs.getD k G0).op.eval ((gs.getD k G0).inputs.map fun i =>
      (Fo false ev (oneEach u v) gs).getD i false)) := by
  unfold V; rw [old_core gs false ev (oneEach u v) (oneEach_len u v) hrb k hk]; rfl

theorem Vnew (k : ℕ) (hk : k < gs.length) (x : Fin n') (y : Fin m') :
    V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') (n + m + k)) x y =
      z ((gs.getD k G0).op.eval ((gs.getD k G0).inputs.map fun i =>
      (Fo false ev (oneEach x y) (baseC n m n' m' R Cc gs)).getD (phi (n + m) (n' + m') i) false)) := by
  unfold V
  rw [new_core R Cc gs false ev (fun g l => rfl) (oneEach x y) (oneEach_len x y) hrb k hk]; rfl

theorem invariant : ∀ a, a < n + m + gs.length →
    Dp (n' + m') (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') a) = Dp (n + m) gs a ∧
    (Dp (n + m) gs a = 0 → ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (k : ZMod 2),
      (∀ u v, V gs a u v = A u + B v) ∧
      ∀ x y, V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') a) x y = LA R A x + LB Cc B y + k) ∧
    (Dp (n + m) gs a ≤ 1 → ∃ (A' : Fin n' → ZMod 2) (B' : Fin m' → ZMod 2), ∀ x y,
      Pz R Cc (V gs a) x y + V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') a) x y = A' x + B' y) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha
  by_cases hin : a < n + m
  · have hD0 : Dp (n + m) gs a = 0 := by
      unfold Dp; rw [Fo_pre _ _ _ _ _ (by simp; omega)]; simp [hin]
    have hI0 : ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (k : ZMod 2),
        (∀ u v, V gs a u v = A u + B v) ∧
        ∀ x y, V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') a) x y = LA R A x + LB Cc B y + k := by
      refine ⟨indA n a, indB n m a, 0, fun u v => ?_, fun x y => ?_⟩
      · unfold V; rw [Fo_pre _ _ _ _ _ (by rw [oneEach_len]; omega), onehot]
        simp only [indA, indB, eq_comm]
      · rw [lift_val R Cc gs a hin, add_zero]
    refine ⟨by rw [lift_dep R Cc gs a hin, hD0], fun _ => hI0, fun _ => ?_⟩
    obtain ⟨A, B, k, h1, h2⟩ := hI0
    exact I0_I1 R Cc ρ σ hρ hσ _ _ A B k h1 h2
  · obtain ⟨k, rfl⟩ : ∃ k, a = n + m + k := ⟨a - (n + m), by omega⟩
    have hk : k < gs.length := by omega
    set g := gs.getD k G0 with hg
    have hmem : g ∈ gs := by rw [hg, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hlen := hfan g hmem
    have hlt : ∀ i ∈ g.inputs, i < n + m + k := fun i hi => by
      have := hrb k hk i hi; omega
    have hDo : Dp (n + m) gs (n + m + k) = Hd g (g.inputs.map fun i => Dp (n + m) gs i) := by
      unfold Dp; rw [old_core gs 0 Hd _ (by simp) hrb k hk]
    have hDn : Dp (n' + m') (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') (n + m + k)) =
        Hd g (g.inputs.map fun i => Dp (n' + m') (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') i)) := by
      unfold Dp
      rw [new_core R Cc gs 0 Hd (fun g l => by simp only [Hd, simG_nl]) _ (by simp) hrb k hk]
    have hVo := Vold R Cc ρ σ hρ hσ gs hrb hfan k hk
    have hVn := Vnew R Cc ρ σ hρ hσ gs hrb hfan k hk
    rw [← hg] at hVo hVn
    rcases hl : g.inputs with _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
    ·
      have hnl : nl g = false := by simp [nl, hl]
      rw [hl] at hVo hVn hDo hDn
      simp only [List.map_nil, Hd, hnl, List.foldr_nil, Bool.toNat_false, add_zero] at hVo hVn hDo hDn
      have hI0 : ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (k' : ZMod 2),
          (∀ u v, V gs (n + m + k) u v = A u + B v) ∧
          ∀ x y, V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') (n + m + k)) x y =
            LA R A x + LB Cc B y + k' := by
        refine ⟨fun _ => z (g.op.eval []), fun _ => 0, z (g.op.eval []) + z (g.op.eval []) * ρ,
          fun u v => ?_, fun x y => ?_⟩
        · rw [hVo]; ring
        · rw [hVn]
          simp only [LA, LB, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero, hρ]
          ring_nf
          simp only [two0, mul_zero, zero_mul, add_zero, zero_add]
      refine ⟨by rw [hDo, hDn], fun _ => hI0, fun _ => ?_⟩
      obtain ⟨A, B, k', h1, h2⟩ := hI0
      exact I0_I1 R Cc ρ σ hρ hσ _ _ A B k' h1 h2
    ·
      have hnl : nl g = false := by simp [nl, hl]
      have hb : b < n + m + k := hlt b (by simp [hl])
      obtain ⟨ihD, ihI0, ihI1⟩ := ih b hb (by omega)
      rw [hl] at hVo hVn hDo hDn
      simp only [List.map_cons, List.map_nil, Hd, hnl, List.foldr_cons, List.foldr_nil,
        Bool.toNat_false, add_zero, Nat.max_zero] at hVo hVn hDo hDn
      have eo : ∀ (u : Fin n) (v : Fin m), V gs (n + m + k) u v =
          z (g.op.eval [false]) + (z (g.op.eval [false]) + z (g.op.eval [true])) * V gs b u v +
            0 * V gs b u v := by
        intro u v; rw [hVo u v, ev1]; unfold V; ring
      have en : ∀ (x : Fin n') (y : Fin m'), V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') (n + m + k)) x y =
          z (g.op.eval [false]) + (z (g.op.eval [false]) + z (g.op.eval [true])) *
            V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') b) x y +
            0 * V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') b) x y := by
        intro x y; rw [hVn x y, ev1]; unfold V; ring
      refine ⟨by rw [hDo, hDn, ihD], fun h0 => ?_, fun h1 => ?_⟩
      · rw [hDo] at h0
        obtain ⟨A, B, k', h1, h2⟩ := ihI0 h0
        obtain ⟨A2, B2, k2, h3, h4⟩ := lin_I0 R Cc ρ σ hρ hσ _ _ 0 _ _ _ _ A A B B k' k' h1 h2 h1 h2
        exact ⟨A2, B2, k2, fun u v => by rw [eo]; exact h3 u v, fun x y => by rw [en]; exact h4 x y⟩
      · rw [hDo] at h1
        obtain ⟨A, B, h2⟩ := ihI1 h1
        obtain ⟨A2, B2, h3⟩ := lin_I1 R Cc ρ σ hρ hσ _ _ 0 _ _ _ _ A A B B h2 h2
        refine ⟨A2, B2, fun x y => ?_⟩
        have : (V gs (n + m + k) : Fin n → Fin m → ZMod 2) = fun u v => z (g.op.eval [false]) +
            (z (g.op.eval [false]) + z (g.op.eval [true])) * V gs b u v + 0 * V gs b u v :=
          funext fun u => funext fun v => eo u v
        rw [this, en]; exact h3 x y
    ·
      have hb : b < n + m + k := hlt b (by simp [hl])
      have hc : c < n + m + k := hlt c (by simp [hl])
      obtain ⟨ihDb, ihI0b, ihI1b⟩ := ih b hb (by omega)
      obtain ⟨ihDc, ihI0c, ihI1c⟩ := ih c hc (by omega)
      have hκ := nl_two g (by rw [hl]; rfl)
      rw [hl] at hVo hVn hDo hDn
      simp only [List.map_cons, List.map_nil, Hd, List.foldr_cons, List.foldr_nil,
        Nat.max_zero] at hVo hVn hDo hDn
      have eo : ∀ (u : Fin n) (v : Fin m), V gs (n + m + k) u v =
          z (g.op.eval [false, false]) + (z (g.op.eval [false, false]) + z (g.op.eval [true, false])) * V gs b u v +
            (z (g.op.eval [false, false]) + z (g.op.eval [false, true])) * V gs c u v +
            z (nl g) * (V gs b u v * V gs c u v) := by
        intro u v; rw [hVo u v, ev2, hκ]; unfold V; ring
      have en : ∀ (x : Fin n') (y : Fin m'), V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') (n + m + k)) x y =
          z (g.op.eval [false, false]) + (z (g.op.eval [false, false]) + z (g.op.eval [true, false])) *
            V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') b) x y +
            (z (g.op.eval [false, false]) + z (g.op.eval [false, true])) *
            V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') c) x y +
            z (nl g) * (V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') b) x y *
              V (baseC n m n' m' R Cc gs) (phi (n + m) (n' + m') c) x y) := by
        intro x y; rw [hVn x y, ev2, hκ]; unfold V; ring
      refine ⟨by rw [hDo, hDn, ihDb, ihDc], ?_, ?_⟩
      · intro h0
        rw [hDo] at h0
        cases hnl : nl g with
        | true => simp [hnl] at h0
        | false =>
          simp only [hnl, Bool.toNat_false, add_zero] at h0
          obtain ⟨Ab, Bb, kb, h1, h2⟩ := ihI0b (by omega)
          obtain ⟨Ac, Bc, kc, h3, h4⟩ := ihI0c (by omega)
          obtain ⟨A2, B2, k2, h5, h6⟩ := lin_I0 R Cc ρ σ hρ hσ _ _ _ _ _ _ _ Ab Ac Bb Bc kb kc h1 h2 h3 h4
          refine ⟨A2, B2, k2, fun u v => ?_, fun x y => ?_⟩
          · rw [eo, hnl]; simp only [z_false, zero_mul, add_zero]; exact h5 u v
          · rw [en, hnl]; simp only [z_false, zero_mul, add_zero]; exact h6 x y
      · intro h1
        rw [hDo] at h1
        cases hnl : nl g with
        | false =>
          simp only [hnl, Bool.toNat_false, add_zero] at h1
          obtain ⟨Ab, Bb, h2⟩ := ihI1b (by omega)
          obtain ⟨Ac, Bc, h3⟩ := ihI1c (by omega)
          obtain ⟨A2, B2, h4⟩ := lin_I1 R Cc ρ σ hρ hσ _ _ _ _ _ _ _ Ab Ac Bb Bc h2 h3
          refine ⟨A2, B2, fun x y => ?_⟩
          have : (V gs (n + m + k) : Fin n → Fin m → ZMod 2) = fun u v => z (g.op.eval [false, false]) +
              (z (g.op.eval [false, false]) + z (g.op.eval [true, false])) * V gs b u v +
              (z (g.op.eval [false, false]) + z (g.op.eval [false, true])) * V gs c u v := by
            funext u v; rw [eo, hnl]; simp only [z_false, zero_mul, add_zero]
          rw [this, en, hnl]; simp only [z_false, zero_mul, add_zero]; exact h4 x y
        | true =>
          simp only [hnl, Bool.toNat_true] at h1
          obtain ⟨Ab, Bb, kb, h2, h3⟩ := ihI0b (by omega)
          obtain ⟨Ac, Bc, kc, h4, h5⟩ := ihI0c (by omega)
          obtain ⟨A2, B2, h6⟩ := prod_I1 R Cc ρ σ hρ hσ _ _ _ _ _ _ _ Ab Ac Bb Bc kb kc h2 h3 h4 h5
          refine ⟨A2, B2, fun x y => ?_⟩
          have : (V gs (n + m + k) : Fin n → Fin m → ZMod 2) = fun u v => z (g.op.eval [false, false]) +
              (z (g.op.eval [false, false]) + z (g.op.eval [true, false])) * V gs b u v +
              (z (g.op.eval [false, false]) + z (g.op.eval [false, true])) * V gs c u v +
              1 * (V gs b u v * V gs c u v) := by
            funext u v; rw [eo, hnl]; rfl
          rw [this, en, hnl]; exact h6 x y
    · have : g.inputs.length ≥ 3 := by rw [hl]; simp
      omega

end Inv

def pullB {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m))
    (G : Fin n → Fin m → Bool) (x : Fin n') (y : Fin m') : Bool :=
  (((R x).sum (fun i => ((Cc y).filter (fun j => G i j)).card)) % 2) == 1

theorem z_mod (N : ℕ) : z ((N % 2) == 1) = (N : ZMod 2) := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · rw [h]
    have : (N : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even]; exact Nat.even_iff.mpr h
    rw [this]; rfl
  · rw [h]
    have : (N : ZMod 2) = 1 := by
      rw [ZMod.natCast_eq_iff]; refine ⟨N / 2, ?_⟩; simp [ZMod.val_one]; omega
    rw [this]; rfl

theorem z_pull {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m))
    (G : Fin n → Fin m → Bool) (x : Fin n') (y : Fin m') :
    z (pullB R Cc G x y) = Pz R Cc (fun u v => z (G u v)) x y := by
  unfold pullB Pz
  rw [z_mod, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold z; split_ifs <;> simp_all

theorem V_beyond {n m : ℕ} (gs : List Gate) (a : ℕ) (ha : n + m + gs.length ≤ a) (u : Fin n) (v : Fin m) :
    V gs a u v = 0 := by
  unfold V
  rw [List.getD_eq_default _ _ (by rw [Fo_len, oneEach_len]; omega)]; rfl

theorem base_props {n m n' m' : ℕ} (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m))
    (gs : List Gate) (hrb : RB (n + m) gs) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    RB (n' + m') (baseC n m n' m' R Cc gs) ∧ (∀ g ∈ baseC n m n' m' R Cc gs, g.inputs.length ≤ 2) ∧
    (baseC n m n' m' R Cc gs).countP nl = gs.countP nl ∧
    (baseC n m n' m' R Cc gs).length = (n + m) * (2 * (n' + m') + 1) + gs.length := by
  have hb := liftBlk_len n m n' m' R Cc
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold baseC
    apply RB_append
    · apply blocks_RB _ _ _ hb
      intro a
      exact RB_chain _ _ (mask_le _ _ _ (by omega))
    · rw [blocks_len _ _ hb]
      intro k hk i hi
      simp only [List.length_map] at hk
      have hgk : (gs.map (simG (phi (n + m) (n' + m')))).getD k G0 = simG (phi (n + m) (n' + m')) (gs.getD k G0) := by
        simp [List.getD_eq_getElem, hk]
      rw [hgk] at hi
      simp only [simG, List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact phi_lt gs hrb k hk j hj
  · intro g hg
    unfold baseC at hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact (blocks_mem _ (fun g => g.inputs.length ≤ 2 ∧ nl g = false)
        (fun a g hg => chain_gates _ _ g (by unfold liftBlk at hg; exact hg)) _ g hg).1
    · simp only [simG, List.length_map]; exact hfan g' hg'
  · unfold baseC
    rw [List.countP_append, blocks_countP _ (fun a g hg => (chain_gates _ _ g (by unfold liftBlk at hg; exact hg)).2),
      List.countP_map]
    simp only [zero_add]
    congr 1
    funext g; simp [Function.comp, simG_nl]
  · simp [baseC, blocks_len _ _ hb]

theorem neg_self2 (c : ZMod 2) : -c = c := by fin_cases c <;> rfl

theorem suffP {n m n' m' : ℕ} (hn' : 0 < n') (hK : 0 < n + m) (R : Fin n' → Finset (Fin n))
    (Cc : Fin m' → Finset (Fin m)) (ρ σ : ZMod 2) (hρ : ∀ x, ((R x).card : ZMod 2) = ρ)
    (hσ : ∀ y, ((Cc y).card : ZMod 2) = σ) (q s : ℕ) (T : Fin q → Fin n → Fin m → Bool)
    (h : Fits n m q T s) : Fits n' m' q (fun j => pullB R Cc (T j)) s := by
  obtain ⟨C, tap, hrb, hfan, hcnt, htap⟩ := h
  have hrb' : RB (n + m) C.gates := hrb
  obtain ⟨bRB, bfan, bcnt, blen⟩ := base_props R Cc C.gates hrb' hfan
  have inv := invariant R Cc ρ σ hρ hσ C.gates hrb' hfan
  have key : ∀ j : Fin q, ∃ (ψj : ℕ) (A' : Fin n' → ZMod 2) (B' : Fin m' → ZMod 2),
      ψj < n' + m' + (baseC n m n' m' R Cc C.gates).length ∧
      Dp (n' + m') (baseC n m n' m' R Cc C.gates) ψj ≤ 1 ∧
      ∀ x y, z (pullB R Cc (T j) x y) = A' x + B' y + V (baseC n m n' m' R Cc C.gates) ψj x y := by
    intro j
    have hT : ∀ u v, V C.gates (tap j) u v = z (T j u v) := by
      intro u v; unfold V; rw [show (Fo false ev (oneEach u v) C.gates).getD (tap j) false = T j u v
        from (htap j).2 u v]
    by_cases hr : tap j < n + m + C.gates.length
    · obtain ⟨hD, -, hI1⟩ := inv (tap j) hr
      obtain ⟨A', B', hAB⟩ := hI1 (htap j).1
      refine ⟨phi (n + m) (n' + m') (tap j), A', B', ?_, ?_, fun x y => ?_⟩
      · rw [blen]; unfold phi; split_ifs with h1
        · have : (tap j + 1) * (2 * (n' + m') + 1) ≤ (n + m) * (2 * (n' + m') + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          nlinarith
        · omega
      · rw [hD]; exact (htap j).1
      · rw [z_pull]
        have e : (fun u v => z (T j u v)) = V C.gates (tap j) := funext fun u => funext fun v => (hT u v).symm
        rw [e]
        have := hAB x y
        rw [← sub_eq_iff_eq_add, sub_eq_add_neg, neg_self2]
        linear_combination this
    · refine ⟨n' + m', 0, 0, ?_, ?_, fun x y => ?_⟩
      · rw [blen]; have : 1 * (2 * (n' + m') + 1) ≤ (n + m) * (2 * (n' + m') + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
      · rw [wireN_dep R Cc C.gates hK]; omega
      · rw [z_pull, wireN_val R Cc C.gates hK]
        have e : (fun u v => z (T j u v)) = fun _ _ => 0 := funext fun u => funext fun v => by
          rw [← hT u v]; exact V_beyond _ _ (by omega) u v
        rw [e]; simp [Pz]
  choose ψ A' B' hψ hD hval using key
  exact tapsFit n' m' q s hn' _ bRB bfan (by rw [bcnt]; exact hcnt) ψ hψ hD A' B' _ hval

theorem G0_props (n' m' : ℕ) : RB (n' + m') [G0] ∧ (∀ g ∈ [G0], g.inputs.length ≤ 2) ∧ [G0].countP nl = 0 ∧
    Dp (n' + m') [G0] (n' + m') ≤ 1 ∧ ∀ {n m : ℕ} (hn : n + m = n' + m') (x : Fin n) (y : Fin m), V [G0] (n' + m') x y = 0 := by
  refine ⟨RB_cons _ _ _ (by simp [G0]) (RB_nil _), by simp [G0], rfl, ?_, ?_⟩
  · unfold Dp; rw [Fo_cons]; simp only [Fo_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]; simp [Hd, G0, nl]
  · intro n m hn x y; unfold V; rw [Fo_cons]; simp only [Fo_nil]
    rw [List.getD_append_right _ _ _ _ (by rw [oneEach_len]; omega), oneEach_len, hn, Nat.sub_self]; rfl

theorem suffConst {n m n' m' : ℕ} (hn' : 0 < n') (hm' : 0 < m') (R : Fin n' → Finset (Fin n))
    (Cc : Fin m' → Finset (Fin m)) (hc : (∀ x x', R x = R x') ∨ (∀ y y', Cc y = Cc y'))
    (q s : ℕ) (T : Fin q → Fin n → Fin m → Bool) : Fits n' m' q (fun j => pullB R Cc (T j)) s := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := G0_props n' m'
  rcases hc with hR | hC
  · apply tapsFit n' m' q s hn' [G0] g1 g2 (by rw [g3]; omega) (fun _ => n' + m') (fun _ => by simp)
      (fun _ => g4) (fun _ _ => 0) (fun j y => Pz R Cc (fun u v => z (T j u v)) ⟨0, hn'⟩ y)
    intro j x y
    rw [z_pull, g5 rfl]
    simp only [Pz, hR x ⟨0, hn'⟩]; ring
  · apply tapsFit n' m' q s hn' [G0] g1 g2 (by rw [g3]; omega) (fun _ => n' + m') (fun _ => by simp)
      (fun _ => g4) (fun j x => Pz R Cc (fun u v => z (T j u v)) x ⟨0, hm'⟩) (fun _ _ => 0)
    intro j x y
    rw [z_pull, g5 rfl]
    simp only [Pz, hC y ⟨0, hm'⟩]; ring

theorem four0 : (4 : ZMod 2) = 0 := rfl

theorem fourpt {n' m' : ℕ} (gs : List Gate) (hrb : RB (n' + m') gs) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hnl : ∀ g ∈ gs, nl g = false) (x1 x2 : Fin n') (y1 y2 : Fin m') :
    ∀ a, V gs a x1 y1 + V gs a x1 y2 + V gs a x2 y1 + V gs a x2 y2 = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  by_cases hin : a < n' + m'
  · have hp : ∀ (x : Fin n') (y : Fin m'), V gs a x y = z ((oneEach x y).getD a false) := fun x y => by
      unfold V; rw [Fo_pre _ _ _ _ _ (by rw [oneEach_len]; exact hin)]
    rw [hp, hp, hp, hp, onehot, onehot, onehot, onehot]
    ring_nf
    simp only [two0, four0, mul_zero, zero_mul, add_zero, zero_add]
  by_cases hr : a < n' + m' + gs.length
  · obtain ⟨k, rfl⟩ : ∃ k, a = n' + m' + k := ⟨a - (n' + m'), by omega⟩
    have hk : k < gs.length := by omega
    set g := gs.getD k G0 with hg
    have hmem : g ∈ gs := by rw [hg, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hlen := hfan g hmem
    have hlt : ∀ i ∈ g.inputs, i < n' + m' + k := fun i hi => by
      have := hrb k hk i hi; omega
    have hV : ∀ (x : Fin n') (y : Fin m'), V gs (n' + m' + k) x y =
        z (g.op.eval (g.inputs.map fun i => (Fo false ev (oneEach x y) gs).getD i false)) := by
      intro x y; unfold V; rw [old_core gs false ev (oneEach x y) (oneEach_len x y) hrb k hk]; rfl
    simp only [hV]
    rcases hl : g.inputs with _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
    · simp only [List.map_nil]
      ring_nf
      simp only [four0, mul_zero]
    · have h1 : ∀ (x : Fin n') (y : Fin m'), z (g.op.eval ([b].map fun i => (Fo false ev (oneEach x y) gs).getD i false)) =
          z (g.op.eval [false]) + (z (g.op.eval [false]) + z (g.op.eval [true])) * V gs b x y :=
        fun x y => ev1 g.op.eval _
      rw [h1, h1, h1, h1]
      have hb := ih b (hlt b (by simp [hl]))
      linear_combination (z (g.op.eval [false]) + z (g.op.eval [true])) * hb +
        (2 * z (g.op.eval [false])) * two0
    · have hκ := nl_two g (by rw [hl]; rfl)
      rw [hnl g hmem, z_false] at hκ
      have h2 : ∀ (x : Fin n') (y : Fin m'), z (g.op.eval ([b, c].map fun i => (Fo false ev (oneEach x y) gs).getD i false)) =
          z (g.op.eval [false, false]) + (z (g.op.eval [false, false]) + z (g.op.eval [true, false])) * V gs b x y +
          (z (g.op.eval [false, false]) + z (g.op.eval [false, true])) * V gs c x y := by
        intro x y
        have := ev2 g.op.eval ((Fo false ev (oneEach x y) gs).getD b false) ((Fo false ev (oneEach x y) gs).getD c false)
        rw [← hκ, zero_mul, zero_mul, add_zero] at this
        exact this
      rw [h2, h2, h2, h2]
      have hb := ih b (hlt b (by simp [hl]))
      have hc := ih c (hlt c (by simp [hl]))
      linear_combination (z (g.op.eval [false, false]) + z (g.op.eval [true, false])) * hb +
        (z (g.op.eval [false, false]) + z (g.op.eval [false, true])) * hc +
        (2 * z (g.op.eval [false, false])) * two0
    · have : g.inputs.length ≥ 3 := by rw [hl]; simp
      omega
  · simp only [V_beyond (n := n') (m := m') gs a (by omega)]; ring

theorem pair_one (a b : ℕ) (h : a % 2 ≠ b % 2) : (a : ZMod 2) + (b : ZMod 2) = 1 := by
  have h' : (a : ZMod 2) ≠ (b : ZMod 2) := by
    rw [Ne, ZMod.natCast_eq_natCast_iff']; exact h
  generalize (a : ZMod 2) = p at h'
  generalize (b : ZMod 2) = r at h'
  fin_cases p <;> fin_cases r <;> first | rfl | exact absurd rfl h'

theorem mem_one {α : Type} [DecidableEq α] (s t : Finset α) (j : α) (h : ¬(j ∈ s ↔ j ∈ t)) :
    ((if j ∈ s then 1 else 0 : ZMod 2) + (if j ∈ t then 1 else 0 : ZMod 2)) = 1 := by
  by_cases h1 : j ∈ s <;> by_cases h2 : j ∈ t <;> simp_all <;> rfl

theorem nec {n m n' m' : ℕ} (hn : 0 < n) (hm : 0 < m) (R : Fin n' → Finset (Fin n))
    (Cc : Fin m' → Finset (Fin m))
    (P : ∀ (g s : ℕ) (T : Fin g → Fin n → Fin m → Bool), Fits n m g T s →
      Fits n' m' g (fun i => pullB R Cc (T i)) s) :
    (∀ x x', R x = R x') ∨ (∀ y y', Cc y = Cc y') ∨
      ((∀ x x', (R x).card % 2 = (R x').card % 2) ∧ (∀ y y', (Cc y).card % 2 = (Cc y').card % 2)) := by
  by_cases hA : ∀ x x', R x = R x'
  · exact Or.inl hA
  by_cases hB : ∀ y y', Cc y = Cc y'
  · exact Or.inr (Or.inl hB)
  right; right
  obtain ⟨g1, g2, g3, g4, g5⟩ := G0_props n m
  have run : ∀ (T : Fin 1 → Fin n → Fin m → Bool), Fits n m 1 T 0 →
      ∀ x1 x2 y1 y2, Pz R Cc (fun u v => z (T 0 u v)) x1 y1 + Pz R Cc (fun u v => z (T 0 u v)) x1 y2 +
        Pz R Cc (fun u v => z (T 0 u v)) x2 y1 + Pz R Cc (fun u v => z (T 0 u v)) x2 y2 = 0 := by
    intro T hT x1 x2 y1 y2
    obtain ⟨C2, tap, hrb, hfan, hcnt, htap⟩ := P 1 0 T hT
    have hnl : ∀ g ∈ C2.gates, nl g = false := by
      have : C2.gates.countP nl = 0 := by omega
      rw [List.countP_eq_zero] at this
      intro g hg; simpa using this g hg
    have fp := fourpt C2.gates hrb hfan hnl x1 x2 y1 y2 (tap 0)
    have hv : ∀ x y, V C2.gates (tap 0) x y = Pz R Cc (fun u v => z (T 0 u v)) x y := by
      intro x y; rw [← z_pull]; unfold V
      rw [show (Fo false ev (oneEach x y) C2.gates).getD (tap 0) false = pullB R Cc (T 0) x y
        from (htap 0).2 x y]
    simpa only [hv] using fp
  constructor
  · intro x1 x2
    by_contra hpar
    simp only [not_forall] at hB
    obtain ⟨y1, y2, hy⟩ := hB
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬(j0 ∈ Cc y1 ↔ j0 ∈ Cc y2) := by
      by_contra hc; push_neg at hc; exact hy (Finset.ext fun j => by
        by_contra h; exact absurd (hc j) (by tauto))
    let T : Fin 1 → Fin n → Fin m → Bool := fun _ _ j => decide (j = j0)
    have hT : Fits n m 1 T 0 := by
      apply tapsFit n m 1 0 hn [G0] g1 g2 (by rw [g3]) (fun _ => n + m) (fun _ => by simp)
        (fun _ => g4) (fun _ _ => 0) (fun _ j => z (decide (j = j0)))
      intro j x y; rw [g5 rfl]; ring
    have h := run T hT x1 x2 y1 y2
    have hP : ∀ x y, Pz R Cc (fun u v => z (T 0 u v)) x y =
        ((R x).card : ZMod 2) * (if j0 ∈ Cc y then 1 else 0) := by
      intro x y
      simp only [Pz, T, z, decide_eq_true_eq, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul]
    simp only [hP] at h
    have e1 := pair_one _ _ hpar
    have e2 := mem_one _ _ _ hj0
    have : (((R x1).card : ZMod 2) + (R x2).card) * ((if j0 ∈ Cc y1 then 1 else 0 : ZMod 2) +
        (if j0 ∈ Cc y2 then 1 else 0)) = 0 := by linear_combination h
    rw [e1, e2] at this
    exact absurd this (by decide)
  · intro y1 y2
    by_contra hpar
    simp only [not_forall] at hA
    obtain ⟨x1, x2, hx⟩ := hA
    obtain ⟨i0, hi0⟩ : ∃ i0, ¬(i0 ∈ R x1 ↔ i0 ∈ R x2) := by
      by_contra hc; push_neg at hc; exact hx (Finset.ext fun i => by
        by_contra h; exact absurd (hc i) (by tauto))
    let T : Fin 1 → Fin n → Fin m → Bool := fun _ i _ => decide (i = i0)
    have hT : Fits n m 1 T 0 := by
      apply tapsFit n m 1 0 hn [G0] g1 g2 (by rw [g3]) (fun _ => n + m) (fun _ => by simp)
        (fun _ => g4) (fun _ i => z (decide (i = i0))) (fun _ _ => 0)
      intro j x y; rw [g5 rfl]; ring
    have h := run T hT x1 x2 y1 y2
    have hP : ∀ x y, Pz R Cc (fun u v => z (T 0 u v)) x y =
        (if i0 ∈ R x then 1 else 0) * ((Cc y).card : ZMod 2) := by
      intro x y
      simp only [Pz, T, z, decide_eq_true_eq, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum, Finset.sum_ite_eq', mul_comm]
    simp only [hP] at h
    have e1 := pair_one _ _ hpar
    have e2 := mem_one _ _ _ hi0
    have : ((if i0 ∈ R x1 then 1 else 0 : ZMod 2) + (if i0 ∈ R x2 then 1 else 0)) *
        (((Cc y1).card : ZMod 2) + (Cc y2).card) = 0 := by linear_combination h
    rw [e1, e2] at this
    exact absurd this (by decide)

theorem mainIff (n m n' m' : ℕ) (hn : 0 < n) (hm : 0 < m) (hn' : 0 < n') (hm' : 0 < m')
    (R : Fin n' → Finset (Fin n)) (Cc : Fin m' → Finset (Fin m)) :
    (∀ (g s : ℕ) (T : Fin g → Fin n → Fin m → Bool), Fits n m g T s →
      Fits n' m' g (fun i => pullB R Cc (T i)) s) ↔
    (∀ x x', R x = R x') ∨ (∀ y y', Cc y = Cc y') ∨
      ((∀ x x', (R x).card % 2 = (R x').card % 2) ∧ (∀ y y', (Cc y).card % 2 = (Cc y').card % 2)) := by
  constructor
  · exact nec hn hm R Cc
  · intro hc g s T hT
    rcases hc with hA | hB | ⟨hρ, hσ⟩
    · exact suffConst hn' hm' R Cc (Or.inl hA) g s T
    · exact suffConst hn' hm' R Cc (Or.inr hB) g s T
    · apply suffP hn' (by omega) R Cc ((R ⟨0, hn'⟩).card : ZMod 2) ((Cc ⟨0, hm'⟩).card : ZMod 2)
        (fun x => by rw [ZMod.natCast_eq_natCast_iff']; exact hρ x _)
        (fun y => by rw [ZMod.natCast_eq_natCast_iff']; exact hσ y _) g s T hT

end PEqualNP.Outside.L_meta_32027

open PEqualNP.Outside.L_meta_32027

theorem PEqualNP.Outside.L_meta_32027 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

∀ (n m n' m' : ℕ), 0 < n → 0 < m → 0 < n' → 0 < m' →
  ∀ (R : Fin n' → Finset (Fin n)) (C : Fin m' → Finset (Fin m)),
    let pull := fun (G : Fin n → Fin m → Bool) (x : Fin n') (y : Fin m') =>
      (((R x).sum (fun i => ((C y).filter (fun j => G i j)).card)) % 2) == 1
    (∀ (g s : ℕ) (T : Fin g → Fin n → Fin m → Bool),
      fits n m g T s → fits n' m' g (fun i => pull (T i)) s) ↔
      (∀ x x', R x = R x') ∨ (∀ y y', C y = C y') ∨
      ((∀ x x', (R x).card % 2 = (R x').card % 2) ∧
       (∀ y y', (C y).card % 2 = (C y').card % 2)) := by
  intro nonlinear depths fits n m n' m' hn hm hn' hm' R C
  exact mainIff n m n' m' hn hm hn' hm' R C
