import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27301

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def emb7 (y : Fin 7 → Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => y 0
  | ⟨2, _⟩ => y 1
  | ⟨3, _⟩ => y 2
  | ⟨4, _⟩ => y 3
  | ⟨5, _⟩ => false
  | ⟨6, _⟩ => y 4
  | ⟨7, _⟩ => y 5
  | ⟨8, _⟩ => y 6

def f7 (y : Fin 7 → Bool) : Bool :=
  (y 0 && y 2 && y 6) || (y 1 && y 2 && y 5) || (y 1 && y 3 && y 4)

lemma pm3_emb7 (y : Fin 7 → Bool) : pm3 (emb7 y) = f7 y := by
  simp [pm3, emb7, f7]

lemma head_getElem {α : Type} {l : List α} {a : α} (h : l.head? = some a) :
    ∃ hlt : 0 < l.length, l[0]'hlt = a := by
  cases l with
  | nil => simp at h
  | cons x xs => simp at h; exact ⟨Nat.zero_lt_succ _, h⟩

lemma tail_head_getElem {α : Type} {l : List α} {a : α} (h : l.tail.head? = some a) :
    ∃ hlt : 1 < l.length, l[1]'hlt = a := by
  cases l with
  | nil => simp at h
  | cons _ xs =>
    cases xs with
    | nil => simp at h
    | cons y ys => simp at h; exact ⟨by simp, h⟩

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]

lemma getD_append_right {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  by_cases h2 : i < (l₁ ++ l₂).length
  · have h3 : i - l₁.length < l₂.length := by simp at h2; omega
    rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h3, List.getElem_append_right h]
  · have h3 : l₂.length ≤ i - l₁.length := by simp at h2; omega
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ h3]

def foldWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma foldWires_nil (w : List Bool) : foldWires [] w = w := rfl

lemma foldWires_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    foldWires (g :: gs) w =
      foldWires gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wires_eq_foldWires (C : Circuit) (x : List Bool) :
    C.wires x = foldWires C.gates x := rfl

lemma foldWires_length (gs : List Gate) (w : List Bool) :
    (foldWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [foldWires_nil]
  | cons g gs ih =>
    rw [foldWires_cons, ih]
    simp; omega

lemma foldWires_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (foldWires gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [foldWires_cons]
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      simp; omega
    rw [ih _ hi', getD_append_left _ _ _ _ hi]

lemma foldWires_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    foldWires (gs₁ ++ gs₂) w = foldWires gs₂ (foldWires gs₁ w) := by
  simp [foldWires, List.foldl_append]

lemma list_split_at {α : Type} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
    cases j with
    | zero => simp
    | succ k =>
      simp only [List.length_cons] at hj
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih k (by omega)

lemma foldWires_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (foldWires gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (foldWires gs w).getD i false) := by
  have hsp := list_split_at gs j hj
  have hlen : (foldWires (gs.take j) w).length = w.length + j := by
    rw [foldWires_length, List.length_take, Nat.min_eq_left (by omega)]
  have hleft : ∀ i < w.length + j,
      (foldWires gs w).getD i false = (foldWires (gs.take j) w).getD i false := by
    intro i hi
    conv_lhs => rw [hsp]
    rw [foldWires_append, foldWires_getD_lt _ _ _ (by omega)]
  have hmap : gs[j].inputs.map (fun i => (foldWires gs w).getD i false) =
      gs[j].inputs.map (fun i => (foldWires (gs.take j) w).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hleft i (hin i hi)
  rw [hmap]
  conv_lhs => rw [hsp]
  rw [foldWires_append, foldWires_cons]
  have hlt : w.length + j < (foldWires (gs.take j) w ++
      [gs[j].op.eval (gs[j].inputs.map fun i => (foldWires (gs.take j) w).getD i false)]).length := by
    simp [hlen]
  rw [foldWires_getD_lt _ _ _ hlt, getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero]

inductive SGate where
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)

def SGate.inputs : SGate → List ℕ
  | .not a => [a]
  | .and a b => [a, b]
  | .or a b => [a, b]

def SGate.isBin : SGate → Bool
  | .not _ => false
  | .and _ _ => true
  | .or _ _ => true

def SGate.eval (w : List Bool) : SGate → Bool
  | .not a => !(w.getD a false)
  | .and a b => w.getD a false && w.getD b false
  | .or a b => w.getD a false || w.getD b false

def swires (gs : List SGate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.eval acc]) w

lemma swires_nil (w : List Bool) : swires [] w = w := rfl

lemma swires_cons (g : SGate) (gs : List SGate) (w : List Bool) :
    swires (g :: gs) w = swires gs (w ++ [g.eval w]) := rfl

lemma swires_length (gs : List SGate) (w : List Bool) :
    (swires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [swires_nil]
  | cons g gs ih =>
    rw [swires_cons, ih]; simp; omega

lemma swires_getD_lt (gs : List SGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (swires gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [swires_cons]
    have hi' : i < (w ++ [g.eval w]).length := by simp; omega
    rw [ih _ hi', getD_append_left _ _ _ _ hi]

lemma swires_append (gs₁ gs₂ : List SGate) (w : List Bool) :
    swires (gs₁ ++ gs₂) w = swires gs₂ (swires gs₁ w) := by
  simp [swires, List.foldl_append]

def SValid (n : ℕ) (gs : List SGate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), match gs[j] with
    | .not a => a < n + j
    | .and a b => a ≠ b ∧ a < n + j ∧ b < n + j
    | .or a b => a ≠ b ∧ a < n + j ∧ b < n + j

lemma swires_getD_gate {n : ℕ} (gs : List SGate) (hv : SValid n gs)
    (w : List Bool) (hw : w.length = n) (j : ℕ) (hj : j < gs.length) :
    (swires gs w).getD (n + j) false = gs[j].eval (swires gs w) := by
  have hsp := list_split_at gs j hj
  have hlen : (swires (gs.take j) w).length = n + j := by
    rw [swires_length, hw, List.length_take, Nat.min_eq_left (by omega)]
  have hleft : ∀ i < n + j,
      (swires gs w).getD i false = (swires (gs.take j) w).getD i false := by
    intro i hi
    conv_lhs => rw [hsp]
    rw [swires_append, swires_getD_lt _ _ _ (by omega)]
  have hgj := hv j hj
  have hev : gs[j].eval (swires gs w) = gs[j].eval (swires (gs.take j) w) := by
    cases hg : gs[j] with
    | not a =>
      simp only [hg] at hgj
      simp only [SGate.eval]
      rw [hleft a hgj]
    | and a b =>
      simp only [hg] at hgj
      simp only [SGate.eval]
      rw [hleft a hgj.2.1, hleft b hgj.2.2]
    | or a b =>
      simp only [hg] at hgj
      simp only [SGate.eval]
      rw [hleft a hgj.2.1, hleft b hgj.2.2]
  rw [hev]
  conv_lhs => rw [hsp]
  rw [swires_append, swires_cons]
  have hlt : n + j < (swires (gs.take j) w ++ [gs[j].eval (swires (gs.take j) w)]).length := by
    simp [hlen]
  rw [swires_getD_lt _ _ _ hlt, getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero]

inductive Rep where
  | const (b : Bool)
  | wire (u : ℕ)

def Rep.isConst : Rep → Bool
  | .const _ => true
  | .wire _ => false

def Rep.eval (w : List Bool) : Rep → Bool
  | .const b => b
  | .wire u => w.getD u false

def stepGate (n : ℕ) (reps : List Rep) (gs : List SGate) (g : Gate) : Rep × Option SGate :=
  match g.op, g.inputs with
  | .not, [a] =>
    match reps.getD a (.const false) with
    | .const b => (.const (!b), none)
    | .wire u => (.wire (n + gs.length), some (.not u))
  | .and, [a, b] =>
    match reps.getD a (.const false), reps.getD b (.const false) with
    | .const false, _ => (.const false, none)
    | _, .const false => (.const false, none)
    | .const true, r => (r, none)
    | r, .const true => (r, none)
    | .wire u, .wire v =>
      if u = v then (.wire u, none)
      else (.wire (n + gs.length), some (.and u v))
  | .or, [a, b] =>
    match reps.getD a (.const false), reps.getD b (.const false) with
    | .const true, _ => (.const true, none)
    | _, .const true => (.const true, none)
    | .const false, r => (r, none)
    | r, .const false => (r, none)
    | .wire u, .wire v =>
      if u = v then (.wire u, none)
      else (.wire (n + gs.length), some (.or u v))
  | _, _ => (.const false, none)

def restrictStep (n : ℕ) (st : List Rep × List SGate) (g : Gate) : List Rep × List SGate :=
  let res := stepGate n st.1 st.2 g
  (st.1 ++ [res.1], match res.2 with | none => st.2 | some sg => st.2 ++ [sg])

def stateAt (cgs : List Gate) (init : List Rep) (n : ℕ) : ℕ → List Rep × List SGate
  | 0 => (init, [])
  | k + 1 =>
    let st := stateAt cgs init n k
    match cgs[k]? with
    | none => st
    | some g => restrictStep n st g

def initReps7 : List Rep :=
  [.const false, .wire 0, .wire 1, .wire 2, .wire 3, .const false, .wire 4, .wire 5, .wire 6]

lemma initReps7_len : initReps7.length = 9 := rfl

lemma stateAt_reps_len (cgs : List Gate) (init : List Rep) (n k : ℕ) (hk : k ≤ cgs.length) :
    (stateAt cgs init n k).1.length = init.length + k := by
  induction k with
  | zero => simp [stateAt]
  | succ k ih =>
    have hlt : k < cgs.length := by omega
    simp only [stateAt, List.getElem?_eq_getElem hlt, restrictStep, List.length_append,
      List.length_singleton]
    rw [ih (by omega)]; omega

lemma stateAt_reps_len_mono (cgs : List Gate) (init : List Rep) (n a b : ℕ) (hab : a ≤ b) :
    (stateAt cgs init n a).1.length ≤ (stateAt cgs init n b).1.length := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    rw [ha]
  | succ b ih =>
    by_cases h : a ≤ b
    · have := ih h
      simp only [stateAt]
      cases cgs[b]? with
      | none => exact this
      | some g => simp only [restrictStep, List.length_append, List.length_singleton]; omega
    · have ha : a = b + 1 := by omega
      rw [ha]

lemma stateAt_reps_mono (cgs : List Gate) (init : List Rep) (n : ℕ) {k₁ k₂ w : ℕ}
    (hle : k₁ ≤ k₂) (hw : w < (stateAt cgs init n k₁).1.length) :
    (stateAt cgs init n k₂).1.getD w (.const false) =
      (stateAt cgs init n k₁).1.getD w (.const false) := by
  induction k₂ with
  | zero =>
    have hk : k₁ = 0 := by omega
    rw [hk]
  | succ k ih =>
    by_cases h : k₁ ≤ k
    · have hw' : w < (stateAt cgs init n k).1.length :=
        lt_of_lt_of_le hw (stateAt_reps_len_mono cgs init n k₁ k h)
      rw [← ih h]
      simp only [stateAt]
      cases cgs[k]? with
      | none => rfl
      | some g =>
        simp only [restrictStep]
        exact getD_append_left _ _ _ _ hw'
    · have hk : k₁ = k + 1 := by omega
      rw [hk]

def NormGate (n j : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, a < n + j ∧ g.inputs = [a]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < n + j ∧ g.inputs = [a, b])

lemma stepGate_valid_and_eval {n : ℕ} (reps : List Rep) (gs : List SGate) (g : Gate)
    (hv : SValid n gs)
    (hreps : ∀ r ∈ reps, match r with | .const _ => True | .wire u => u < n + gs.length)
    (hnorm : NormGate reps.length 0 g) :
    let res := stepGate n reps gs g
    let gs' := match res.2 with | none => gs | some sg => gs ++ [sg]
    SValid n gs' ∧
    (match res.1 with | .const _ => True | .wire u => u < n + gs'.length) ∧
    (∀ y : List Bool, y.length = n →
      res.1.eval (swires gs' y) =
        g.op.eval (g.inputs.map fun i => (reps.getD i (.const false)).eval (swires gs y))) := by
  have hrep_get : ∀ i, i < reps.length → match reps.getD i (.const false) with
      | .const _ => True | .wire u => u < n + gs.length := by
    intro i hi
    have hmem : reps.getD i (.const false) ∈ reps := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact hreps _ hmem
  have hv_app : ∀ sg, (match sg with
      | .not a => a < n + gs.length
      | .and a b => a ≠ b ∧ a < n + gs.length ∧ b < n + gs.length
      | .or a b => a ≠ b ∧ a < n + gs.length ∧ b < n + gs.length) →
      SValid n (gs ++ [sg]) := by
    intro sg hsg j hj
    by_cases hlt : j < gs.length
    · have hjv := hv j hlt
      simpa [List.getElem_append_left hlt] using hjv
    · have heq : j = gs.length := by simp at hj; omega
      have hget : (gs ++ [sg])[j] = sg := by simp [heq]
      simpa [hget, heq] using hsg
  rcases hnorm with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
  · simp only [Nat.add_zero] at ha
    have hra := hrep_get a ha
    simp only [stepGate, hop, hin]
    cases hga : reps.getD a (.const false) with
    | const c =>
      refine ⟨hv, trivial, fun y _ => ?_⟩
      simp only [List.map_cons, List.map_nil, hga, Rep.eval, GateOp.eval, List.headD_cons]
    | wire u =>
      simp only [hga] at hra
      have hv' : SValid n (gs ++ [.not u]) := hv_app (.not u) hra
      refine ⟨hv', by simp, fun y hy => ?_⟩
      simp only [List.map_cons, List.map_nil, hga, Rep.eval, GateOp.eval, List.headD_cons]
      rw [swires_append, swires_cons, swires_nil]
      rw [getD_append_right _ _ _ _ (by rw [swires_length, hy])]
      simp only [swires_length, hy, Nat.sub_self, List.getD_cons_zero, SGate.eval]
  · simp only [Nat.add_zero] at hb
    have ha : a < reps.length := by omega
    have hra := hrep_get a ha
    have hrb := hrep_get b hb
    rcases hop with hop | hop
    · simp only [stepGate, hop, hin]
      cases hga : reps.getD a (.const false) with
      | const ca =>
        cases ca with
        | false =>
          refine ⟨hv, trivial, fun y _ => ?_⟩
          simp only [List.map_cons, List.map_nil, hga, Rep.eval, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.false_and]
        | true =>
          cases hgb : reps.getD b (.const false) with
          | const cb =>
            cases cb with
            | false =>
              refine ⟨hv, trivial, fun y _ => ?_⟩
              simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
                List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.false_and]
            | true =>
              refine ⟨hv, trivial, fun y _ => ?_⟩
              simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
                List.all_cons, List.all_nil, id_eq, Bool.true_and]
          | wire v =>
            simp only [hgb] at hrb
            refine ⟨hv, hrb, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_true]
      | wire u =>
        simp only [hga] at hra
        cases hgb : reps.getD b (.const false) with
        | const cb =>
          cases cb with
          | false =>
            refine ⟨hv, trivial, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false]
          | true =>
            refine ⟨hv, hra, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_true]
        | wire v =>
          simp only [hgb] at hrb
          by_cases huv : u = v
          · simp only [huv, ite_true]
            refine ⟨hv, hrb, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, huv, Rep.eval, GateOp.eval,
              List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
          · simp only [huv, ite_false]
            have hv' : SValid n (gs ++ [.and u v]) := hv_app (.and u v) ⟨huv, hra, hrb⟩
            refine ⟨hv', by simp, fun y hy => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
            rw [swires_append, swires_cons, swires_nil]
            rw [getD_append_right _ _ _ _ (by rw [swires_length, hy])]
            simp only [swires_length, hy, Nat.sub_self, List.getD_cons_zero, SGate.eval]
    · simp only [stepGate, hop, hin]
      cases hga : reps.getD a (.const false) with
      | const ca =>
        cases ca with
        | true =>
          refine ⟨hv, trivial, fun y _ => ?_⟩
          simp only [List.map_cons, List.map_nil, hga, Rep.eval, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.true_or]
        | false =>
          cases hgb : reps.getD b (.const false) with
          | const cb =>
            cases cb with
            | true =>
              refine ⟨hv, trivial, fun y _ => ?_⟩
              simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
                List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.true_or]
            | false =>
              refine ⟨hv, trivial, fun y _ => ?_⟩
              simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
                List.any_cons, List.any_nil, id_eq, Bool.false_or]
          | wire v =>
            simp only [hgb] at hrb
            refine ⟨hv, hrb, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
      | wire u =>
        simp only [hga] at hra
        cases hgb : reps.getD b (.const false) with
        | const cb =>
          cases cb with
          | true =>
            refine ⟨hv, trivial, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.true_or, Bool.or_true]
          | false =>
            refine ⟨hv, hra, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
        | wire v =>
          simp only [hgb] at hrb
          by_cases huv : u = v
          · simp only [huv, ite_true]
            refine ⟨hv, hrb, fun y _ => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, huv, Rep.eval, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
          · simp only [huv, ite_false]
            have hv' : SValid n (gs ++ [.or u v]) := hv_app (.or u v) ⟨huv, hra, hrb⟩
            refine ⟨hv', by simp, fun y hy => ?_⟩
            simp only [List.map_cons, List.map_nil, hga, hgb, Rep.eval, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            rw [swires_append, swires_cons, swires_nil]
            rw [getD_append_right _ _ _ _ (by rw [swires_length, hy])]
            simp only [swires_length, hy, Nat.sub_self, List.getD_cons_zero, SGate.eval]

lemma stateAt_invariants (cgs : List Gate)
    (hnorm : ∀ j : Fin cgs.length, NormGate 9 j.val cgs[j.val])
    (k : ℕ) (hk : k ≤ cgs.length) :
    let st := stateAt cgs initReps7 7 k
    SValid 7 st.2 ∧
    (∀ r ∈ st.1, match r with | .const _ => True | .wire u => u < 7 + st.2.length) ∧
    (∀ y : Fin 7 → Bool, ∀ w < 9 + k,
      (st.1.getD w (.const false)).eval (swires st.2 (List.ofFn y)) =
        (foldWires (cgs.take k) (List.ofFn (emb7 y))).getD w false) := by
  induction k with
  | zero =>
    refine ⟨fun j hj => by simp [stateAt] at hj, ?_, ?_⟩
    · intro r hr
      simp only [stateAt, initReps7, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [stateAt, List.length_nil]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · intro y w hw
      simp only [stateAt, List.take_zero, foldWires_nil, swires_nil]
      have h9 : w < 9 := by omega
      interval_cases w <;>
        simp [initReps7, Rep.eval, emb7, List.getD_eq_getElem]
  | succ k ih =>
    have hk' : k < cgs.length := by omega
    obtain ⟨hv, hreps, heval⟩ := ih (by omega)
    set st := stateAt cgs initReps7 7 k with hst_def
    have hlen : st.1.length = 9 + k := by
      have := stateAt_reps_len cgs initReps7 7 k (by omega)
      rw [initReps7_len] at this; exact this
    have hng : NormGate st.1.length 0 cgs[k] := by
      rw [hlen]
      simpa [NormGate] using hnorm ⟨k, hk'⟩
    obtain ⟨hv', hnewr, hnewev⟩ := stepGate_valid_and_eval st.1 st.2 cgs[k] hv hreps hng
    have hst1 : stateAt cgs initReps7 7 (k + 1) = restrictStep 7 st cgs[k] := by
      simp [stateAt, List.getElem?_eq_getElem hk', hst_def]
    rw [hst1]
    simp only [restrictStep]
    refine ⟨hv', ?_, ?_⟩
    · intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have h1 := hreps r hr
        cases r with
        | const _ => trivial
        | wire u =>
          cases (stepGate 7 st.1 st.2 cgs[k]).2 <;> simp at h1 ⊢ <;> omega
      · exact hnewr
    · intro y w hw
      have htake : cgs.take (k + 1) = cgs.take k ++ [cgs[k]] := by
        rw [List.take_succ_eq_append_getElem hk']
      have hfwlen : (foldWires (cgs.take k) (List.ofFn (emb7 y))).length = 9 + k := by
        rw [foldWires_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
      by_cases hwlt : w < 9 + k
      · rw [getD_append_left _ _ _ _ (by omega)]
        rw [htake, foldWires_append, foldWires_getD_lt _ _ _ (by omega)]
        rw [← heval y w hwlt]
        have hrmem : st.1.getD w (.const false) ∈ st.1 := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
        have hrb := hreps _ hrmem
        cases hget : st.1.getD w (.const false) with
        | const _ => rfl
        | wire u =>
          simp only [hget] at hrb
          simp only [Rep.eval]
          cases (stepGate 7 st.1 st.2 cgs[k]).2 with
          | none => rfl
          | some sg =>
            rw [swires_append, swires_getD_lt _ _ _ (by rw [swires_length, List.length_ofFn]; omega)]
      · have hweq : w = 9 + k := by omega
        subst hweq
        rw [getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        rw [hnewev (List.ofFn y) (by simp)]
        rw [htake, foldWires_append, foldWires_cons, foldWires_nil]
        rw [getD_append_right _ _ _ _ (by omega)]
        simp only [hfwlen, Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hilt : i < 9 + k := by
          have hnk := hnorm ⟨k, hk'⟩
          dsimp only at hnk
          rcases hnk with ⟨_, a, ha, hin⟩ | ⟨_, a, b, _, hb, hin⟩
          · rw [hin] at hi; simp at hi; omega
          · rw [hin] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
        exact heval y i hilt

lemma stepGate_isNone_of_const {n : ℕ} (reps : List Rep) (gs : List SGate) (g : Gate)
    (hnorm : NormGate reps.length 0 g)
    (hc : (stepGate n reps gs g).1.isConst = true ∨
      g.inputs.any (fun i => (reps.getD i (.const false)).isConst) = true) :
    (stepGate n reps gs g).2 = none := by
  rcases hnorm with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
  · simp only [stepGate, hop, hin] at hc ⊢
    cases hga : reps.getD a (.const false) with
    | const _ => rfl
    | wire _ =>
      simp only [List.any_cons, List.any_nil, Bool.or_false] at hc
      rw [hga] at hc
      simp [Rep.isConst] at hc
  · rcases hop with hop | hop <;>
    · simp only [stepGate, hop, hin] at hc ⊢
      cases hga : reps.getD a (.const false) with
      | const ca =>
        cases hgb : reps.getD b (.const false) with
        | const cb => cases ca <;> cases cb <;> rfl
        | wire _ => cases ca <;> rfl
      | wire u =>
        cases hgb : reps.getD b (.const false) with
        | const cb => cases cb <;> rfl
        | wire v =>
          simp only [List.any_cons, List.any_nil, Bool.or_false] at hc
          rw [hga, hgb] at hc
          by_cases huv : u = v
          · simp [huv]
          · simp [huv, Rep.isConst] at hc

lemma stepGate_const_of_two_consts {n : ℕ} (reps : List Rep) (gs : List SGate) (g : Gate)
    (hnorm : NormGate reps.length 0 g)
    (hall : ∀ i ∈ g.inputs, (reps.getD i (.const false)).isConst = true) :
    (stepGate n reps gs g).1.isConst = true := by
  rcases hnorm with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
  · have ha : (reps.getD a (.const false)).isConst = true := hall a (by simp [hin])
    simp only [stepGate, hop, hin]
    cases hga : reps.getD a (.const false) with
    | const _ => rfl
    | wire _ => rw [hga] at ha; exact Bool.noConfusion ha
  · have ha : (reps.getD a (.const false)).isConst = true := hall a (by simp [hin])
    have hb : (reps.getD b (.const false)).isConst = true := hall b (by simp [hin])
    rcases hop with hop | hop <;>
    · simp only [stepGate, hop, hin]
      cases hga : reps.getD a (.const false) with
      | wire _ => rw [hga] at ha; exact Bool.noConfusion ha
      | const ca =>
        cases hgb : reps.getD b (.const false) with
        | wire _ => rw [hgb] at hb; exact Bool.noConfusion hb
        | const cb => cases ca <;> cases cb <;> rfl

def isKilledGate (finalReps : List Rep) (cgs : List Gate) (j : ℕ) : Bool :=
  (finalReps.getD (9 + j) (.const false)).isConst ||
  (cgs.getD j ⟨.and, []⟩).inputs.any fun i => (finalReps.getD i (.const false)).isConst

lemma stateAt_gates_count (cgs : List Gate)
    (hnorm : ∀ j : Fin cgs.length, NormGate 9 j.val cgs[j.val])
    (k : ℕ) (hk : k ≤ cgs.length) :
    (stateAt cgs initReps7 7 k).2.length +
      ((Finset.range k).filter fun j =>
        isKilledGate (stateAt cgs initReps7 7 cgs.length).1 cgs j = true).card ≤ k := by
  set finalReps := (stateAt cgs initReps7 7 cgs.length).1
  induction k with
  | zero => simp [stateAt]
  | succ k ih =>
    have hk' : k < cgs.length := by omega
    have hih := ih (by omega)
    set st := stateAt cgs initReps7 7 k
    have hst_len : st.1.length = 9 + k := by
      have := stateAt_reps_len cgs initReps7 7 k (by omega)
      rw [initReps7_len] at this; exact this
    have hst1 : stateAt cgs initReps7 7 (k + 1) = restrictStep 7 st cgs[k] := by
      simp [stateAt, List.getElem?_eq_getElem hk', st]
    have hgetD : cgs.getD k ⟨.and, []⟩ = cgs[k] := List.getD_eq_getElem _ _ hk'
    have hng : NormGate st.1.length 0 cgs[k] := by
      rw [hst_len]; simpa [NormGate] using hnorm ⟨k, hk'⟩
    have hrep_out : finalReps.getD (9 + k) (.const false) = (stepGate 7 st.1 st.2 cgs[k]).1 := by
      have hlt : 9 + k < (stateAt cgs initReps7 7 (k + 1)).1.length := by
        rw [stateAt_reps_len cgs initReps7 7 (k + 1) (by omega), initReps7_len]; omega
      rw [stateAt_reps_mono cgs initReps7 7 (by omega : k + 1 ≤ cgs.length) hlt]
      rw [hst1]; simp only [restrictStep]
      rw [getD_append_right _ _ _ _ (by omega)]
      simp only [hst_len, Nat.sub_self, List.getD_cons_zero]
    have hrep_in : ∀ i ∈ cgs[k].inputs,
        finalReps.getD i (.const false) = st.1.getD i (.const false) := by
      intro i hi
      have hilt : i < 9 + k := by
        have hnk := hnorm ⟨k, hk'⟩
        dsimp only at hnk
        rcases hnk with ⟨_, a, ha, hin⟩ | ⟨_, a, b, _, hb, hin⟩
        · rw [hin] at hi; simp at hi; omega
        · rw [hin] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
      exact stateAt_reps_mono cgs initReps7 7 (by omega : k ≤ cgs.length) (by rw [hst_len]; exact hilt)
    rw [Finset.range_add_one, Finset.filter_insert, hst1]
    simp only [restrictStep]
    by_cases hkill : isKilledGate finalReps cgs k = true
    · rw [if_pos hkill]
      have hkill' : (finalReps.getD (9 + k) (.const false)).isConst = true ∨
          cgs[k].inputs.any (fun i => (finalReps.getD i (.const false)).isConst) = true := by
        simp only [isKilledGate, hgetD, Bool.or_eq_true] at hkill
        exact hkill
      have hkc : (stepGate 7 st.1 st.2 cgs[k]).1.isConst = true ∨
          cgs[k].inputs.any (fun i => (st.1.getD i (.const false)).isConst) = true := by
        rcases hkill' with h1 | h2
        · exact Or.inl (hrep_out ▸ h1)
        · right
          rw [List.any_eq_true] at h2 ⊢
          rcases h2 with ⟨i, hi, hic⟩
          exact ⟨i, hi, hrep_in i hi ▸ hic⟩
      have hnone := stepGate_isNone_of_const st.1 st.2 cgs[k] hng hkc
      rw [hnone]
      have hnotmem : k ∉ (Finset.range k).filter (fun j => isKilledGate finalReps cgs j = true) := by
        simp
      rw [Finset.card_insert_of_notMem hnotmem]
      dsimp only [st] at hih ⊢
      omega
    · rw [if_neg hkill]
      dsimp only [st] at hih ⊢
      cases (stepGate 7 st.1 st.2 cgs[k]).2 <;> simp <;> omega

lemma exists_second_reader_zero (C : Circuit)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x)
    (hout : C.output + 1 = 9 + C.size)
    (hnorm : ∀ j : Fin C.gates.length, NormGate 9 j.val C.gates[j.val])
    (h0 : C.gates.head? = some ⟨GateOp.and, [0, 1]⟩) :
    ∃ j : Fin C.gates.length, j.val ≠ 0 ∧ 0 ∈ C.gates[j.val].inputs := by
  by_contra hno
  push_neg at hno
  let xa : Fin 9 → Bool := fun i => i == 0 || i == 4 || i == 8
  let xb : Fin 9 → Bool := fun i => i == 4 || i == 8
  obtain ⟨hlen, hg0⟩ := head_getElem h0
  have hagree : ∀ w, 1 ≤ w → w < 9 + C.gates.length →
      (C.wires (List.ofFn xa)).getD w false = (C.wires (List.ofFn xb)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw1 hwlt
      by_cases hw9 : w < 9
      · rw [wires_eq_foldWires, foldWires_getD_lt _ _ _ (by simp; omega)]
        rw [wires_eq_foldWires, foldWires_getD_lt _ _ _ (by simp; omega)]
        interval_cases w <;> simp [List.getD_eq_getElem, xa, xb]
      · set j := w - 9
        have hj : j < C.gates.length := by omega
        have hwj : w = 9 + j := by omega
        have hin : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn xa).length + j := by
          intro i hi
          have hnj := hnorm ⟨j, hj⟩
          dsimp only at hnj
          rcases hnj with ⟨_, a, ha, he⟩ | ⟨_, a, b, _, hb, he⟩
          · rw [he] at hi; simp at hi; simp; omega
          · rw [he] at hi; simp at hi; simp; rcases hi with rfl | rfl <;> omega
        have hinb : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn xb).length + j := by
          simpa using hin
        rw [hwj, wires_eq_foldWires, wires_eq_foldWires]
        have h1 := foldWires_getD_gate C.gates (List.ofFn xa) j hj hin
        have h2 := foldWires_getD_gate C.gates (List.ofFn xb) j hj hinb
        simp only [List.length_ofFn] at h1 h2
        rw [h1, h2]
        by_cases hj0 : j = 0
        · have hgj : C.gates[j] = ⟨GateOp.and, [0, 1]⟩ := by simp [hj0, hg0]
          rw [hgj]
          have h1a : (foldWires C.gates (List.ofFn xa)).getD 1 false = false := by
            rw [foldWires_getD_lt _ _ _ (by simp)]; simp [List.getD_eq_getElem, xa]
          have h1b : (foldWires C.gates (List.ofFn xb)).getD 1 false = false := by
            rw [foldWires_getD_lt _ _ _ (by simp)]; simp [List.getD_eq_getElem, xb]
          simp only [List.map_cons, List.map_nil, h1a, h1b, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false]
        · congr 1
          apply List.map_congr_left
          intro i hi
          have hi0 : i ≠ 0 := by
            intro hiz; subst hiz
            exact hno ⟨j, hj⟩ hj0 hi
          have hilt : i < 9 + j := by
            have := hin i hi; simp at this; exact this
          exact ih i (by omega) (by omega) (by omega)
  have hout_ge : 1 ≤ C.output := by simp [Circuit.size] at hout; omega
  have hout_lt : C.output < 9 + C.gates.length := by simp [Circuit.size] at hout; omega
  have heq : C.eval (List.ofFn xa) = C.eval (List.ofFn xb) := hagree C.output hout_ge hout_lt
  rw [heval xa, heval xb] at heq
  have : pm3 xa = true ∧ pm3 xb = false := by decide
  rw [this.1, this.2] at heq
  exact Bool.noConfusion heq

lemma exists_second_reader_five (C : Circuit)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x)
    (hout : C.output + 1 = 9 + C.size)
    (hnorm : ∀ j : Fin C.gates.length, NormGate 9 j.val C.gates[j.val])
    (h1 : C.gates.tail.head? = some ⟨GateOp.and, [5, 8]⟩) :
    ∃ j : Fin C.gates.length, j.val ≠ 1 ∧ 5 ∈ C.gates[j.val].inputs := by
  by_contra hno
  push_neg at hno
  let xa : Fin 9 → Bool := fun i => i == 1 || i == 5 || i == 6
  let xb : Fin 9 → Bool := fun i => i == 1 || i == 6
  obtain ⟨hlen, hg1⟩ := tail_head_getElem h1
  have hagree : ∀ w, w ≠ 5 → w < 9 + C.gates.length →
      (C.wires (List.ofFn xa)).getD w false = (C.wires (List.ofFn xb)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw5 hwlt
      by_cases hw9 : w < 9
      · rw [wires_eq_foldWires, foldWires_getD_lt _ _ _ (by simp; omega)]
        rw [wires_eq_foldWires, foldWires_getD_lt _ _ _ (by simp; omega)]
        interval_cases w <;> simp_all [List.getD_eq_getElem, xa, xb]
      · set j := w - 9
        have hj : j < C.gates.length := by omega
        have hwj : w = 9 + j := by omega
        have hin : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn xa).length + j := by
          intro i hi
          have hnj := hnorm ⟨j, hj⟩
          dsimp only at hnj
          rcases hnj with ⟨_, a, ha, he⟩ | ⟨_, a, b, _, hb, he⟩
          · rw [he] at hi; simp at hi; simp; omega
          · rw [he] at hi; simp at hi; simp; rcases hi with rfl | rfl <;> omega
        have hinb : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn xb).length + j := by
          simpa using hin
        rw [hwj, wires_eq_foldWires, wires_eq_foldWires]
        have h1w := foldWires_getD_gate C.gates (List.ofFn xa) j hj hin
        have h2w := foldWires_getD_gate C.gates (List.ofFn xb) j hj hinb
        simp only [List.length_ofFn] at h1w h2w
        rw [h1w, h2w]
        by_cases hj1 : j = 1
        · have hgj : C.gates[j] = ⟨GateOp.and, [5, 8]⟩ := by simp [hj1, hg1]
          rw [hgj]
          have h8a : (foldWires C.gates (List.ofFn xa)).getD 8 false = false := by
            rw [foldWires_getD_lt _ _ _ (by simp)]; simp [List.getD_eq_getElem, xa]
          have h8b : (foldWires C.gates (List.ofFn xb)).getD 8 false = false := by
            rw [foldWires_getD_lt _ _ _ (by simp)]; simp [List.getD_eq_getElem, xb]
          simp only [List.map_cons, List.map_nil, h8a, h8b, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false]
        · congr 1
          apply List.map_congr_left
          intro i hi
          have hi5 : i ≠ 5 := by
            intro hi5; subst hi5
            exact hno ⟨j, hj⟩ hj1 hi
          have hilt : i < 9 + j := by
            have := hin i hi; simp at this; exact this
          exact ih i (by omega) hi5 (by omega)
  have hout5 : C.output ≠ 5 := by simp [Circuit.size] at hout; omega
  have hout_lt : C.output < 9 + C.gates.length := by simp [Circuit.size] at hout; omega
  have heq : C.eval (List.ofFn xa) = C.eval (List.ofFn xb) := hagree C.output hout5 hout_lt
  rw [heval xa, heval xb] at heq
  have : pm3 xa = true ∧ pm3 xb = false := by decide
  rw [this.1, this.2] at heq
  exact Bool.noConfusion heq

lemma reduce_to_f7 (C : Circuit)
    (hsize : C.size ≤ 12)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x)
    (hout : C.output + 1 = 9 + C.size)
    (hnorm : ∀ j : Fin C.gates.length, NormGate 9 j.val C.gates[j.val])
    (hused : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some ⟨GateOp.and, [0, 1]⟩)
    (h1 : C.gates.tail.head? = some ⟨GateOp.and, [5, 8]⟩) :
    ∃ (gs : List SGate) (out : ℕ), SValid 7 gs ∧ gs.length ≤ 6 ∧ out < 7 + gs.length ∧
      ∀ y : Fin 7 → Bool, (swires gs (List.ofFn y)).getD out false = f7 y := by
  obtain ⟨hlen0, hg0⟩ := head_getElem h0
  obtain ⟨hlen1, hg1⟩ := tail_head_getElem h1
  set st := stateAt C.gates initReps7 7 C.gates.length
  obtain ⟨hv, hreps, hev⟩ := stateAt_invariants C.gates hnorm C.gates.length le_rfl
  have hev_final : ∀ y : Fin 7 → Bool, ∀ w < 9 + C.gates.length,
      (st.1.getD w (.const false)).eval (swires st.2 (List.ofFn y)) =
        (C.wires (List.ofFn (emb7 y))).getD w false := by
    intro y w hw
    have h := hev y w hw
    rw [List.take_length] at h
    exact h
  have hst_len : st.1.length = 9 + C.gates.length := by
    have := stateAt_reps_len C.gates initReps7 7 C.gates.length le_rfl
    rw [initReps7_len] at this; exact this
  have hinit_rep : ∀ w < 9, st.1.getD w (.const false) = initReps7.getD w (.const false) := by
    intro w hw
    exact stateAt_reps_mono C.gates initReps7 7 (Nat.zero_le _) (by simp [stateAt, initReps7_len, hw])
  have hc0 : (st.1.getD 0 (.const false)).isConst = true := by rw [hinit_rep 0 (by omega)]; rfl
  have hc1 : (st.1.getD 1 (.const false)).isConst = false := by rw [hinit_rep 1 (by omega)]; rfl
  have hc5 : (st.1.getD 5 (.const false)).isConst = true := by rw [hinit_rep 5 (by omega)]; rfl
  have hc8 : (st.1.getD 8 (.const false)).isConst = false := by rw [hinit_rep 8 (by omega)]; rfl
  have hg0_const : (st.1.getD 9 (.const false)).isConst = true := by
    have hlt1 : 9 < (stateAt C.gates initReps7 7 1).1.length := by
      rw [stateAt_reps_len C.gates initReps7 7 1 (by omega), initReps7_len]; omega
    rw [stateAt_reps_mono C.gates initReps7 7 (by omega : 1 ≤ C.gates.length) hlt1]
    simp only [stateAt, List.getElem?_eq_getElem hlen0, hg0, restrictStep]
    rw [getD_append_right _ _ _ _ (by rw [initReps7_len])]
    simp only [initReps7_len, Nat.sub_self, List.getD_cons_zero]
    rfl
  have hg1_const : (st.1.getD 10 (.const false)).isConst = true := by
    have hlt2 : 10 < (stateAt C.gates initReps7 7 2).1.length := by
      rw [stateAt_reps_len C.gates initReps7 7 2 (by omega), initReps7_len]; omega
    rw [stateAt_reps_mono C.gates initReps7 7 (by omega : 2 ≤ C.gates.length) hlt2]
    have h9 : (stateAt C.gates initReps7 7 1).1.length = 10 := by
      rw [stateAt_reps_len C.gates initReps7 7 1 (by omega), initReps7_len]
    have h5 : (stateAt C.gates initReps7 7 1).1.getD 5 (.const false) = .const false := by
      rw [stateAt_reps_mono C.gates initReps7 7 (Nat.zero_le 1) (by simp [stateAt, initReps7_len])]
      rfl
    have hstep2 : stateAt C.gates initReps7 7 2 =
        restrictStep 7 (stateAt C.gates initReps7 7 1) C.gates[1] := by
      simp only [stateAt, List.getElem?_eq_getElem hlen1]
    rw [hstep2, hg1]
    simp only [restrictStep]
    rw [getD_append_right _ _ _ _ (by rw [h9])]
    simp only [h9, Nat.sub_self, List.getD_cons_zero, stepGate, h5, Rep.isConst]
  have hout_not_const : (st.1.getD C.output (.const false)).isConst = false := by
    cases hro : st.1.getD C.output (.const false) with
    | wire _ => rfl
    | const b =>
      have hlt : C.output < 9 + C.gates.length := by simp [Circuit.size] at hout; omega
      have hT := hev_final (fun _ => true) C.output hlt
      have hF := hev_final (fun _ => false) C.output hlt
      rw [hro] at hT hF
      simp only [Rep.eval] at hT hF
      have heT : (C.wires (List.ofFn (emb7 fun _ => true))).getD C.output false = true := by
        change C.eval (List.ofFn (emb7 fun _ => true)) = true
        rw [heval, pm3_emb7]; decide
      have heF : (C.wires (List.ofFn (emb7 fun _ => false))).getD C.output false = false := by
        change C.eval (List.ofFn (emb7 fun _ => false)) = false
        rw [heval, pm3_emb7]; decide
      rw [heT] at hT; rw [heF] at hF
      rw [hT] at hF; exact Bool.noConfusion hF
  set K := (Finset.range (9 + C.gates.length)).filter
    fun w => (st.1.getD w (.const false)).isConst = true
  set Kg : Finset (Fin C.gates.length) := Finset.univ.filter
    fun j => (st.1.getD (9 + j.val) (.const false)).isConst = true
  set Pg : Finset (Fin C.gates.length) := Finset.univ.filter
    fun j => (st.1.getD (9 + j.val) (.const false)).isConst = false ∧
      C.gates[j.val].inputs.any (fun i => (st.1.getD i (.const false)).isConst) = true
  let edge (w : ℕ) (j : Fin C.gates.length) : ℕ := if w ∈ C.gates[j.val].inputs then 1 else 0
  have hsum_swap : ∑ w ∈ K, ∑ j : Fin C.gates.length, edge w j =
      ∑ j : Fin C.gates.length, ∑ w ∈ K, edge w j := Finset.sum_comm
  obtain ⟨r0, hr0ne, hr0in⟩ := exists_second_reader_zero C heval hout hnorm h0
  obtain ⟨r5, hr5ne, hr5in⟩ := exists_second_reader_five C heval hout hnorm h1
  have hdeg0 : 2 ≤ ∑ j : Fin C.gates.length, edge 0 j := by
    have hsub : ({⟨0, hlen0⟩, r0} : Finset (Fin C.gates.length)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset (f := fun j => edge 0 j) hsub
    have hne : (⟨0, hlen0⟩ : Fin C.gates.length) ≠ r0 := by
      intro h; exact hr0ne (congrArg Fin.val h).symm
    rw [Finset.sum_pair hne] at hle
    have he0 : edge 0 ⟨0, hlen0⟩ = 1 := by simp [edge, hg0]
    have her : edge 0 r0 = 1 := by simp [edge, hr0in]
    omega
  have hdeg5 : 2 ≤ ∑ j : Fin C.gates.length, edge 5 j := by
    have hsub : ({⟨1, hlen1⟩, r5} : Finset (Fin C.gates.length)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset (f := fun j => edge 5 j) hsub
    have hne : (⟨1, hlen1⟩ : Fin C.gates.length) ≠ r5 := by
      intro h; exact hr5ne (congrArg Fin.val h).symm
    rw [Finset.sum_pair hne] at hle
    have he1 : edge 5 ⟨1, hlen1⟩ = 1 := by simp [edge, hg1]
    have her : edge 5 r5 = 1 := by simp [edge, hr5in]
    omega
  have hdegKg : ∀ j ∈ Kg, 1 ≤ ∑ k : Fin C.gates.length, edge (9 + j.val) k := by
    intro j hj
    simp only [Kg, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hjnotlast : j.val + 1 < C.gates.length := by
      by_contra hge
      have heq : 9 + j.val = C.output := by
        simp [Circuit.size] at hout; omega
      rw [heq] at hj
      rw [hout_not_const] at hj
      exact Bool.noConfusion hj
    obtain ⟨k, _, hkin⟩ := hused j hjnotlast
    have hle : edge (9 + j.val) k ≤ ∑ m : Fin C.gates.length, edge (9 + j.val) m :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hk1 : edge (9 + j.val) k = 1 := by
      have : 9 + j.val ∈ C.gates[k.val].inputs := by simpa using hkin
      simp [edge, this]
    omega
  have hLHS : Kg.card + 4 ≤ ∑ w ∈ K, ∑ j : Fin C.gates.length, edge w j := by
    set Ksub : Finset ℕ := insert 0 (insert 5 (Kg.image fun j => 9 + j.val))
    have hsub : Ksub ⊆ K := by
      intro w hw
      simp only [Ksub, Finset.mem_insert, Finset.mem_image] at hw
      rcases hw with rfl | rfl | ⟨j, hj, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc0⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc5⟩
      · simp only [Kg, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩
    have hle := Finset.sum_le_sum_of_subset (f := fun w => ∑ j : Fin C.gates.length, edge w j) hsub
    have h0not : (0 : ℕ) ∉ insert 5 (Kg.image fun j => 9 + j.val) := by
      simp only [Finset.mem_insert, Finset.mem_image]
      rintro (h | ⟨j, _, h⟩) <;> omega
    have h5not : (5 : ℕ) ∉ Kg.image (fun j => 9 + j.val) := by
      simp only [Finset.mem_image]
      rintro ⟨j, _, h⟩; omega
    have hsum_sub : ∑ w ∈ Ksub, ∑ j : Fin C.gates.length, edge w j =
        (∑ j : Fin C.gates.length, edge 0 j) +
        (∑ j : Fin C.gates.length, edge 5 j) +
        ∑ w ∈ Kg.image (fun j => 9 + j.val), ∑ j : Fin C.gates.length, edge w j := by
      simp only [Ksub]
      rw [Finset.sum_insert h0not, Finset.sum_insert h5not]
      omega
    have himg : ∑ w ∈ Kg.image (fun j => 9 + j.val), ∑ j : Fin C.gates.length, edge w j =
        ∑ j ∈ Kg, ∑ k : Fin C.gates.length, edge (9 + j.val) k := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      dsimp only at hab
      exact Fin.ext (by omega)
    have hkg_sum : Kg.card ≤ ∑ j ∈ Kg, ∑ k : Fin C.gates.length, edge (9 + j.val) k := by
      calc Kg.card = ∑ _j ∈ Kg, 1 := by simp
        _ ≤ ∑ j ∈ Kg, ∑ k : Fin C.gates.length, edge (9 + j.val) k :=
          Finset.sum_le_sum fun j hj => hdegKg j hj
    omega
  have hRHS_each : ∀ j : Fin C.gates.length,
      (j.val = 0 → ∑ w ∈ K, edge w j = 1) ∧
      (j.val = 1 → ∑ w ∈ K, edge w j = 1) ∧
      (j ∈ Kg → ∑ w ∈ K, edge w j ≤ 2) ∧
      (j ∈ Pg → ∑ w ∈ K, edge w j ≤ 1) ∧
      (j ∉ Kg → j ∉ Pg → ∑ w ∈ K, edge w j = 0) := by
    intro j
    have hsum_eq : ∀ (l : List ℕ) (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < 9 + C.gates.length),
        (∑ w ∈ K, if w ∈ l then 1 else 0) =
        (l.filter fun x => (st.1.getD x (.const false)).isConst).length := by
      intro l hnd hlt
      induction l with
      | nil => simp
      | cons a t ih =>
        rw [List.nodup_cons] at hnd
        have hsplit : ∀ w ∈ K, (if w ∈ a :: t then 1 else 0) =
            (if w = a then 1 else 0) + (if w ∈ t then 1 else 0) := by
          intro w _
          by_cases hwa : w = a
          · subst hwa; simp [hnd.1]
          · simp [hwa]
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
        rw [ih hnd.2 (fun x hx => hlt x (List.mem_cons_of_mem a hx))]
        have hhead : (∑ w ∈ K, if w = a then 1 else 0) =
            if (st.1.getD a (.const false)).isConst = true then 1 else 0 := by
          have ha_lt : a < 9 + C.gates.length := hlt a List.mem_cons_self
          by_cases haK : a ∈ K
          · have hca : (st.1.getD a (.const false)).isConst = true := (Finset.mem_filter.mp haK).2
            rw [if_pos hca]
            rw [Finset.sum_eq_single a]
            · simp
            · intro b _ hba; simp [hba]
            · intro h; exact absurd haK h
          · have hca : (st.1.getD a (.const false)).isConst ≠ true := by
              intro h; exact haK (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, h⟩)
            rw [if_neg hca]
            apply Finset.sum_eq_zero
            intro b hb
            have hba : b ≠ a := by intro h; subst h; exact haK hb
            simp [hba]
        rw [hhead, List.filter_cons]
        cases (st.1.getD a (.const false)).isConst <;> simp <;> omega
    have hnd : C.gates[j.val].inputs.Nodup ∧ ∀ x ∈ C.gates[j.val].inputs, x < 9 + C.gates.length := by
      rcases hnorm j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
      · refine ⟨by rw [hin]; simp, fun x hx => ?_⟩
        rw [hin] at hx; simp at hx; omega
      · refine ⟨by rw [hin]; simp; omega, fun x hx => ?_⟩
        rw [hin] at hx; simp at hx; rcases hx with rfl | rfl <;> omega
    have hcard : ∑ w ∈ K, edge w j =
        (C.gates[j.val].inputs.filter fun x => (st.1.getD x (.const false)).isConst).length :=
      hsum_eq C.gates[j.val].inputs hnd.1 hnd.2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hj0
      have hgj : C.gates[j.val] = ⟨GateOp.and, [0, 1]⟩ := by simp [hj0, hg0]
      rw [hcard, hgj]
      simp only [List.filter_cons, List.filter_nil, hc0, hc1]
      rfl
    · intro hj1
      have hgj : C.gates[j.val] = ⟨GateOp.and, [5, 8]⟩ := by simp [hj1, hg1]
      rw [hcard, hgj]
      simp only [List.filter_cons, List.filter_nil, hc5, hc8]
      rfl
    · intro _
      rw [hcard]
      have hlen_le : C.gates[j.val].inputs.length ≤ 2 := by
        rcases hnorm j with ⟨_, _, _, hin⟩ | ⟨_, _, _, _, _, hin⟩ <;> rw [hin] <;> simp
      exact le_trans (List.length_filter_le _ _) hlen_le
    · intro hjP
      simp only [Pg, Finset.mem_filter, Finset.mem_univ, true_and] at hjP
      rw [hcard]
      rcases hnorm j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
      · rw [hin]; exact List.length_filter_le _ _
      · rw [hin]
        by_contra hgt
        simp only [List.filter_cons, List.filter_nil] at hgt
        have ha_c : (st.1.getD a (.const false)).isConst = true := by
          cases h1c : (st.1.getD a (.const false)).isConst <;>
          cases h2c : (st.1.getD b (.const false)).isConst <;>
          simp only [h1c, h2c] at hgt <;> simp at hgt ⊢
        have hb_c : (st.1.getD b (.const false)).isConst = true := by
          cases h1c : (st.1.getD a (.const false)).isConst <;>
          cases h2c : (st.1.getD b (.const false)).isConst <;>
          simp only [h1c, h2c] at hgt <;> simp at hgt ⊢
        set stj := stateAt C.gates initReps7 7 j.val
        have hstj_len : stj.1.length = 9 + j.val := by
          have := stateAt_reps_len C.gates initReps7 7 j.val (by omega)
          rw [initReps7_len] at this; exact this
        have hngj : NormGate stj.1.length 0 C.gates[j.val] := by
          rw [hstj_len]; simpa [NormGate] using hnorm j
        have hall_j : ∀ i ∈ C.gates[j.val].inputs, (stj.1.getD i (.const false)).isConst = true := by
          intro i hi
          rw [hin] at hi; simp at hi
          have hilt : i < stj.1.length := by rcases hi with rfl | rfl <;> omega
          have hmono := stateAt_reps_mono C.gates initReps7 7 (by omega : j.val ≤ C.gates.length) hilt
          rw [← hmono]
          rcases hi with rfl | rfl
          · exact ha_c
          · exact hb_c
        have hres_c := stepGate_const_of_two_consts (n := 7) stj.1 stj.2 C.gates[j.val] hngj hall_j
        have hrep_out : st.1.getD (9 + j.val) (.const false) =
            (stepGate 7 stj.1 stj.2 C.gates[j.val]).1 := by
          have hltj : 9 + j.val < (stateAt C.gates initReps7 7 (j.val + 1)).1.length := by
            rw [stateAt_reps_len C.gates initReps7 7 (j.val + 1) (by omega), initReps7_len]; omega
          rw [stateAt_reps_mono C.gates initReps7 7 (by omega : j.val + 1 ≤ C.gates.length) hltj]
          simp only [stateAt, List.getElem?_eq_getElem j.isLt, restrictStep]
          rw [getD_append_right _ _ _ _ (by rw [hstj_len])]
          simp only [hstj_len, Nat.sub_self, List.getD_cons_zero, stj]
        rw [hrep_out, hres_c] at hjP
        exact Bool.noConfusion hjP.1
    · intro hnotK hnotP
      rw [hcard, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro x hx hxc
      have hK_false : (st.1.getD (9 + j.val) (.const false)).isConst = false := by
        cases hc : (st.1.getD (9 + j.val) (.const false)).isConst with
        | false => rfl
        | true => exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩) hnotK
      have hany : C.gates[j.val].inputs.any (fun i => (st.1.getD i (.const false)).isConst) = true :=
        List.any_eq_true.mpr ⟨x, hx, hxc⟩
      exact hnotP (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hK_false, hany⟩)
  have hRHS : (∑ j : Fin C.gates.length, ∑ w ∈ K, edge w j) + 2 ≤ 2 * Kg.card + Pg.card := by
    let f (j : Fin C.gates.length) : ℕ :=
      if j.val = 0 ∨ j.val = 1 then 1
      else if j ∈ Kg then 2
      else if j ∈ Pg then 1
      else 0
    have hle : ∑ j : Fin C.gates.length, ∑ w ∈ K, edge w j ≤ ∑ j : Fin C.gates.length, f j := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨h0e, h1e, hKe, hPe, h00⟩ := hRHS_each j
      simp only [f]
      by_cases h01 : j.val = 0 ∨ j.val = 1
      · rw [if_pos h01]
        rcases h01 with h0v | h1v
        · rw [h0e h0v]
        · rw [h1e h1v]
      · rw [if_neg h01]
        by_cases hjK : j ∈ Kg
        · rw [if_pos hjK]; exact hKe hjK
        · rw [if_neg hjK]
          by_cases hjP : j ∈ Pg
          · rw [if_pos hjP]; exact hPe hjP
          · rw [if_neg hjP]; rw [h00 hjK hjP]
    have hj0_mem : (⟨0, hlen0⟩ : Fin C.gates.length) ∈ Kg :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg0_const⟩
    have hj1_mem : (⟨1, hlen1⟩ : Fin C.gates.length) ∈ Kg :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg1_const⟩
    have hdisj : Disjoint Kg Pg := by
      rw [Finset.disjoint_left]
      intro j h1m h2m
      simp only [Kg, Pg, Finset.mem_filter, Finset.mem_univ, true_and] at h1m h2m
      rw [h1m] at h2m; exact Bool.noConfusion h2m.1
    have hf_sum : (∑ j : Fin C.gates.length, f j) + 2 = 2 * Kg.card + Pg.card := by
      have hplus : ∀ j : Fin C.gates.length,
          f j + (if j.val = 0 ∨ j.val = 1 then 1 else 0) =
          (if j ∈ Kg then 2 else 0) + (if j ∈ Pg then 1 else 0) := by
        intro j
        simp only [f]
        by_cases h01 : j.val = 0 ∨ j.val = 1
        · have hjK : j ∈ Kg := by
            rcases h01 with h0v | h1v
            · have : j = ⟨0, hlen0⟩ := Fin.ext h0v; rw [this]; exact hj0_mem
            · have : j = ⟨1, hlen1⟩ := Fin.ext h1v; rw [this]; exact hj1_mem
          have hjnotP : j ∉ Pg := Finset.disjoint_left.mp hdisj hjK
          simp [h01, hjK, hjnotP]
        · by_cases hjK : j ∈ Kg
          · have hjnotP : j ∉ Pg := Finset.disjoint_left.mp hdisj hjK
            simp [h01, hjK, hjnotP]
          · by_cases hjP : j ∈ Pg <;> simp [h01, hjK, hjP]
      have hsum1 : ∑ j : Fin C.gates.length, (f j + (if j.val = 0 ∨ j.val = 1 then 1 else 0)) =
          ∑ j : Fin C.gates.length, ((if j ∈ Kg then 2 else 0) + (if j ∈ Pg then 1 else 0)) :=
        Finset.sum_congr rfl fun j _ => hplus j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum1
      have h01_sum : ∑ j : Fin C.gates.length, (if j.val = 0 ∨ j.val = 1 then 1 else 0) = 2 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
        have hfilt : Finset.univ.filter (fun j : Fin C.gates.length => j.val = 0 ∨ j.val = 1) =
            {⟨0, hlen0⟩, ⟨1, hlen1⟩} := by
          ext j; simp [Fin.ext_iff]
        rw [hfilt, Finset.card_pair]
        intro h; have := congrArg Fin.val h; simp at this
      have hK_sum : ∑ j : Fin C.gates.length, (if j ∈ Kg then 2 else 0) = 2 * Kg.card := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        have : Finset.univ.filter (fun j : Fin C.gates.length => j ∈ Kg) = Kg := by ext; simp
        rw [this]; omega
      have hP_sum : ∑ j : Fin C.gates.length, (if j ∈ Pg then 1 else 0) = Pg.card := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
        have : Finset.univ.filter (fun j : Fin C.gates.length => j ∈ Pg) = Pg := by ext; simp
        rw [this]
      rw [h01_sum, hK_sum, hP_sum] at hsum1
      exact hsum1
    omega
  have hcp : 6 ≤ Kg.card + Pg.card := by omega
  have hcount : st.2.length +
      ((Finset.range C.gates.length).filter fun j => isKilledGate st.1 C.gates j = true).card ≤
      C.gates.length :=
    stateAt_gates_count C.gates hnorm C.gates.length le_rfl
  set killed := (Finset.range C.gates.length).filter fun j => isKilledGate st.1 C.gates j = true
  have hdisj : Disjoint Kg Pg := by
    rw [Finset.disjoint_left]
    intro j h1m h2m
    simp only [Kg, Pg, Finset.mem_filter, Finset.mem_univ, true_and] at h1m h2m
    rw [h1m] at h2m; exact Bool.noConfusion h2m.1
  have hkilled_ge : Kg.card + Pg.card ≤ killed.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have himg_sub : (Kg ∪ Pg).image Fin.val ⊆ killed := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_union] at hx
      rcases hx with ⟨j, hj, rfl⟩
      simp only [killed, Finset.mem_filter, Finset.mem_range, isKilledGate, Bool.or_eq_true]
      refine ⟨j.isLt, ?_⟩
      have hgd : C.gates.getD j.val ⟨.and, []⟩ = C.gates[j.val] := List.getD_eq_getElem _ _ j.isLt
      rw [hgd]
      rcases hj with hjK | hjP
      · simp only [Kg, Finset.mem_filter, Finset.mem_univ, true_and] at hjK
        exact Or.inl hjK
      · simp only [Pg, Finset.mem_filter, Finset.mem_univ, true_and] at hjP
        exact Or.inr hjP.2
    have hcard_img : ((Kg ∪ Pg).image Fin.val).card = (Kg ∪ Pg).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    rw [← hcard_img]
    exact Finset.card_le_card himg_sub
  have hgs_len : st.2.length ≤ 6 := by
    simp only [Circuit.size] at hsize
    omega
  cases hro : st.1.getD C.output (.const false) with
  | const _ =>
    rw [hro] at hout_not_const; exact Bool.noConfusion hout_not_const
  | wire u =>
    have hlt_out : C.output < 9 + C.gates.length := by simp [Circuit.size] at hout; omega
    have hu_lt : u < 7 + st.2.length := by
      have hmem : st.1.getD C.output (.const false) ∈ st.1 := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
      have h := hreps _ hmem
      rw [hro] at h
      exact h
    refine ⟨st.2, u, hv, hgs_len, hu_lt, fun y => ?_⟩
    have h := hev_final y C.output hlt_out
    rw [hro] at h
    simp only [Rep.eval] at h
    rw [h]
    change C.eval (List.ofFn (emb7 y)) = f7 y
    rw [heval, pm3_emb7]

def shiftWire (d w : ℕ) : ℕ := if w < d then w else w - 1

lemma shiftWire_of_lt {d w : ℕ} (h : w < d) : shiftWire d w = w := if_pos h

def shiftGate (d : ℕ) : SGate → SGate
  | .not a => .not (shiftWire d a)
  | .and a b => .and (shiftWire d a) (shiftWire d b)
  | .or a b => .or (shiftWire d a) (shiftWire d b)

def eraseGate (n : ℕ) (gs : List SGate) (j : ℕ) : List SGate :=
  gs.take j ++ (gs.drop (j + 1)).map (shiftGate (n + j))

lemma shiftWire_lt {d w k : ℕ} (hw : w < k + 1) (hne : w ≠ d) (hd : d ≤ k) :
    shiftWire d w < k := by
  simp only [shiftWire]
  split <;> omega

lemma shiftWire_ne {d a b : ℕ} (hab : a ≠ b) (ha : a ≠ d) (hb : b ≠ d) :
    shiftWire d a ≠ shiftWire d b := by
  simp only [shiftWire]
  split <;> split <;> omega

lemma eraseGate_valid {n : ℕ} (gs : List SGate) (hv : SValid n gs) (j : ℕ) (hj : j < gs.length)
    (hunused : ∀ k : Fin gs.length, n + j ∉ gs[k.val].inputs) :
    SValid n (eraseGate n gs j) := by
  intro idx hidx
  have hlen : (eraseGate n gs j).length = gs.length - 1 := by
    simp [eraseGate, List.length_take, List.length_drop]; omega
  by_cases hilt : idx < j
  · have hget : (eraseGate n gs j)[idx] = gs[idx] := by
      simp only [eraseGate]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    simpa [hget] using hv idx (by omega)
  · have hi_lt : idx + 1 < gs.length := by omega
    have hget : (eraseGate n gs j)[idx] = shiftGate (n + j) gs[idx + 1] := by
      simp only [eraseGate]
      have htl : (gs.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega)]
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_drop, htl]
      congr 2; omega
    have hv_old := hv (idx + 1) hi_lt
    have hun := hunused ⟨idx + 1, hi_lt⟩
    simp only [hget]
    cases hg : gs[idx + 1] with
    | not a =>
      simp only [hg] at hv_old hun
      simp only [SGate.inputs, List.mem_singleton] at hun
      simp only [shiftGate]
      exact shiftWire_lt (by omega) (Ne.symm hun) (by omega)
    | and a b =>
      simp only [hg] at hv_old hun
      simp only [SGate.inputs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
      simp only [shiftGate]
      exact ⟨shiftWire_ne hv_old.1 (Ne.symm hun.1) (Ne.symm hun.2),
        shiftWire_lt (by omega) (Ne.symm hun.1) (by omega),
        shiftWire_lt (by omega) (Ne.symm hun.2) (by omega)⟩
    | or a b =>
      simp only [hg] at hv_old hun
      simp only [SGate.inputs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
      simp only [shiftGate]
      exact ⟨shiftWire_ne hv_old.1 (Ne.symm hun.1) (Ne.symm hun.2),
        shiftWire_lt (by omega) (Ne.symm hun.1) (by omega),
        shiftWire_lt (by omega) (Ne.symm hun.2) (by omega)⟩

lemma eraseGate_eval {n : ℕ} (gs : List SGate) (hv : SValid n gs) (j : ℕ) (hj : j < gs.length)
    (hunused : ∀ k : Fin gs.length, n + j ∉ gs[k.val].inputs)
    (x : List Bool) (hx : x.length = n) :
    ∀ w < n + gs.length, w ≠ n + j →
      (swires (eraseGate n gs j) x).getD (shiftWire (n + j) w) false = (swires gs x).getD w false := by
  have hv' := eraseGate_valid gs hv j hj hunused
  have hlen : (eraseGate n gs j).length = gs.length - 1 := by
    simp [eraseGate, List.length_take, List.length_drop]; omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwlt hwne
    by_cases hwn : w < n
    · have hsw : shiftWire (n + j) w = w := shiftWire_of_lt (by omega)
      rw [hsw, swires_getD_lt _ _ _ (by omega), swires_getD_lt _ _ _ (by omega)]
    · by_cases hwj : w < n + j
      · have hsw : shiftWire (n + j) w = w := shiftWire_of_lt hwj
        set k := w - n
        have hk : k < j := by omega
        have hwk : w = n + k := by omega
        rw [hsw, hwk, swires_getD_gate (eraseGate n gs j) hv' x hx k (by omega)]
        rw [swires_getD_gate gs hv x hx k (by omega)]
        have hget : (eraseGate n gs j)[k] = gs[k] := by
          simp only [eraseGate]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [hget]
        have hvk := hv k (by omega)
        cases hg : gs[k] with
        | not a =>
          simp only [hg] at hvk
          have ha := ih a (by omega) (by omega) (by omega)
          have hswa : shiftWire (n + j) a = a := shiftWire_of_lt (by omega)
          rw [hswa] at ha
          simp only [SGate.eval, ha]
        | and a b =>
          simp only [hg] at hvk
          have ha := ih a (by omega) (by omega) (by omega)
          have hb := ih b (by omega) (by omega) (by omega)
          have hswa : shiftWire (n + j) a = a := shiftWire_of_lt (by omega)
          have hswb : shiftWire (n + j) b = b := shiftWire_of_lt (by omega)
          rw [hswa] at ha; rw [hswb] at hb
          simp only [SGate.eval, ha, hb]
        | or a b =>
          simp only [hg] at hvk
          have ha := ih a (by omega) (by omega) (by omega)
          have hb := ih b (by omega) (by omega) (by omega)
          have hswa : shiftWire (n + j) a = a := shiftWire_of_lt (by omega)
          have hswb : shiftWire (n + j) b = b := shiftWire_of_lt (by omega)
          rw [hswa] at ha; rw [hswb] at hb
          simp only [SGate.eval, ha, hb]
      · set k := w - n - 1
        have hkj : j ≤ k := by omega
        have hklt : k < (eraseGate n gs j).length := by omega
        have hwk : w = n + (k + 1) := by omega
        have hsw : shiftWire (n + j) w = n + k := by
          simp only [shiftWire, if_neg hwj]; omega
        rw [hsw, hwk, swires_getD_gate (eraseGate n gs j) hv' x hx k hklt]
        rw [swires_getD_gate gs hv x hx (k + 1) (by omega)]
        have hget : (eraseGate n gs j)[k] = shiftGate (n + j) gs[k + 1] := by
          simp only [eraseGate]
          have htl : (gs.take j).length = j := by rw [List.length_take, Nat.min_eq_left (by omega)]
          rw [List.getElem_append_right (by omega)]
          simp only [List.getElem_map, List.getElem_drop, htl]
          congr 2; omega
        rw [hget]
        have hvk := hv (k + 1) (by omega)
        have hun := hunused ⟨k + 1, by omega⟩
        cases hg : gs[k + 1] with
        | not a =>
          simp only [hg] at hvk hun
          simp only [SGate.inputs, List.mem_singleton] at hun
          have ha := ih a (by omega) (by omega) (Ne.symm hun)
          simp only [shiftGate, SGate.eval, ha]
        | and a b =>
          simp only [hg] at hvk hun
          simp only [SGate.inputs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
          have ha := ih a (by omega) (by omega) (Ne.symm hun.1)
          have hb := ih b (by omega) (by omega) (Ne.symm hun.2)
          simp only [shiftGate, SGate.eval, ha, hb]
        | or a b =>
          simp only [hg] at hvk hun
          simp only [SGate.inputs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
          have ha := ih a (by omega) (by omega) (Ne.symm hun.1)
          have hb := ih b (by omega) (by omega) (Ne.symm hun.2)
          simp only [shiftGate, SGate.eval, ha, hb]

lemma unused_input_indep {n : ℕ} (gs : List SGate) (hv : SValid n gs) (v : Fin n)
    (hunused : ∀ j : Fin gs.length, v.val ∉ gs[j.val].inputs)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ v → x i = y i) :
    ∀ w < n + gs.length, w ≠ v.val →
      (swires gs (List.ofFn x)).getD w false = (swires gs (List.ofFn y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwlt hwne
    by_cases hwn : w < n
    · rw [swires_getD_lt _ _ _ (by simp; omega), swires_getD_lt _ _ _ (by simp; omega)]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      exact hxy ⟨w, hwn⟩ (fun h => hwne (congrArg Fin.val h))
    · set j := w - n
      have hj : j < gs.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj, swires_getD_gate gs hv _ (by simp) j hj, swires_getD_gate gs hv _ (by simp) j hj]
      have hvj := hv j hj
      have hun := hunused ⟨j, hj⟩
      cases hg : gs[j] with
      | not a =>
        simp only [hg] at hvj hun
        simp only [SGate.inputs, List.mem_singleton] at hun
        simp only [SGate.eval, ih a (by omega) (by omega) (Ne.symm hun)]
      | and a b =>
        simp only [hg] at hvj hun
        simp only [SGate.inputs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
        simp only [SGate.eval, ih a (by omega) (by omega) (Ne.symm hun.1),
          ih b (by omega) (by omega) (Ne.symm hun.2)]
      | or a b =>
        simp only [hg] at hvj hun
        simp only [SGate.inputs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
        simp only [SGate.eval, ih a (by omega) (by omega) (Ne.symm hun.1),
          ih b (by omega) (by omega) (Ne.symm hun.2)]

inductive MForm (n : ℕ) where
  | var (v : Fin n)
  | and (l r : MForm n)
  | or (l r : MForm n)

def MForm.eval {n : ℕ} (x : Fin n → Bool) : MForm n → Bool
  | .var v => x v
  | .and l r => l.eval x && r.eval x
  | .or l r => l.eval x || r.eval x

def MForm.leaves {n : ℕ} : MForm n → ℕ
  | .var _ => 1
  | .and l r => l.leaves + r.leaves
  | .or l r => l.leaves + r.leaves

def MForm.varSet {n : ℕ} : MForm n → Finset (Fin n)
  | .var v => {v}
  | .and l r => l.varSet ∪ r.varSet
  | .or l r => l.varSet ∪ r.varSet

lemma MForm.leaves_pos {n : ℕ} (T : MForm n) : 1 ≤ T.leaves := by
  induction T with
  | var _ => exact le_rfl
  | and _ _ ihl _ => simp [MForm.leaves]; omega
  | or _ _ ihl _ => simp [MForm.leaves]; omega

lemma MForm.card_varSet_le_leaves {n : ℕ} (T : MForm n) : T.varSet.card ≤ T.leaves := by
  induction T with
  | var _ => simp [MForm.varSet, MForm.leaves]
  | and l r ihl ihr =>
    simp only [MForm.varSet, MForm.leaves]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihl ihr)
  | or l r ihl ihr =>
    simp only [MForm.varSet, MForm.leaves]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihl ihr)

lemma MForm.eval_mono {n : ℕ} (T : MForm n) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) (hx : T.eval x = true) : T.eval y = true := by
  induction T with
  | var v => exact hxy v hx
  | and l r ihl ihr =>
    simp only [MForm.eval, Bool.and_eq_true] at hx ⊢
    exact ⟨ihl hx.1, ihr hx.2⟩
  | or l r ihl ihr =>
    simp only [MForm.eval, Bool.or_eq_true] at hx ⊢
    rcases hx with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

lemma MForm.eval_eq_of_eq_on_varSet {n : ℕ} (T : MForm n) {x y : Fin n → Bool}
    (hxy : ∀ v ∈ T.varSet, x v = y v) : T.eval x = T.eval y := by
  induction T with
  | var v => exact hxy v (by simp [MForm.varSet])
  | and l r ihl ihr =>
    simp only [MForm.eval]
    rw [ihl (fun v hv => hxy v (by simp [MForm.varSet, hv])),
        ihr (fun v hv => hxy v (by simp [MForm.varSet, hv]))]
  | or l r ihl ihr =>
    simp only [MForm.eval]
    rw [ihl (fun v hv => hxy v (by simp [MForm.varSet, hv])),
        ihr (fun v hv => hxy v (by simp [MForm.varSet, hv]))]

def essVars {n : ℕ} (g : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ x : Fin n → Bool, g x ≠ g (Function.update x v (!x v))

lemma MForm.essVars_subset_varSet {n : ℕ} (T : MForm n) :
    essVars T.eval ⊆ T.varSet := by
  intro v hv
  simp only [essVars, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨x, hx⟩ := hv
  by_contra hnot
  apply hx
  apply MForm.eval_eq_of_eq_on_varSet
  intro u hu
  have huv : u ≠ v := fun h => hnot (h ▸ hu)
  simp [Function.update, huv]

lemma MForm.card_essVars_le_leaves {n : ℕ} (T : MForm n) :
    (essVars T.eval).card ≤ T.leaves :=
  le_trans (Finset.card_le_card T.essVars_subset_varSet) T.card_varSet_le_leaves

def formsAt {n : ℕ} (hn : 0 < n) (gs : List SGate) : ℕ → List (MForm n)
  | 0 => List.ofFn MForm.var
  | k + 1 =>
    let prev := formsAt hn gs k
    match gs[k]? with
    | none => prev
    | some g =>
      let d := MForm.var ⟨0, hn⟩
      let f := match g with
        | .and a b => MForm.and (prev.getD a d) (prev.getD b d)
        | .or a b => MForm.or (prev.getD a d) (prev.getD b d)
        | .not a => prev.getD a d
      prev ++ [f]

lemma formsAt_length {n : ℕ} (hn : 0 < n) (gs : List SGate) (k : ℕ) (hk : k ≤ gs.length) :
    (formsAt hn gs k).length = n + k := by
  induction k with
  | zero => simp [formsAt]
  | succ k ih =>
    have hlt : k < gs.length := by omega
    simp only [formsAt, List.getElem?_eq_getElem hlt, List.length_append, List.length_singleton]
    rw [ih (by omega)]; omega

lemma formsAt_length_mono {n : ℕ} (hn : 0 < n) (gs : List SGate) (a b : ℕ) (hab : a ≤ b) :
    (formsAt hn gs a).length ≤ (formsAt hn gs b).length := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    rw [ha]
  | succ b ih =>
    by_cases h : a ≤ b
    · have := ih h
      simp only [formsAt]
      cases gs[b]? with
      | none => exact this
      | some g => simp only [List.length_append, List.length_singleton]; omega
    · have ha : a = b + 1 := by omega
      rw [ha]

lemma formsAt_mono {n : ℕ} (hn : 0 < n) (gs : List SGate) {k₁ k₂ w : ℕ}
    (hle : k₁ ≤ k₂) (hw : w < (formsAt hn gs k₁).length) :
    (formsAt hn gs k₂).getD w (MForm.var ⟨0, hn⟩) =
      (formsAt hn gs k₁).getD w (MForm.var ⟨0, hn⟩) := by
  induction k₂ with
  | zero =>
    have hk : k₁ = 0 := by omega
    rw [hk]
  | succ k ih =>
    by_cases h : k₁ ≤ k
    · have hw' : w < (formsAt hn gs k).length :=
        lt_of_lt_of_le hw (formsAt_length_mono hn gs k₁ k h)
      rw [← ih h]
      simp only [formsAt]
      cases gs[k]? with
      | none => rfl
      | some g => exact getD_append_left _ _ _ _ hw'
    · have hk : k₁ = k + 1 := by omega
      rw [hk]

lemma formsAt_eval {n : ℕ} (hn : 0 < n) (gs : List SGate) (hv : SValid n gs)
    (hbin : ∀ j : Fin gs.length, gs[j.val].isBin = true) (k : ℕ) (hk : k ≤ gs.length) :
    ∀ x : Fin n → Bool, ∀ w < n + k,
      ((formsAt hn gs k).getD w (MForm.var ⟨0, hn⟩)).eval x =
        (swires gs (List.ofFn x)).getD w false := by
  induction k with
  | zero =>
    intro x w hw
    simp only [formsAt]
    rw [swires_getD_lt _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    simp [MForm.eval]
  | succ k ih =>
    have hlt : k < gs.length := by omega
    intro x w hw
    have hprev_len : (formsAt hn gs k).length = n + k := formsAt_length hn gs k (by omega)
    by_cases hwlt : w < n + k
    · rw [formsAt_mono hn gs (Nat.le_succ k) (by omega)]
      exact ih (by omega) x w hwlt
    · have hweq : w = n + k := by omega
      subst hweq
      simp only [formsAt, List.getElem?_eq_getElem hlt]
      rw [getD_append_right _ _ _ _ (by omega)]
      simp only [hprev_len, Nat.sub_self, List.getD_cons_zero]
      rw [swires_getD_gate gs hv (List.ofFn x) (by simp) k hlt]
      have hvk := hv k hlt
      have hbk := hbin ⟨k, hlt⟩
      cases hg : gs[k] with
      | not _ => simp [hg, SGate.isBin] at hbk
      | and a b =>
        simp only [hg] at hvk
        simp only [MForm.eval, SGate.eval]
        rw [ih (by omega) x a hvk.2.1, ih (by omega) x b hvk.2.2]
      | or a b =>
        simp only [hg] at hvk
        simp only [MForm.eval, SGate.eval]
        rw [ih (by omega) x a hvk.2.1, ih (by omega) x b hvk.2.2]

lemma extract_monotone_formula {n : ℕ} (hn : 0 < n) (gs : List SGate) (out : ℕ)
    (hv : SValid n gs) (hout_ge : n ≤ out) (hout_lt : out < n + gs.length)
    (hbin : ∀ j : Fin gs.length, gs[j.val].isBin = true)
    (hdeg_gate : ∀ j : Fin gs.length,
      (∑ m : Fin gs.length, if n + j.val ∈ gs[m.val].inputs then 1 else 0) +
      (if n + j.val = out then 1 else 0) = 1) :
    ∃ T : MForm n,
      (∀ x : Fin n → Bool, T.eval x = (swires gs (List.ofFn x)).getD out false) ∧
      T.leaves = ∑ v ∈ Finset.range n, ∑ m : Fin gs.length, if v ∈ gs[m.val].inputs then 1 else 0 := by
  let d := MForm.var ⟨0, hn⟩
  set finalForms := formsAt hn gs gs.length
  let remdeg (k w : ℕ) : ℕ :=
    (∑ m : Fin gs.length, if k ≤ m.val ∧ w ∈ gs[m.val].inputs then 1 else 0) +
    (if w = out then 1 else 0)
  let phi (k : ℕ) : ℕ :=
    ∑ w ∈ Finset.range (n + k), remdeg k w * (finalForms.getD w d).leaves
  have hphi_step : ∀ k, k < gs.length → phi (k + 1) = phi k := by
    intro k hk
    have hvk := hv k hk
    have hbk := hbin ⟨k, hk⟩
    have hfk_len : (formsAt hn gs k).length = n + k := formsAt_length hn gs k (by omega)
    have hmono_k : ∀ w < n + k, finalForms.getD w d = (formsAt hn gs k).getD w d := fun w hw =>
      formsAt_mono hn gs (by omega : k ≤ gs.length) (by omega)
    have hmono_k1 : finalForms.getD (n + k) d =
        (formsAt hn gs (k + 1)).getD (n + k) d :=
      formsAt_mono hn gs (by omega : k + 1 ≤ gs.length)
        (by rw [formsAt_length hn gs (k + 1) (by omega)]; omega)
    have hrem_new : remdeg (k + 1) (n + k) = 1 := by
      have hno_earlier : ∀ m : Fin gs.length, m.val < k + 1 → n + k ∉ gs[m.val].inputs := by
        intro m hm hin
        have hvm := hv m.val m.isLt
        cases hgm : gs[m.val] with
        | not a => simp [hgm, SGate.inputs] at hvm hin; omega
        | and a b => simp [hgm, SGate.inputs] at hvm hin; rcases hin with rfl | rfl <;> omega
        | or a b => simp [hgm, SGate.inputs] at hvm hin; rcases hin with rfl | rfl <;> omega
      have hsum_eq : (∑ m : Fin gs.length, if k + 1 ≤ m.val ∧ n + k ∈ gs[m.val].inputs then 1 else 0) =
          ∑ m : Fin gs.length, if n + k ∈ gs[m.val].inputs then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro m _
        by_cases hmk : k + 1 ≤ m.val
        · simp [hmk]
        · have hne := hno_earlier m (by omega)
          simp [hne]
      simp only [remdeg, hsum_eq]
      exact hdeg_gate ⟨k, hk⟩
    have hstep_ab : ∀ a b, a ≠ b → a < n + k → b < n + k →
        gs[k].inputs = [a, b] →
        (finalForms.getD (n + k) d).leaves =
          (finalForms.getD a d).leaves + (finalForms.getD b d).leaves →
        phi (k + 1) = phi k := by
      intro a b hab ha hb hgin hleaves
      simp only [phi]
      rw [← Nat.add_assoc, Finset.sum_range_succ, hrem_new, one_mul, hleaves]
      have hrem_diff : ∀ w ∈ Finset.range (n + k),
          remdeg k w = remdeg (k + 1) w + (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
        intro w _
        simp only [remdeg]
        have hsplit : (∑ m : Fin gs.length, if k ≤ m.val ∧ w ∈ gs[m.val].inputs then 1 else 0) =
            (∑ m : Fin gs.length, if k + 1 ≤ m.val ∧ w ∈ gs[m.val].inputs then 1 else 0) +
            (if w ∈ gs[k].inputs then 1 else 0) := by
          have hpt : ∀ m : Fin gs.length,
              (if k ≤ m.val ∧ w ∈ gs[m.val].inputs then 1 else 0) =
              (if k + 1 ≤ m.val ∧ w ∈ gs[m.val].inputs then 1 else 0) +
              (if m = ⟨k, hk⟩ ∧ w ∈ gs[m.val].inputs then 1 else 0) := by
            intro m
            by_cases hm : m.val = k
            · have hme : m = ⟨k, hk⟩ := Fin.ext hm
              rw [hme]; simp
            · have hne : m ≠ ⟨k, hk⟩ := fun h => hm (congrArg Fin.val h)
              by_cases hge : k ≤ m.val
              · have : k + 1 ≤ m.val := by omega
                simp [hge, this, hne]
              · have : ¬ k + 1 ≤ m.val := by omega
                simp [hge, this, hne]
          rw [Finset.sum_congr rfl (fun m _ => hpt m), Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single ⟨k, hk⟩]
          · simp
          · intro m _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsplit, hgin]
        by_cases hwa : w = a
        · subst hwa; simp [hab]; omega
        · by_cases hwb : w = b
          · subst hwb; simp [hwa]; omega
          · simp [hwa, hwb]
      have hsum_k : ∑ w ∈ Finset.range (n + k), remdeg k w * (finalForms.getD w d).leaves =
          (∑ w ∈ Finset.range (n + k), remdeg (k + 1) w * (finalForms.getD w d).leaves) +
          (∑ w ∈ Finset.range (n + k), (if w = a then 1 else 0) * (finalForms.getD w d).leaves) +
          (∑ w ∈ Finset.range (n + k), (if w = b then 1 else 0) * (finalForms.getD w d).leaves) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        rw [hrem_diff w hw, add_mul, add_mul]
      have hsa : ∑ w ∈ Finset.range (n + k), (if w = a then 1 else 0) * (finalForms.getD w d).leaves =
          (finalForms.getD a d).leaves := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro w _ hwa; simp [hwa]
        · intro h; exact absurd (Finset.mem_range.mpr ha) h
      have hsb : ∑ w ∈ Finset.range (n + k), (if w = b then 1 else 0) * (finalForms.getD w d).leaves =
          (finalForms.getD b d).leaves := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro w _ hwb; simp [hwb]
        · intro h; exact absurd (Finset.mem_range.mpr hb) h
      rw [hsum_k, hsa, hsb]
      omega
    cases hgk : gs[k] with
    | not _ => simp [hgk, SGate.isBin] at hbk
    | and a b =>
      simp only [hgk] at hvk
      apply hstep_ab a b hvk.1 hvk.2.1 hvk.2.2 (by simp [hgk, SGate.inputs])
      rw [hmono_k1, hmono_k a hvk.2.1, hmono_k b hvk.2.2]
      simp only [formsAt, List.getElem?_eq_getElem hk, hgk]
      rw [getD_append_right _ _ _ _ (by omega)]
      simp only [hfk_len, Nat.sub_self, List.getD_cons_zero, MForm.leaves, d]
    | or a b =>
      simp only [hgk] at hvk
      apply hstep_ab a b hvk.1 hvk.2.1 hvk.2.2 (by simp [hgk, SGate.inputs])
      rw [hmono_k1, hmono_k a hvk.2.1, hmono_k b hvk.2.2]
      simp only [formsAt, List.getElem?_eq_getElem hk, hgk]
      rw [getD_append_right _ _ _ _ (by omega)]
      simp only [hfk_len, Nat.sub_self, List.getD_cons_zero, MForm.leaves, d]
  have hphi_eq : phi gs.length = phi 0 := by
    have haux : ∀ k, k ≤ gs.length → phi k = phi 0 := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih => rw [hphi_step k (by omega), ih (by omega)]
    exact haux gs.length le_rfl
  have hphi0 : phi 0 = ∑ v ∈ Finset.range n, ∑ m : Fin gs.length, if v ∈ gs[m.val].inputs then 1 else 0 := by
    simp only [phi, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro v hv
    have hvlt : v < n := Finset.mem_range.mp hv
    have hfv : (finalForms.getD v d).leaves = 1 := by
      rw [formsAt_mono hn gs (Nat.zero_le _) (by simp [formsAt, hvlt])]
      simp only [formsAt]
      rw [List.getD_eq_getElem _ _ (by simp [hvlt])]
      simp only [List.getElem_ofFn, MForm.leaves]
    have hne : v ≠ out := by omega
    rw [hfv, mul_one]
    simp only [remdeg, if_neg hne, add_zero, Nat.zero_le, true_and]
  have hphis : phi gs.length = (finalForms.getD out d).leaves := by
    simp only [phi]
    rw [Finset.sum_eq_single out]
    · have hzero : ∑ m : Fin gs.length, (if gs.length ≤ m.val ∧ out ∈ gs[m.val].inputs then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        have : ¬ gs.length ≤ m.val := by omega
        simp [this]
      simp only [remdeg, hzero, zero_add, ite_true, one_mul]
    · intro w _ hne
      have hzero : ∑ m : Fin gs.length, (if gs.length ≤ m.val ∧ w ∈ gs[m.val].inputs then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        have : ¬ gs.length ≤ m.val := by omega
        simp [this]
      simp only [remdeg, hzero, if_neg hne, add_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr hout_lt) h
  refine ⟨finalForms.getD out d, ?_, by rw [← hphis, hphi_eq, hphi0]⟩
  intro x
  exact formsAt_eval hn gs hv hbin gs.length le_rfl x out hout_lt

def f7_pi1 : Fin 7 → Bool := fun i => i == 0 || i == 2 || i == 6
def f7_pi2 : Fin 7 → Bool := fun i => i == 1 || i == 2 || i == 5
def f7_pi3 : Fin 7 → Bool := fun i => i == 1 || i == 3 || i == 4

def f7_imp_list : List (Finset (Fin 7)) :=
  [{0, 1}, {1, 2}, {2, 3}, {2, 4}, {1, 6}, {0, 3, 5}, {0, 4, 5}, {3, 5, 6}, {4, 5, 6}]

def zeroOfClause (c : Finset (Fin 7)) : Fin 7 → Bool := fun i => !(decide (i ∈ c))

lemma f7_all_vars_ess : ∀ v : Fin 7, ∃ y : Fin 7 → Bool, f7 y ≠ f7 (Function.update y v (!y v)) := by
  intro v
  fin_cases v
  · exact ⟨f7_pi1, by decide⟩
  · exact ⟨f7_pi2, by decide⟩
  · exact ⟨f7_pi1, by decide⟩
  · exact ⟨f7_pi3, by decide⟩
  · exact ⟨f7_pi3, by decide⟩
  · exact ⟨f7_pi2, by decide⟩
  · exact ⟨f7_pi1, by decide⟩

lemma f7_not_var (v : Fin 7) : ¬ (∀ y : Fin 7 → Bool, y v = f7 y) := by
  intro h
  have h1 := h (fun i => decide (i = v))
  have h2 : f7 (fun i => decide (i = v)) = false := by
    revert v; decide
  simp [h2] at h1

lemma f7_true_ge_pi : ∀ y : Fin 7 → Bool, f7 y = true →
    (∀ i, f7_pi1 i = true → y i = true) ∨
    (∀ i, f7_pi2 i = true → y i = true) ∨
    (∀ i, f7_pi3 i = true → y i = true) := by
  intro y hy
  simp only [f7, Bool.or_eq_true, Bool.and_eq_true] at hy
  rcases hy with (⟨⟨h0, h2⟩, h6⟩ | ⟨⟨h1, h2⟩, h5⟩) | ⟨⟨h1, h3⟩, h4⟩
  · left; intro i hi; fin_cases i <;> simp_all [f7_pi1]
  · right; left; intro i hi; fin_cases i <;> simp_all [f7_pi2]
  · right; right; intro i hi; fin_cases i <;> simp_all [f7_pi3]

lemma f7_pi_minimal :
    (f7 f7_pi1 = true ∧ ∀ v : Fin 7, f7_pi1 v = true → f7 (Function.update f7_pi1 v false) = false) ∧
    (f7 f7_pi2 = true ∧ ∀ v : Fin 7, f7_pi2 v = true → f7 (Function.update f7_pi2 v false) = false) ∧
    (f7 f7_pi3 = true ∧ ∀ v : Fin 7, f7_pi3 v = true → f7 (Function.update f7_pi3 v false) = false) := by
  decide

lemma f7_false_le_clause : ∀ y : Fin 7 → Bool, f7 y = false →
    ∃ c ∈ f7_imp_list, ∀ i, y i = true → zeroOfClause c i = true := by
  intro y hy
  simp only [f7, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hy
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hle_of : ∀ (c : Finset (Fin 7)), c ∈ f7_imp_list → (∀ v ∈ c, y v = false) →
      ∃ c' ∈ f7_imp_list, ∀ i, y i = true → zeroOfClause c' i = true := by
    intro c hc hall
    refine ⟨c, hc, fun i hi => ?_⟩
    simp only [zeroOfClause, Bool.not_eq_true', decide_eq_false_iff_not]
    intro hic
    have := hall i hic; rw [hi] at this; exact Bool.noConfusion this
  rcases h1 with (hy0 | hy2) | hy6
  · rcases h2 with (hy1 | hy2) | hy5
    · exact hle_of {0, 1} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
    · rcases h3 with (hy1 | hy3) | hy4
      · exact hle_of {0, 1} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      · exact hle_of {2, 3} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      · exact hle_of {2, 4} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
    · rcases h3 with (hy1 | hy3) | hy4
      · exact hle_of {0, 1} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      · exact hle_of {0, 3, 5} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> assumption)
      · exact hle_of {0, 4, 5} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> assumption)
  · rcases h3 with (hy1 | hy3) | hy4
    · exact hle_of {1, 2} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
    · exact hle_of {2, 3} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
    · exact hle_of {2, 4} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
  · rcases h2 with (hy1 | hy2) | hy5
    · exact hle_of {1, 6} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
    · rcases h3 with (hy1 | hy3) | hy4
      · exact hle_of {1, 6} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      · exact hle_of {2, 3} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      · exact hle_of {2, 4} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
    · rcases h3 with (hy1 | hy3) | hy4
      · exact hle_of {1, 6} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      · exact hle_of {3, 5, 6} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> assumption)
      · exact hle_of {4, 5, 6} (by simp [f7_imp_list]) (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> assumption)

lemma f7_clause_minimal : ∀ c ∈ f7_imp_list,
    f7 (zeroOfClause c) = false ∧
    ∀ v ∈ c, f7 (Function.update (zeroOfClause c) v true) = true := by
  intro c hc
  simp only [f7_imp_list, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by decide, fun v hv => by fin_cases v <;> simp_all [f7, zeroOfClause]⟩

lemma f7_ess_card : (essVars f7).card = 7 := by
  have huniv : essVars f7 = Finset.univ := by
    ext v
    simp [essVars, f7_all_vars_ess v]
  rw [huniv]; simp

lemma no_mform7_le_7 (T : MForm 7) (hlev : T.leaves ≤ 7) :
    ¬ (∀ y : Fin 7 → Bool, T.eval y = f7 y) := by
  intro hev
  cases T with
  | var v => exact f7_not_var v hev
  | or l r =>
    simp only [MForm.leaves] at hlev
    have hl_le : l.leaves ≤ 6 := by have := r.leaves_pos; omega
    have hr_le : r.leaves ≤ 6 := by have := l.leaves_pos; omega
    have hl_le_f : ∀ y, l.eval y = true → f7 y = true := by
      intro y h; rw [← hev y]; simp [MForm.eval, h]
    have hr_le_f : ∀ y, r.eval y = true → f7 y = true := by
      intro y h; rw [← hev y]; simp [MForm.eval, h]
    have hl_ne : ∃ y, f7 y = true ∧ l.eval y = false := by
      by_contra h
      push_neg at h
      have heq : ∀ y, l.eval y = f7 y := by
        intro y
        cases hf : f7 y with
        | true => cases hl : l.eval y with | true => rfl | false => exact absurd hl (h y hf)
        | false => cases hl : l.eval y with | false => rfl | true => have := hl_le_f y hl; rw [hf] at this; exact Bool.noConfusion this
      have hcard : (essVars l.eval).card = 7 := by
        have : essVars l.eval = essVars f7 := by congr 1; funext y; exact heq y
        rw [this, f7_ess_card]
      have := l.card_essVars_le_leaves
      omega
    have hr_ne : ∃ y, f7 y = true ∧ r.eval y = false := by
      by_contra h
      push_neg at h
      have heq : ∀ y, r.eval y = f7 y := by
        intro y
        cases hf : f7 y with
        | true => cases hr : r.eval y with | true => rfl | false => exact absurd hr (h y hf)
        | false => cases hr : r.eval y with | false => rfl | true => have := hr_le_f y hr; rw [hf] at this; exact Bool.noConfusion this
      have hcard : (essVars r.eval).card = 7 := by
        have : essVars r.eval = essVars f7 := by congr 1; funext y; exact heq y
        rw [this, f7_ess_card]
      have := r.card_essVars_le_leaves
      omega
    have hpi_ess : ∀ (F : MForm 7) (p : Fin 7 → Bool),
        (∀ y, F.eval y = true → f7 y = true) →
        (∀ v : Fin 7, p v = true → f7 (Function.update p v false) = false) →
        F.eval p = true → ∀ v : Fin 7, p v = true → v ∈ essVars F.eval := by
      intro F p hFle hmin hFp v hv
      simp only [essVars, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨p, ?_⟩
      rw [hv, Bool.not_true, hFp]
      cases hf : F.eval (Function.update p v false) with
      | false => decide
      | true =>
        have := hFle _ hf
        rw [hmin v hv] at this; exact Bool.noConfusion this
    have hp1 : (∀ v : Fin 7, f7_pi1 v = true → v ∈ essVars l.eval) ∨
        (∀ v : Fin 7, f7_pi1 v = true → v ∈ essVars r.eval) := by
      have h := hev f7_pi1
      rw [f7_pi_minimal.1.1] at h
      simp only [MForm.eval, Bool.or_eq_true] at h
      rcases h with hl | hr
      · exact Or.inl (hpi_ess l f7_pi1 hl_le_f f7_pi_minimal.1.2 hl)
      · exact Or.inr (hpi_ess r f7_pi1 hr_le_f f7_pi_minimal.1.2 hr)
    have hp2 : (∀ v : Fin 7, f7_pi2 v = true → v ∈ essVars l.eval) ∨
        (∀ v : Fin 7, f7_pi2 v = true → v ∈ essVars r.eval) := by
      have h := hev f7_pi2
      rw [f7_pi_minimal.2.1.1] at h
      simp only [MForm.eval, Bool.or_eq_true] at h
      rcases h with hl | hr
      · exact Or.inl (hpi_ess l f7_pi2 hl_le_f f7_pi_minimal.2.1.2 hl)
      · exact Or.inr (hpi_ess r f7_pi2 hr_le_f f7_pi_minimal.2.1.2 hr)
    have hp3 : (∀ v : Fin 7, f7_pi3 v = true → v ∈ essVars l.eval) ∨
        (∀ v : Fin 7, f7_pi3 v = true → v ∈ essVars r.eval) := by
      have h := hev f7_pi3
      rw [f7_pi_minimal.2.2.1] at h
      simp only [MForm.eval, Bool.or_eq_true] at h
      rcases h with hl | hr
      · exact Or.inl (hpi_ess l f7_pi3 hl_le_f f7_pi_minimal.2.2.2 hl)
      · exact Or.inr (hpi_ess r f7_pi3 hr_le_f f7_pi_minimal.2.2.2 hr)
    have hunion : essVars l.eval ∪ essVars r.eval = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      fin_cases v
      · rcases hp1 with h | h; exact Or.inl (h 0 rfl); exact Or.inr (h 0 rfl)
      · rcases hp2 with h | h; exact Or.inl (h 1 rfl); exact Or.inr (h 1 rfl)
      · rcases hp1 with h | h; exact Or.inl (h 2 rfl); exact Or.inr (h 2 rfl)
      · rcases hp3 with h | h; exact Or.inl (h 3 rfl); exact Or.inr (h 3 rfl)
      · rcases hp3 with h | h; exact Or.inl (h 4 rfl); exact Or.inr (h 4 rfl)
      · rcases hp2 with h | h; exact Or.inl (h 5 rfl); exact Or.inr (h 5 rfl)
      · rcases hp1 with h | h; exact Or.inl (h 6 rfl); exact Or.inr (h 6 rfl)
    have hdisj : Disjoint (essVars l.eval) (essVars r.eval) := by
      have hcu := Finset.card_union_add_card_inter (essVars l.eval) (essVars r.eval)
      rw [hunion] at hcu
      have hcard7 : (Finset.univ : Finset (Fin 7)).card = 7 := by simp
      have hle1 := l.card_essVars_le_leaves
      have hle2 := r.card_essVars_le_leaves
      have hinter : (essVars l.eval ∩ essVars r.eval).card = 0 := by omega
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter)
    have hne_r : (essVars r.eval).Nonempty := by
      obtain ⟨y, hy1, hyl⟩ := hl_ne
      rcases f7_true_ge_pi y hy1 with h1 | h2 | h3
      · have hlp : l.eval f7_pi1 = false := by
          cases h : l.eval f7_pi1 with
          | false => rfl
          | true => have := l.eval_mono h1 h; rw [this] at hyl; exact Bool.noConfusion hyl
        have hrp : r.eval f7_pi1 = true := by
          have := hev f7_pi1; rw [f7_pi_minimal.1.1] at this; simp [MForm.eval, hlp] at this; exact this
        exact ⟨0, hpi_ess r f7_pi1 hr_le_f f7_pi_minimal.1.2 hrp 0 rfl⟩
      · have hlp : l.eval f7_pi2 = false := by
          cases h : l.eval f7_pi2 with
          | false => rfl
          | true => have := l.eval_mono h2 h; rw [this] at hyl; exact Bool.noConfusion hyl
        have hrp : r.eval f7_pi2 = true := by
          have := hev f7_pi2; rw [f7_pi_minimal.2.1.1] at this; simp [MForm.eval, hlp] at this; exact this
        exact ⟨1, hpi_ess r f7_pi2 hr_le_f f7_pi_minimal.2.1.2 hrp 1 rfl⟩
      · have hlp : l.eval f7_pi3 = false := by
          cases h : l.eval f7_pi3 with
          | false => rfl
          | true => have := l.eval_mono h3 h; rw [this] at hyl; exact Bool.noConfusion hyl
        have hrp : r.eval f7_pi3 = true := by
          have := hev f7_pi3; rw [f7_pi_minimal.2.2.1] at this; simp [MForm.eval, hlp] at this; exact this
        exact ⟨1, hpi_ess r f7_pi3 hr_le_f f7_pi_minimal.2.2.2 hrp 1 rfl⟩
    have hne_l : (essVars l.eval).Nonempty := by
      obtain ⟨y, hy1, hyr⟩ := hr_ne
      rcases f7_true_ge_pi y hy1 with h1 | h2 | h3
      · have hrp : r.eval f7_pi1 = false := by
          cases h : r.eval f7_pi1 with
          | false => rfl
          | true => have := r.eval_mono h1 h; rw [this] at hyr; exact Bool.noConfusion hyr
        have hlp : l.eval f7_pi1 = true := by
          have := hev f7_pi1; rw [f7_pi_minimal.1.1] at this; simp [MForm.eval, hrp] at this; exact this
        exact ⟨0, hpi_ess l f7_pi1 hl_le_f f7_pi_minimal.1.2 hlp 0 rfl⟩
      · have hrp : r.eval f7_pi2 = false := by
          cases h : r.eval f7_pi2 with
          | false => rfl
          | true => have := r.eval_mono h2 h; rw [this] at hyr; exact Bool.noConfusion hyr
        have hlp : l.eval f7_pi2 = true := by
          have := hev f7_pi2; rw [f7_pi_minimal.2.1.1] at this; simp [MForm.eval, hrp] at this; exact this
        exact ⟨1, hpi_ess l f7_pi2 hl_le_f f7_pi_minimal.2.1.2 hlp 1 rfl⟩
      · have hrp : r.eval f7_pi3 = false := by
          cases h : r.eval f7_pi3 with
          | false => rfl
          | true => have := r.eval_mono h3 h; rw [this] at hyr; exact Bool.noConfusion hyr
        have hlp : l.eval f7_pi3 = true := by
          have := hev f7_pi3; rw [f7_pi_minimal.2.2.1] at this; simp [MForm.eval, hrp] at this; exact this
        exact ⟨1, hpi_ess l f7_pi3 hl_le_f f7_pi_minimal.2.2.2 hlp 1 rfl⟩
    rcases hp2 with h2l | h2r
    · have h1l : ∀ v : Fin 7, f7_pi1 v = true → v ∈ essVars l.eval := by
        rcases hp1 with h | h
        · exact h
        · exact absurd (h 2 rfl) (Finset.disjoint_left.mp hdisj (h2l 2 rfl))
      have h3l : ∀ v : Fin 7, f7_pi3 v = true → v ∈ essVars l.eval := by
        rcases hp3 with h | h
        · exact h
        · exact absurd (h 1 rfl) (Finset.disjoint_left.mp hdisj (h2l 1 rfl))
      obtain ⟨v, hv⟩ := hne_r
      have hvl : v ∈ essVars l.eval := by
        fin_cases v
        · exact h1l 0 rfl
        · exact h2l 1 rfl
        · exact h2l 2 rfl
        · exact h3l 3 rfl
        · exact h3l 4 rfl
        · exact h2l 5 rfl
        · exact h1l 6 rfl
      exact Finset.disjoint_left.mp hdisj hvl hv
    · have h1r : ∀ v : Fin 7, f7_pi1 v = true → v ∈ essVars r.eval := by
        rcases hp1 with h | h
        · exact absurd (h2r 2 rfl) (Finset.disjoint_left.mp hdisj (h 2 rfl))
        · exact h
      have h3r : ∀ v : Fin 7, f7_pi3 v = true → v ∈ essVars r.eval := by
        rcases hp3 with h | h
        · exact absurd (h2r 1 rfl) (Finset.disjoint_left.mp hdisj (h 1 rfl))
        · exact h
      obtain ⟨v, hv⟩ := hne_l
      have hvr : v ∈ essVars r.eval := by
        fin_cases v
        · exact h1r 0 rfl
        · exact h2r 1 rfl
        · exact h2r 2 rfl
        · exact h3r 3 rfl
        · exact h3r 4 rfl
        · exact h2r 5 rfl
        · exact h1r 6 rfl
      exact Finset.disjoint_left.mp hdisj hv hvr
  | and l r =>
    simp only [MForm.leaves] at hlev
    have hl_le : l.leaves ≤ 6 := by have := r.leaves_pos; omega
    have hr_le : r.leaves ≤ 6 := by have := l.leaves_pos; omega
    have hf_le_l : ∀ y, f7 y = true → l.eval y = true := by
      intro y h; rw [← hev y] at h; simp [MForm.eval] at h; exact h.1
    have hf_le_r : ∀ y, f7 y = true → r.eval y = true := by
      intro y h; rw [← hev y] at h; simp [MForm.eval] at h; exact h.2
    have hl_ne : ∃ y, f7 y = false ∧ l.eval y = true := by
      by_contra h
      push_neg at h
      have heq : ∀ y, l.eval y = f7 y := by
        intro y
        cases hf : f7 y with
        | true => exact hf_le_l y hf
        | false => cases hl : l.eval y with | false => rfl | true => exact absurd hl (h y hf)
      have hcard : (essVars l.eval).card = 7 := by
        have : essVars l.eval = essVars f7 := by congr 1; funext y; exact heq y
        rw [this, f7_ess_card]
      have := l.card_essVars_le_leaves
      omega
    have hr_ne : ∃ y, f7 y = false ∧ r.eval y = true := by
      by_contra h
      push_neg at h
      have heq : ∀ y, r.eval y = f7 y := by
        intro y
        cases hf : f7 y with
        | true => exact hf_le_r y hf
        | false => cases hr : r.eval y with | false => rfl | true => exact absurd hr (h y hf)
      have hcard : (essVars r.eval).card = 7 := by
        have : essVars r.eval = essVars f7 := by congr 1; funext y; exact heq y
        rw [this, f7_ess_card]
      have := r.card_essVars_le_leaves
      omega
    have hcl_ess : ∀ (F : MForm 7) (c : Finset (Fin 7)), c ∈ f7_imp_list →
        (∀ y, f7 y = true → F.eval y = true) →
        F.eval (zeroOfClause c) = false → c ⊆ essVars F.eval := by
      intro F c hc hfF hFc v hv
      simp only [essVars, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨zeroOfClause c, ?_⟩
      have hzv : zeroOfClause c v = false := by simp [zeroOfClause, hv]
      rw [hzv, Bool.not_false, hFc]
      have h1 := (f7_clause_minimal c hc).2 v hv
      rw [hfF _ h1]; decide
    have hcl_side : ∀ c ∈ f7_imp_list, c ⊆ essVars l.eval ∨ c ⊆ essVars r.eval := by
      intro c hc
      have h := hev (zeroOfClause c)
      rw [(f7_clause_minimal c hc).1] at h
      simp only [MForm.eval, Bool.and_eq_false_iff] at h
      rcases h with hl | hr
      · exact Or.inl (hcl_ess l c hc hf_le_l hl)
      · exact Or.inr (hcl_ess r c hc hf_le_r hr)
    have hc01 := hcl_side {0, 1} (by simp [f7_imp_list])
    have hc12 := hcl_side {1, 2} (by simp [f7_imp_list])
    have hc23 := hcl_side {2, 3} (by simp [f7_imp_list])
    have hc24 := hcl_side {2, 4} (by simp [f7_imp_list])
    have hc16 := hcl_side {1, 6} (by simp [f7_imp_list])
    have hc035 := hcl_side {0, 3, 5} (by simp [f7_imp_list])
    have hunion : essVars l.eval ∪ essVars r.eval = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      fin_cases v
      · rcases hc01 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
      · rcases hc01 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
      · rcases hc12 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
      · rcases hc23 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
      · rcases hc24 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
      · rcases hc035 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
      · rcases hc16 with h | h; exact Or.inl (h (by simp)); exact Or.inr (h (by simp))
    have hdisj : Disjoint (essVars l.eval) (essVars r.eval) := by
      have hcu := Finset.card_union_add_card_inter (essVars l.eval) (essVars r.eval)
      rw [hunion] at hcu
      have hcard7 : (Finset.univ : Finset (Fin 7)).card = 7 := by simp
      have hle1 := l.card_essVars_le_leaves
      have hle2 := r.card_essVars_le_leaves
      have hinter : (essVars l.eval ∩ essVars r.eval).card = 0 := by omega
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter)
    have hclause_ne : ∀ c ∈ f7_imp_list, c.Nonempty := by
      intro c hc
      simp only [f7_imp_list, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨3, by simp⟩
      · exact ⟨4, by simp⟩
    have hne_r : (essVars r.eval).Nonempty := by
      obtain ⟨y, hy0, hyl⟩ := hl_ne
      obtain ⟨c, hc, hyle⟩ := f7_false_le_clause y hy0
      have hlc : l.eval (zeroOfClause c) = true := l.eval_mono hyle hyl
      have hrc : r.eval (zeroOfClause c) = false := by
        have := hev (zeroOfClause c)
        rw [(f7_clause_minimal c hc).1] at this
        simp [MForm.eval, hlc] at this; exact this
      obtain ⟨v, hv⟩ := hclause_ne c hc
      exact ⟨v, hcl_ess r c hc hf_le_r hrc hv⟩
    have hne_l : (essVars l.eval).Nonempty := by
      obtain ⟨y, hy0, hyr⟩ := hr_ne
      obtain ⟨c, hc, hyle⟩ := f7_false_le_clause y hy0
      have hrc : r.eval (zeroOfClause c) = true := r.eval_mono hyle hyr
      have hlc : l.eval (zeroOfClause c) = false := by
        have := hev (zeroOfClause c)
        rw [(f7_clause_minimal c hc).1] at this
        simp [MForm.eval, hrc] at this; exact this
      obtain ⟨v, hv⟩ := hclause_ne c hc
      exact ⟨v, hcl_ess l c hc hf_le_l hlc hv⟩
    rcases hc12 with h12l | h12r
    · have h01l : ({0, 1} : Finset (Fin 7)) ⊆ essVars l.eval :=
        hc01.resolve_right fun h =>
          Finset.disjoint_left.mp hdisj (h12l (show (1 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
            (h (show (1 : Fin 7) ∈ ({0, 1} : Finset (Fin 7)) by simp))
      have h23l : ({2, 3} : Finset (Fin 7)) ⊆ essVars l.eval :=
        hc23.resolve_right fun h =>
          Finset.disjoint_left.mp hdisj (h12l (show (2 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
            (h (show (2 : Fin 7) ∈ ({2, 3} : Finset (Fin 7)) by simp))
      have h24l : ({2, 4} : Finset (Fin 7)) ⊆ essVars l.eval :=
        hc24.resolve_right fun h =>
          Finset.disjoint_left.mp hdisj (h12l (show (2 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
            (h (show (2 : Fin 7) ∈ ({2, 4} : Finset (Fin 7)) by simp))
      have h16l : ({1, 6} : Finset (Fin 7)) ⊆ essVars l.eval :=
        hc16.resolve_right fun h =>
          Finset.disjoint_left.mp hdisj (h12l (show (1 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
            (h (show (1 : Fin 7) ∈ ({1, 6} : Finset (Fin 7)) by simp))
      have h035l : ({0, 3, 5} : Finset (Fin 7)) ⊆ essVars l.eval :=
        hc035.resolve_right fun h =>
          Finset.disjoint_left.mp hdisj (h01l (show (0 : Fin 7) ∈ ({0, 1} : Finset (Fin 7)) by simp))
            (h (show (0 : Fin 7) ∈ ({0, 3, 5} : Finset (Fin 7)) by simp))
      obtain ⟨v, hv⟩ := hne_r
      have hvl : v ∈ essVars l.eval := by
        fin_cases v
        · exact h01l (by simp)
        · exact h12l (by simp)
        · exact h12l (by simp)
        · exact h23l (by simp)
        · exact h24l (by simp)
        · exact h035l (by simp)
        · exact h16l (by simp)
      exact Finset.disjoint_left.mp hdisj hvl hv
    · have h01r : ({0, 1} : Finset (Fin 7)) ⊆ essVars r.eval :=
        hc01.resolve_left fun h =>
          Finset.disjoint_left.mp hdisj (h (show (1 : Fin 7) ∈ ({0, 1} : Finset (Fin 7)) by simp))
            (h12r (show (1 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
      have h23r : ({2, 3} : Finset (Fin 7)) ⊆ essVars r.eval :=
        hc23.resolve_left fun h =>
          Finset.disjoint_left.mp hdisj (h (show (2 : Fin 7) ∈ ({2, 3} : Finset (Fin 7)) by simp))
            (h12r (show (2 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
      have h24r : ({2, 4} : Finset (Fin 7)) ⊆ essVars r.eval :=
        hc24.resolve_left fun h =>
          Finset.disjoint_left.mp hdisj (h (show (2 : Fin 7) ∈ ({2, 4} : Finset (Fin 7)) by simp))
            (h12r (show (2 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
      have h16r : ({1, 6} : Finset (Fin 7)) ⊆ essVars r.eval :=
        hc16.resolve_left fun h =>
          Finset.disjoint_left.mp hdisj (h (show (1 : Fin 7) ∈ ({1, 6} : Finset (Fin 7)) by simp))
            (h12r (show (1 : Fin 7) ∈ ({1, 2} : Finset (Fin 7)) by simp))
      have h035r : ({0, 3, 5} : Finset (Fin 7)) ⊆ essVars r.eval :=
        hc035.resolve_left fun h =>
          Finset.disjoint_left.mp hdisj (h (show (0 : Fin 7) ∈ ({0, 3, 5} : Finset (Fin 7)) by simp))
            (h01r (show (0 : Fin 7) ∈ ({0, 1} : Finset (Fin 7)) by simp))
      obtain ⟨v, hv⟩ := hne_l
      have hvr : v ∈ essVars r.eval := by
        fin_cases v
        · exact h01r (by simp)
        · exact h12r (by simp)
        · exact h12r (by simp)
        · exact h23r (by simp)
        · exact h24r (by simp)
        · exact h035r (by simp)
        · exact h16r (by simp)
      exact Finset.disjoint_left.mp hdisj hv hvr

lemma no_scirc_f7_le_6 :
    ¬ (∃ (gs : List SGate) (out : ℕ), SValid 7 gs ∧ gs.length ≤ 6 ∧ out < 7 + gs.length ∧
      ∀ y : Fin 7 → Bool, (swires gs (List.ofFn y)).getD out false = f7 y) := by
  intro hex
  let P (s : ℕ) : Prop :=
    ∃ (gs : List SGate) (out : ℕ), SValid 7 gs ∧ gs.length = s ∧ out < 7 + s ∧
      ∀ y : Fin 7 → Bool, (swires gs (List.ofFn y)).getD out false = f7 y
  have hPex : ∃ s, P s := by
    obtain ⟨gs, out, hv, hle, hout, hev⟩ := hex
    exact ⟨gs.length, gs, out, hv, rfl, hout, hev⟩
  classical
  set s := Nat.find hPex with hs_def
  have hs_le : s ≤ 6 := by
    obtain ⟨gs, out, hv, hle, hout, hev⟩ := hex
    exact le_trans (Nat.find_min' hPex ⟨gs, out, hv, rfl, hout, hev⟩) hle
  obtain ⟨gs, out, hv, hlen, hout_lt, hev⟩ := Nat.find_spec hPex
  rw [← hs_def] at hlen hout_lt
  have hmin : ∀ s' < s, ¬ P s' := fun s' hlt => Nat.find_min hPex hlt
  have hout_ge : 7 ≤ out := by
    by_contra hlt
    push_neg at hlt
    apply f7_not_var ⟨out, hlt⟩
    intro y
    have h := hev y
    rw [swires_getD_lt _ _ _ (by simp; omega)] at h
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at h
    rw [List.getElem_ofFn] at h
    exact h
  let deg (w : ℕ) : ℕ := ∑ m : Fin gs.length, if w ∈ gs[m.val].inputs then 1 else 0
  have hdeg_in : ∀ v : Fin 7, 1 ≤ deg v.val := by
    intro v
    by_contra h0
    have hunused : ∀ m : Fin gs.length, v.val ∉ gs[m.val].inputs := by
      intro m hm
      have hle : (if v.val ∈ gs[m.val].inputs then 1 else 0) ≤ deg v.val :=
        Finset.single_le_sum (f := fun m : Fin gs.length => if v.val ∈ gs[m.val].inputs then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
      simp [hm] at hle; omega
    obtain ⟨y, hy⟩ := f7_all_vars_ess v
    have hagree := unused_input_indep gs hv v hunused y (Function.update y v (!y v))
      (fun i hi => by simp [Function.update, hi]) out (by omega) (by omega)
    rw [hev y, hev (Function.update y v (!y v))] at hagree
    exact hy hagree
  have hdeg_gate : ∀ j : Fin gs.length, 7 + j.val ≠ out → 1 ≤ deg (7 + j.val) := by
    intro j hjne
    by_contra h0
    have hunused : ∀ m : Fin gs.length, 7 + j.val ∉ gs[m.val].inputs := by
      intro m hm
      have hle : (if 7 + j.val ∈ gs[m.val].inputs then 1 else 0) ≤ deg (7 + j.val) :=
        Finset.single_le_sum (f := fun m : Fin gs.length => if 7 + j.val ∈ gs[m.val].inputs then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
      simp [hm] at hle; omega
    have hv' := eraseGate_valid gs hv j.val j.isLt hunused
    have hlen' : (eraseGate 7 gs j.val).length = s - 1 := by
      simp [eraseGate, List.length_take, List.length_drop, hlen]; omega
    have hout' : shiftWire (7 + j.val) out < 7 + (s - 1) := by
      apply shiftWire_lt (by omega) (Ne.symm hjne) (by omega)
    have hs_pos : 0 < s := by omega
    apply hmin (s - 1) (by omega)
    refine ⟨eraseGate 7 gs j.val, shiftWire (7 + j.val) out, hv', hlen', hout', fun y => ?_⟩
    rw [eraseGate_eval gs hv j.val j.isLt hunused (List.ofFn y) (by simp) out (by omega) (Ne.symm hjne)]
    exact hev y
  set B := Finset.univ.filter fun m : Fin gs.length => gs[m.val].isBin = true
  set U := Finset.univ.filter fun m : Fin gs.length => gs[m.val].isBin = false
  have hBU : B.card + U.card = s := by
    have hdisj : Disjoint B U := by
      rw [Finset.disjoint_left]; intro m h1 h2
      simp only [B, U, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h1] at h2; exact Bool.noConfusion h2
    have hun : B ∪ U = Finset.univ := by
      ext m; simp only [B, U, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases gs[m.val].isBin <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hun]; simp [hlen]
  have hsum_deg : ∑ w ∈ Finset.range (7 + s), deg w = 2 * B.card + U.card := by
    simp only [deg]
    rw [Finset.sum_comm]
    have heach : ∀ m : Fin gs.length,
        (∑ w ∈ Finset.range (7 + s), if w ∈ gs[m.val].inputs then 1 else 0) =
        if gs[m.val].isBin = true then 2 else 1 := by
      intro m
      have hvm := hv m.val m.isLt
      cases hgm : gs[m.val] with
      | not a =>
        simp only [hgm] at hvm
        simp only [SGate.inputs, SGate.isBin, List.mem_singleton, Bool.false_eq_true, ite_false]
        rw [Finset.sum_eq_single a]
        · simp
        · intro w _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      | and a b =>
        simp only [hgm] at hvm
        simp only [SGate.inputs, SGate.isBin, List.mem_cons, List.not_mem_nil, or_false, ite_true]
        have hsp : ∀ w ∈ Finset.range (7 + s),
            (if w = a ∨ w = b then 1 else 0) = (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
          intro w _
          by_cases ha : w = a
          · subst ha; simp [hvm.1]
          · by_cases hb : w = b
            · subst hb; simp [ha]
            · simp [ha, hb]
        rw [Finset.sum_congr rfl hsp, Finset.sum_add_distrib]
        rw [Finset.sum_eq_single a (fun w _ h => by simp [h]) (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
        rw [Finset.sum_eq_single b (fun w _ h => by simp [h]) (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
        simp
      | or a b =>
        simp only [hgm] at hvm
        simp only [SGate.inputs, SGate.isBin, List.mem_cons, List.not_mem_nil, or_false, ite_true]
        have hsp : ∀ w ∈ Finset.range (7 + s),
            (if w = a ∨ w = b then 1 else 0) = (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
          intro w _
          by_cases ha : w = a
          · subst ha; simp [hvm.1]
          · by_cases hb : w = b
            · subst hb; simp [ha]
            · simp [ha, hb]
        rw [Finset.sum_congr rfl hsp, Finset.sum_add_distrib]
        rw [Finset.sum_eq_single a (fun w _ h => by simp [h]) (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
        rw [Finset.sum_eq_single b (fun w _ h => by simp [h]) (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
        simp
    rw [Finset.sum_congr rfl (fun m _ => heach m)]
    have hpt : ∀ m : Fin gs.length,
        (if gs[m.val].isBin = true then 2 else 1) =
        (if m ∈ B then 2 else 0) + (if m ∈ U then 1 else 0) := by
      intro m
      cases h : gs[m.val].isBin <;> simp [B, U, h]
    rw [Finset.sum_congr rfl (fun m _ => hpt m), Finset.sum_add_distrib]
    have hBs : ∑ m : Fin gs.length, (if m ∈ B then 2 else 0) = 2 * B.card := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      have : Finset.univ.filter (fun m : Fin gs.length => m ∈ B) = B := by ext; simp
      rw [this]; omega
    have hUs : ∑ m : Fin gs.length, (if m ∈ U then 1 else 0) = U.card := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      have : Finset.univ.filter (fun m : Fin gs.length => m ∈ U) = U := by ext; simp
      rw [this]
    rw [hBs, hUs]
  have hge1 : ∀ w ∈ (Finset.range (7 + s)).erase out, 1 ≤ deg w := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_range] at hw
    by_cases h7 : w < 7
    · exact hdeg_in ⟨w, h7⟩
    · have h := hdeg_gate ⟨w - 7, by omega⟩ (by dsimp only; omega)
      simpa [show 7 + (w - 7) = w by omega] using h
  have hsum_er_ge : 6 + s ≤ ∑ w ∈ (Finset.range (7 + s)).erase out, deg w := by
    calc 6 + s = ((Finset.range (7 + s)).erase out).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hout_lt), Finset.card_range]; omega
      _ = ∑ _w ∈ (Finset.range (7 + s)).erase out, 1 := by simp
      _ ≤ ∑ w ∈ (Finset.range (7 + s)).erase out, deg w := Finset.sum_le_sum hge1
  have hsum_split : ∑ w ∈ Finset.range (7 + s), deg w =
      deg out + ∑ w ∈ (Finset.range (7 + s)).erase out, deg w :=
    (Finset.add_sum_erase _ _ (Finset.mem_range.mpr hout_lt)).symm
  have hB6 : B.card = 6 := by omega
  have hU0 : U.card = 0 := by omega
  have hs6 : s = 6 := by omega
  have hdeg_out0 : deg out = 0 := by omega
  have hsum_er_eq : ∑ w ∈ (Finset.range (7 + s)).erase out, deg w = 6 + s := by omega
  have hdeg_one : ∀ w ∈ (Finset.range (7 + s)).erase out, deg w = 1 := by
    intro w hw
    by_contra hne
    have hgt : 2 ≤ deg w := by have := hge1 w hw; omega
    have hrest : ∑ u ∈ ((Finset.range (7 + s)).erase out).erase w, 1 ≤
        ∑ u ∈ ((Finset.range (7 + s)).erase out).erase w, deg u :=
      Finset.sum_le_sum fun u hu => hge1 u (Finset.mem_of_mem_erase hu)
    have hsp := Finset.add_sum_erase ((Finset.range (7 + s)).erase out) deg hw
    have hc1 : (((Finset.range (7 + s)).erase out).erase w).card = 5 + s := by
      rw [Finset.card_erase_of_mem hw, Finset.card_erase_of_mem (Finset.mem_range.mpr hout_lt),
        Finset.card_range]
      omega
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hc1] at hrest
    omega
  have hall_bin : ∀ m : Fin gs.length, gs[m.val].isBin = true := by
    intro m
    cases h : gs[m.val].isBin with
    | true => rfl
    | false =>
      have hmU : m ∈ U := by simp [U, h]
      have : 0 < U.card := Finset.card_pos.mpr ⟨m, hmU⟩
      omega
  have hdeg_gate_eq : ∀ j : Fin gs.length,
      deg (7 + j.val) + (if 7 + j.val = out then 1 else 0) = 1 := by
    intro j
    by_cases he : 7 + j.val = out
    · rw [he, if_pos rfl, hdeg_out0]
    · rw [if_neg he, add_zero]
      exact hdeg_one (7 + j.val) (Finset.mem_erase.mpr ⟨he, Finset.mem_range.mpr (by omega)⟩)
  obtain ⟨T, hTev, hTlev⟩ := extract_monotone_formula (by omega : 0 < 7) gs out hv hout_ge
    (by omega) hall_bin hdeg_gate_eq
  have hlev7 : T.leaves = 7 := by
    rw [hTlev]
    have h7 : ∀ v ∈ Finset.range 7, deg v = 1 := fun v hv =>
      hdeg_one v (Finset.mem_erase.mpr ⟨by have := Finset.mem_range.mp hv; omega,
        Finset.mem_range.mpr (by have := Finset.mem_range.mp hv; omega)⟩)
    calc ∑ v ∈ Finset.range 7, deg v = ∑ _v ∈ Finset.range 7, 1 := Finset.sum_congr rfl h7
      _ = 7 := by simp
  exact no_mform7_le_7 T (by omega) (fun y => by rw [hTev y, hev y])

end PEqualNP.Outside.L_meta_27301

theorem PEqualNP.Outside.L_meta_27301 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩)) := by
  rintro ⟨C, _, hsize, heval, hout, hnorm, _, hused, h0, h1⟩
  exact PEqualNP.Outside.L_meta_27301.no_scirc_f7_le_6
    (PEqualNP.Outside.L_meta_27301.reduce_to_f7 C hsize heval hout hnorm hused h0 h1)
