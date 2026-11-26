import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25000_aux
namespace PinSource
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuit (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := restrict n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, h2, fun y => (hk' y).symm⟩

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi

theorem one_drop (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (i : Fin n)
    (b : Bool)
    (hess : ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hnc : ¬ ∃ c, ∀ y : Fin n → Bool, C.eval (List.ofFn (Function.update y i b)) = c) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (Function.update y i b)) := by
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have hw : ∀ x, C.wires x = run C.gates x := fun _ => rfl
  have hev : ∀ x, C.eval x = (run C.gates x).getD C.output false := fun _ => rfl
  have hout : C.output < n + C.gates.length := by
    by_contra hcon
    obtain ⟨x, y, -, hxy⟩ := hess
    apply hxy
    rw [hev, hev, List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
  let X : (Fin n → Bool) → List Bool := fun y => List.ofFn (Function.update y i b)
  have hXl : ∀ y, (X y).length = n := fun y => by simp [X]
  have hXi : ∀ y, (X y).getD i false = b := by
    intro y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  have hXk : ∀ (k : ℕ), k < n → k ≠ i → ∀ y, (X y).getD k false = (List.ofFn y).getD k false := by
    intro k hk hki y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_ofFn, List.getElem_ofFn]
    exact Function.update_of_ne (fun hc => hki (congrArg Fin.val hc)) _ _
  have hinw : ∀ k < n, ∀ y, (C.wires (X y)).getD k false = (X y).getD k false := by
    intro k hk y
    rw [hw]
    exact run_input _ _ _ (by rw [hXl]; exact hk)
  have hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun k =>
          if k < n + j then (C.wires (X y)).getD k false else false) := by
    intro j hj y
    have h := run_gate C.gates (X y) j hj
    rw [hXl] at h
    exact h
  have hoi : C.output ≠ i := by
    intro h
    apply hnc
    refine ⟨b, fun y => ?_⟩
    rw [hev, h, run_input _ _ _ (by simp)]
    exact hXi y
  have hread : ∃ g ∈ C.gates, (i : ℕ) ∈ rds g := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy, hne⟩ := hess
    apply hne
    rw [hev, hev]
    refine indep i C.gates (fun g hg => (hops g hg).1) hcon _ _ (by simp) (fun k hk => ?_) _ hoi
    by_cases h : k < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_ofFn, List.getElem_ofFn]
      exact hxy _ fun hc => hk (congrArg Fin.val hc)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  obtain ⟨D, S, d1, -, -, d4, d5, d6⟩ := circuit n n C X hops hXl (fun k hk => by
      by_cases h : k = i
      · exact Or.inl ⟨b, fun y => by rw [h]; exact hXi y⟩
      · exact Or.inr ⟨k, hk, hXk k hk h⟩) hrec hinw hout hnc
  refine ⟨D, fun g hg => ?_, ?_, fun y => d6 y⟩
  · obtain ⟨h1, h2⟩ := d1 g hg
    exact ⟨by simpa using h1, h2⟩
  · have hdrop : Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
      obtain ⟨hop, hlen⟩ := hops _ hg
      have hv := hrec j hj
      have hii : ∀ y, (if (i : ℕ) < n + j then (C.wires (X y)).getD (i : ℕ) false else false) = b := by
        intro y
        rw [if_pos (by have := i.2; omega), hinw i i.2, hXi]
      generalize hI : C.gates[j].inputs = I at *
      generalize hO : C.gates[j].op = o at *
      have two : ∀ c : ℕ, (∀ y, (C.wires (X y)).getD (n + j) false =
          (b && if c < n + j then (C.wires (X y)).getD c false else false)) ∨
          (∀ y, (C.wires (X y)).getD (n + j) false =
          (b || if c < n + j then (C.wires (X y)).getD c false else false)) →
          Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
        intro c hc
        by_cases hcl : c < n + j
        · simp only [hcl, if_true] at hc
          rcases hc with hc | hc <;> cases b
          · exact Or.inl ⟨false, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inl ⟨true, fun y => by simp only; rw [hc y]; rfl⟩
        · simp only [hcl, if_false] at hc
          rcases hc with hc | hc
          · exact Or.inl ⟨b && false, fun y => hc y⟩
          · exact Or.inl ⟨b || false, fun y => hc y⟩
      match I, hlen with
      | [], _ =>
        exfalso
        simp only [rds, hO, hI] at hgi
        rcases hop with rfl | rfl | rfl <;> simp at hgi
      | [a], _ =>
        have hai : a = i := by
          simp only [rds, hO, hI] at hgi
          rcases hop with rfl | rfl | rfl
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
        subst hai
        refine Or.inl ⟨o.eval [b], fun y => ?_⟩
        simp only
        rw [hv y, List.map_singleton, hii y]
      | [a, c], _ =>
        rcases hop with rfl | rfl | rfl
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.and_comm]
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.or_comm]
        · have hai : (i : ℕ) = a := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          subst hai
          refine Or.inl ⟨!b, fun y => ?_⟩
          simp only
          rw [hv y, List.map_cons, hii y]
          rfl
    have hsub : S ⊆ (Finset.range C.gates.length).erase j := by
      intro k hk
      obtain ⟨h1, h2⟩ := d5 k hk
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 h1⟩
      rintro rfl
      exact h2 hdrop
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hj), Finset.card_range] at h1
    change D.gates.length + 1 ≤ C.gates.length
    omega


end PinSource

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def promiseBits {n m : ℕ} (w : Fin n) (v : Fin m) : Fin (n + m) → Bool :=
  Fin.append (fun i => decide (i = w)) (fun j => decide (j = v))

theorem ofFn_promiseBits {n m : ℕ} (w : Fin n) (v : Fin m) :
    List.ofFn (promiseBits w v) = oneEach w v := by
  simp [promiseBits, oneEach]

theorem pin_update_kept {n m : ℕ} (u2 w : Fin n) (v : Fin m) (hne : w ≠ u2) :
    Function.update (promiseBits w v) (u2.castAdd m) false = promiseBits w v := by
  funext j
  by_cases hj : j = u2.castAdd m
  · subst j
    simp [promiseBits, Fin.append_left, Ne.symm hne]
  · simp [Function.update_of_ne hj]

theorem pinKept {n m : ℕ} {A : Fin n → Fin m → Bool} (u2 : Fin n)
    (C : Circuit) (hC : FanInTwo C) (hA : Represents A C)
    (hess : ∃ x y : Fin (n+m) → Bool, (∀ j, j ≠ u2.castAdd m → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hnc : ¬ ∃ c : Bool, ∀ y : Fin (n+m) → Bool,
      C.eval (List.ofFn (Function.update y (u2.castAdd m) false)) = c) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ (w : Fin n) (v : Fin m), w ≠ u2 → D.eval (oneEach w v) = A w v := by
  obtain ⟨D, hD, hsz, he⟩ := PinSource.one_drop (n+m) C hC (u2.castAdd m) false hess hnc
  refine ⟨D, hD, hsz, ?_⟩
  intro w v hw
  rw [← hA w v]
  simpa only [pin_update_kept u2 w v hw, ofFn_promiseBits] using he (promiseBits w v)

end PEqualNP.Outside.L_meta_25000_aux

namespace PEqualNP.Outside.L_meta_25000_aux

open PEqualNP.CircuitLowerBounds

def eraseWire (u dead i : ℕ) : ℕ := if i = u then dead else i

def eraseGate (u dead : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (eraseWire u dead)⟩

def eraseInput (n u : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (eraseGate u (n + C.size)), eraseWire u (n + C.size) C.output⟩

theorem eraseInput_size (C : Circuit) (n u : ℕ) : (eraseInput n u C).size = C.size := by
  simp [Circuit.size, eraseInput]

theorem eraseInput_fan (C : Circuit) (n u : ℕ) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (eraseInput n u C) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
  simpa [eraseGate] using hC q hq

theorem eraseWire_ne (u dead i : ℕ) (h : u < dead) : eraseWire u dead i ≠ u := by
  simp only [eraseWire]
  split <;> omega

theorem eraseInput_out (C : Circuit) (n u : ℕ) (hu : u < n) : (eraseInput n u C).output ≠ u :=
  eraseWire_ne _ _ _ (by omega)

theorem eraseInput_pins (C : Circuit) (n u : ℕ) (hu : u < n) :
    ∀ g ∈ (eraseInput n u C).gates, u ∉ g.inputs := by
  intro g hg h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
  obtain ⟨i, hi, eq⟩ := List.mem_map.1 h
  exact eraseWire_ne u (n+C.size) i (by omega) eq

theorem erase_get (x : List Bool) (i u dead : ℕ) (hu : u < x.length)
    (hd : x.length ≤ dead) :
    x.getD (eraseWire u dead i) false = (x.set u false).getD i false := by
  by_cases he : i = u
  · subst i
    simp [eraseWire, List.getD_eq_getElem?_getD, List.getElem?_eq_none hd,
      List.getElem?_set_self hu]
  · simp [eraseWire, he, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm he)]

def eraseRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem eraseRun_length (gs : List Gate) (x : List Bool) : (eraseRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [eraseRun]
  | cons g gs ih =>
    change (eraseRun gs (x ++ [_])).length = _
    rw [ih]
    simp; omega

theorem eraseRun_rel (gs : List Gate) (x : List Bool) (u dead : ℕ)
    (hu : u < x.length) (hd : x.length + gs.length ≤ dead) :
    (eraseRun (gs.map (eraseGate u dead)) x).set u false =
      eraseRun gs (x.set u false) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hmap : (g.inputs.map (eraseWire u dead)).map (fun i => x.getD i false) =
        g.inputs.map (fun i => (x.set u false).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => erase_get x i u dead hu (by omega)
    let b := g.op.eval (g.inputs.map fun i => (x.set u false).getD i false)
    change (eraseRun (gs.map (eraseGate u dead)) (x ++ [g.op.eval
      ((g.inputs.map (eraseWire u dead)).map fun i => x.getD i false)])).set u false =
      eraseRun gs ((x.set u false) ++ [b])
    rw [hmap]
    change (eraseRun (gs.map (eraseGate u dead)) (x ++ [b])).set u false = _
    rw [ih (x ++ [b]) (by simp; omega) (by simp at hd ⊢; omega), List.set_append_left _ _ hu]

theorem eraseInput_eval (C : Circuit) (x : List Bool) (n u : ℕ)
    (hx : x.length = n) (hu : u < n) :
    (eraseInput n u C).eval x = C.eval (x.set u false) := by
  let z := eraseRun (C.gates.map (eraseGate u (n+C.size))) x
  have hz : z.length = n + C.size := by simp [z, eraseRun_length, hx, Circuit.size]
  change z.getD (eraseWire u (n+C.size) C.output) false = (eraseRun C.gates (x.set u false)).getD C.output false
  rw [erase_get z C.output u _ (by omega) (by omega)]
  exact congrArg (fun l : List Bool => l.getD C.output false)
    (eraseRun_rel C.gates x u (n+C.size) (by omega) (by simp [hx,Circuit.size]))

end PEqualNP.Outside.L_meta_25000_aux

namespace PEqualNP.Outside.L_meta_25000_aux

open PEqualNP.Represents

def blankBits (n : ℕ) {m : ℕ} (v : Fin m) : Fin (n+m) → Bool :=
  Fin.append (fun _ : Fin n => false) (fun j => decide (j = v))

theorem blankBits_row {n m : ℕ} (u : Fin n) (v : Fin m) :
    blankBits n v (u.castAdd m) = false := by
  simp [blankBits]

theorem blankBits_update {n m : ℕ} (u : Fin n) (v : Fin m) :
    Function.update (blankBits n v) (u.castAdd m) false = blankBits n v := by
  funext j
  by_cases h : j = u.castAdd m
  · subst j
    simp [blankBits_row]
  · simp [Function.update_of_ne h]

theorem dropRow_update {n m : ℕ} (w : Fin n) (v : Fin m) :
    Function.update (Fin.append (fun i : Fin n => decide (i = w)) (fun j : Fin m => decide (j = v)))
      (w.castAdd m) false = blankBits n v := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · by_cases h : i = w
    · subst i
      simp [blankBits]
    · simp [Fin.append_left, blankBits, h]
  · have h' : Fin.natAdd n j ≠ w.castAdd m := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    simp [Function.update_of_ne h', Fin.append_right, blankBits]

theorem ofFn_set_row {k : ℕ} (f : Fin k → Bool) (i : Fin k) (b : Bool) :
    (List.ofFn f).set i.val b = List.ofFn (Function.update f i b) := by
  apply List.ext_getElem
  · simp
  · intro j hl hr
    have hj : j < k := by simpa using hr
    by_cases he : j = i.val
    · subst j
      simp
    · have hh : (⟨j, hj⟩ : Fin k) ≠ i := fun hc => he (congrArg Fin.val hc)
      simp [Ne.symm he, Function.update_of_ne hh]

theorem set_row_self {n m : ℕ} (w : Fin n) (v : Fin m) :
    (oneEach w v).set w.val false = List.ofFn (blankBits n v) := by
  let f : Fin (n+m) → Bool := Fin.append (fun i : Fin n => decide (i = w))
    (fun j : Fin m => decide (j = v))
  have hf : List.ofFn f = oneEach w v := by simp [f,oneEach]
  rw [← hf]
  exact (ofFn_set_row f (w.castAdd m) false).trans (congrArg List.ofFn (dropRow_update w v))

theorem set_row_kept {n m : ℕ} (u w : Fin n) (v : Fin m) (hw : w ≠ u) :
    (oneEach w v).set u.val false = oneEach w v := by
  let f : Fin (n+m) → Bool := Fin.append (fun i : Fin n => decide (i = w))
    (fun j : Fin m => decide (j = v))
  have hf : List.ofFn f = oneEach w v := by simp [f,oneEach]
  have hkeep : Function.update f (u.castAdd m) false = f := by
    funext j
    by_cases h : j = u.castAdd m
    · subst j
      simp [f, Fin.append_left, Ne.symm hw]
    · simp [Function.update_of_ne h]
  rw [← hf]
  exact (ofFn_set_row f (u.castAdd m) false).trans (congrArg List.ofFn hkeep)

end PEqualNP.Outside.L_meta_25000_aux

open PEqualNP.Outside.L_meta_25000_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem PEqualNP.Outside.L_meta_25000 : (∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n), (∀ v : Fin m, A u v = A u2 v) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (PEqualNP.Represents.oneEach w v) = A w v) ∧ (C2.size + 1 ≤ s ∨ (C2.size ≤ s ∧ (C2.output ≠ u.val ∧ ∀ g < C2.gates.length, (C2.output = n + m + g ∨ (n + m ≤ C2.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C2 g (C2.output - (n + m)))) → u.val ∉ (C2.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs)))) := by
  classical
  intro n m s A u u2 rows witness
  obtain ⟨C, hC, hsize, hrep⟩ := witness
  let D := eraseInput (n + m) u.val C
  have hu : u.val < n + m := by have := u.isLt; omega
  have he (w : Fin n) (v : Fin m) :
      D.eval (oneEach w v) = C.eval ((oneEach w v).set u.val false) :=
    eraseInput_eval C (oneEach w v) (n + m) u.val (by simp [oneEach]) hu
  by_cases ok : ∀ (w : Fin n) (v : Fin m), w ≠ u2 → D.eval (oneEach w v) = A w v
  · refine ⟨D, eraseInput_fan C _ _ hC, ok, Or.inr ⟨?_, eraseInput_out C _ _ hu, ?_⟩⟩
    · exact (eraseInput_size C _ _).le.trans hsize
    · intro j hj _
      apply eraseInput_pins C _ _ hu
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _
  · push Not at ok
    obtain ⟨w, v, hkeep, hbad⟩ := ok
    have wu : w = u := by
      by_contra hne
      apply hbad
      rw [he, set_row_kept u w v hne]
      exact hrep w v
    subst w
    have diff : C.eval (List.ofFn (blankBits n v)) ≠ A u v := by
      rw [he, set_row_self] at hbad
      exact hbad
    have ess : ∃ x y : Fin (n + m) → Bool,
        (∀ j, j ≠ u2.castAdd m → x j = y j) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
      refine ⟨blankBits n v, promiseBits u2 v, ?_, ?_⟩
      · intro j hj
        have h := congrFun (dropRow_update u2 v) j
        simpa [promiseBits, Function.update_of_ne hj] using h.symm
      · rw [ofFn_promiseBits, hrep u2 v, ← rows v]
        exact diff
    have nc : ¬ ∃ c : Bool, ∀ y : Fin (n+m) → Bool,
        C.eval (List.ofFn (Function.update y (u2.castAdd m) false)) = c := by
      rintro ⟨c, hc⟩
      have ha := hc (promiseBits u v)
      have hb := hc (blankBits n v)
      rw [pin_update_kept u2 u v hkeep, ofFn_promiseBits, hrep u v] at ha
      rw [blankBits_update] at hb
      exact diff (hb.trans ha.symm)
    obtain ⟨D', fan, size, spec⟩ := pinKept u2 C hC hrep ess nc
    exact ⟨D', fan, spec, Or.inl (size.trans hsize)⟩
