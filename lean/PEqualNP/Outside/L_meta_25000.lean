import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25000

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



def zapWire (i Z k : ℕ) : ℕ := if k = i then Z else k

def zapGate (i Z : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (zapWire i Z)⟩

def zap (N : ℕ) (C : Circuit) (i : ℕ) : Circuit :=
  ⟨C.gates.map (zapGate i (N+C.size)), zapWire i (N+C.size) C.output⟩

theorem zap_run (N i Z : ℕ) (hi : i < N) (gs : List Gate)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hyi : y.getD i false = false)
    (hxy : ∀ k, k ≠ i → x.getD k false = y.getD k false) :
    N + gs.length ≤ Z → ∀ k, k ≠ i →
      (run (gs.map (zapGate i Z)) x).getD k false = (run gs y).getD k false := by
  induction gs using List.reverseRecOn with
  | nil => intro _; simpa [run] using hxy
  | append_singleton gs g ih =>
    intro hZ
    have ih' := ih (by simp at hZ; omega)
    have he : (zapGate i Z g).op.eval ((zapGate i Z g).inputs.map
        (fun k => (run (gs.map (zapGate i Z)) x).getD k false)) =
        g.op.eval (g.inputs.map (fun k => (run gs y).getD k false)) := by
      simp only [zapGate, List.map_map]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      by_cases hki : k = i
      · subst k
        simp only [Function.comp_apply, zapWire, ite_true]
        rw [List.getD_eq_default _ _ (by rw [run_length, List.length_map, hx]; simp at hZ; omega),
          run_input _ _ _ (by omega), hyi]
      · simpa [zapWire, hki] using ih' k hki
    intro k hki
    simp only [List.map_append, List.map_singleton]
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length,
      List.length_map, hx, hy, he]
    split_ifs
    · rfl
    · exact ih' k hki

theorem zap_eval (N : ℕ) (C : Circuit) (i : Fin N) (x : Fin N → Bool) :
    (zap N C i).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update x i false)) := by
  let y := List.ofFn (Function.update x i false)
  have hy : y.length = N := by simp [y]
  have hyi : y.getD i false = false := by
    rw [List.getD_eq_getElem _ _ (by simp [y]), List.getElem_ofFn]
    simp
  have hxy : ∀ k : ℕ, k ≠ (i : ℕ) → (List.ofFn x).getD k false = y.getD k false := by
    intro k hki
    by_cases hk : k < N
    · rw [List.getD_eq_getElem _ _ (by simpa using hk),
        List.getD_eq_getElem _ _ (by simpa [y] using hk)]
      simp only [y, List.getElem_ofFn]
      exact (Function.update_of_ne (fun h => hki (congrArg Fin.val h)) _ _).symm
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [y]; omega)]
  change (run (C.gates.map (zapGate i (N+C.size))) (List.ofFn x)).getD
    (zapWire i (N+C.size) C.output) false = (run C.gates y).getD C.output false
  by_cases ho : C.output = i
  · rw [zapWire, if_pos ho, ho,
      List.getD_eq_default _ _ (by rw [run_length, List.length_map, List.length_ofFn]; rfl),
      run_input _ _ _ (by omega), hyi]
  · rw [zapWire, if_neg ho]
    exact zap_run N i (N+C.size) i.2 C.gates (List.ofFn x) y (by simp) hy hyi hxy
      (by rfl) C.output ho

theorem zap_properties (N : ℕ) (C : Circuit) (i : Fin N)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (zap N C i) ∧
    (zap N C i).size = C.size ∧ (zap N C i).output ≠ i ∧
    ∀ g ∈ (zap N C i).gates, (i : ℕ) ∉ g.inputs := by
  have hZi : N+C.size ≠ i := by have := i.2; omega
  have hw : ∀ k, zapWire i (N+C.size) k ≠ i := by
    intro k; unfold zapWire; split_ifs with h
    · exact hZi
    · exact h
  refine ⟨?_, by simp [zap, Circuit.size], hw _, ?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    simpa [zapGate] using hC a ha
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    simpa only [zapGate, List.mem_map] using
      (show ¬ ∃ b, b ∈ a.inputs ∧ zapWire i (N+C.size) b = i from
        fun ⟨b, _, hb⟩ => hw b hb)

def input {n m : ℕ} (w : Fin n) (v : Fin m) : Fin (n+m) → Bool :=
  Fin.append (fun a => decide (a=w)) (fun b => decide (b=v))

def zeroRow {n m : ℕ} (v : Fin m) : Fin (n+m) → Bool :=
  Fin.append (fun _ => false) (fun b => decide (b=v))

theorem input_ofFn {n m : ℕ} (w : Fin n) (v : Fin m) :
    List.ofFn (input w v) = PEqualNP.Represents.oneEach w v := by
  exact List.ofFn_fin_append _ _

theorem input_update_other {n m : ℕ} (w u : Fin n) (v : Fin m) (hwu : w ≠ u) :
    Function.update (input w v) (Fin.castAdd m u) false = input w v := by
  funext k
  by_cases h : k = Fin.castAdd m u
  · subst k
    simp [input, Function.update_self, Ne.symm hwu]
  · exact Function.update_of_ne h _ _

theorem input_update_self {n m : ℕ} (u : Fin n) (v : Fin m) :
    Function.update (input u v) (Fin.castAdd m u) false = zeroRow (n:=n) v := by
  funext k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · by_cases ha : a = u
    · subst a; simp [input, zeroRow]
    · simp [input, zeroRow, Function.update_apply, ha]
  · have hne : Fin.natAdd n b ≠ Fin.castAdd m u := by
      intro h; have hv := congrArg Fin.val h; have := u.2; simp only [Fin.val_natAdd, Fin.val_castAdd] at hv; omega
    simp [input, zeroRow, Function.update_apply, hne]

def constantCircuit (N : ℕ) (b : Bool) : Circuit :=
  ⟨if b then [⟨GateOp.and, []⟩] else [], N⟩

theorem constant_eval (N : ℕ) (b : Bool) (x : Fin N → Bool) :
    (constantCircuit N b).eval (List.ofFn x) = b := by
  cases b <;> simp [constantCircuit, Circuit.eval, Circuit.wires, GateOp.eval]

theorem constant_properties (N : ℕ) (b : Bool) (i : Fin N) :
    PEqualNP.MetaComplexity.FanInTwo (constantCircuit N b) ∧
    (constantCircuit N b).output ≠ i ∧
    (∀ g ∈ (constantCircuit N b).gates, (i : ℕ) ∉ g.inputs) := by
  cases b <;> simp [constantCircuit, PEqualNP.MetaComplexity.FanInTwo]
  all_goals have := i.2; omega

end PEqualNP.Outside.L_meta_25000

theorem PEqualNP.Outside.L_meta_25000 : (∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u u2 : Fin n), (∀ v : Fin m, A u v = A u2 v) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ (∀ (w : Fin n) (v : Fin m), w ≠ u2 → C2.eval (PEqualNP.Represents.oneEach w v) = A w v) ∧ (C2.size + 1 ≤ s ∨ (C2.size ≤ s ∧ (C2.output ≠ u.val ∧ ∀ g < C2.gates.length, (C2.output = n + m + g ∨ (n + m ≤ C2.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C2 g (C2.output - (n + m)))) → u.val ∉ (C2.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs)))) := by
  classical
  intro n m s A u u2 heq hex
  obtain ⟨C, hC, hsize, hrep⟩ := hex
  let i : Fin (n+m) := Fin.castAdd m u
  let j : Fin (n+m) := Fin.castAdd m u2
  have hin : ∀ w v, C.eval (List.ofFn (PEqualNP.Outside.L_meta_25000.input w v)) = A w v := by
    intro w v
    rw [PEqualNP.Outside.L_meta_25000.input_ofFn]
    exact hrep w v
  let f : (Fin (n+m) → Bool) → Bool := fun x => C.eval (List.ofFn x)
  by_cases hc : ∃ b, ∀ x, f (Function.update x j false) = b
  · obtain ⟨b, hb⟩ := hc
    let D := PEqualNP.Outside.L_meta_25000.constantCircuit (n+m) b
    obtain ⟨hD, hout, hno⟩ := PEqualNP.Outside.L_meta_25000.constant_properties (n+m) b i
    have hDsize : D.size ≤ s := by
      cases b
      · simpa [D, PEqualNP.Outside.L_meta_25000.constantCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]
      · have hpos : 1 ≤ C.size := by
          by_contra h
          have hg : C.gates = [] := List.length_eq_zero_iff.1 (by
            change C.gates.length = 0
            change ¬ 1 ≤ C.gates.length at h
            omega)
          have hzero := hb (fun _ => false)
          have hup : Function.update (fun _ : Fin (n+m) => false) j false = (fun _ => false) := by
            funext k; by_cases hkj : k=j <;> simp [Function.update_apply, hkj]
          rw [hup] at hzero
          simp [f, PEqualNP.CircuitLowerBounds.Circuit.eval,
            PEqualNP.CircuitLowerBounds.Circuit.wires, hg,
            List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hzero
          split_ifs at hzero <;> simp_all
        simpa [D, PEqualNP.Outside.L_meta_25000.constantCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]
          using (le_trans hpos hsize)
    refine ⟨D, hD, ?_, Or.inr ⟨hDsize, hout, ?_⟩⟩
    · intro w v hw
      rw [← PEqualNP.Outside.L_meta_25000.input_ofFn]
      rw [PEqualNP.Outside.L_meta_25000.constant_eval]
      have h := hb (PEqualNP.Outside.L_meta_25000.input w v)
      rw [PEqualNP.Outside.L_meta_25000.input_update_other w u2 v hw] at h
      exact h.symm.trans (hin w v)
    · intro g hg _
      rw [List.getD_eq_getElem _ _ hg]
      exact hno _ (List.getElem_mem hg)
  · by_cases he : ∃ x y : Fin (n+m) → Bool,
        (∀ k, k ≠ j → x k = y k) ∧ f x ≠ f y
    · obtain ⟨D, hD, hDs, hDf⟩ := PEqualNP.Outside.L_meta_25000.one_drop (n+m) C hC j false he hc
      refine ⟨D, hD, ?_, Or.inl (le_trans hDs hsize)⟩
      intro w v hw
      rw [← PEqualNP.Outside.L_meta_25000.input_ofFn, hDf,
        PEqualNP.Outside.L_meta_25000.input_update_other w u2 v hw]
      exact hin w v
    · have hind : ∀ x, f (Function.update x j false) = f x := by
        intro x
        by_contra h
        exact he ⟨Function.update x j false, x,
          fun k hk => Function.update_of_ne hk _ _, h⟩
      let D := PEqualNP.Outside.L_meta_25000.zap (n+m) C i
      obtain ⟨hD, hDs, hout, hno⟩ := PEqualNP.Outside.L_meta_25000.zap_properties (n+m) C i hC
      refine ⟨D, hD, ?_, Or.inr ⟨by rw [hDs]; exact hsize, hout, ?_⟩⟩
      · intro w v _
        rw [← PEqualNP.Outside.L_meta_25000.input_ofFn,
          PEqualNP.Outside.L_meta_25000.zap_eval]
        by_cases hw : w = u
        · subst w
          rw [PEqualNP.Outside.L_meta_25000.input_update_self]
          have h := hind (PEqualNP.Outside.L_meta_25000.input u2 v)
          rw [PEqualNP.Outside.L_meta_25000.input_update_self] at h
          exact h.trans ((hin u2 v).trans (heq v).symm)
        · rw [PEqualNP.Outside.L_meta_25000.input_update_other w u v hw]
          exact hin w v
      · intro g hg _
        rw [List.getD_eq_getElem _ _ hg]
        exact hno _ (List.getElem_mem hg)
