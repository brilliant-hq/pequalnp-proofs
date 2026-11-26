import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18938_aux

open PEqualNP.CircuitLowerBounds

theorem app_lt {α : Type} (w : List α) (a a0 : α) (i : ℕ) (h : i < w.length) :
    (w ++ [a]).getD i a0 = w.getD i a0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem app_eq {α : Type} (w : List α) (a a0 : α) (i : ℕ) (h : i = w.length) :
    (w ++ [a]).getD i a0 = a := by
  subst h
  simp [List.getD_eq_getElem?_getD]

theorem app_gt {α : Type} (w : List α) (a a0 : α) (i : ℕ) (h : w.length < i) :
    (w ++ [a]).getD i a0 = a0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

theorem far {α : Type} (w : List α) (a0 : α) (i : ℕ) (h : w.length ≤ i) :
    w.getD i a0 = a0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem ofFn_getD {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]
  · rw [dif_neg h]
    exact far _ _ _ (by simp; omega)

def ev (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sel (op : GateOp) (k : ℕ) : Option ℕ :=
  match op with
  | GateOp.or => some k
  | _ => none

def step2 (m : ℕ) (s : List (Option ℕ) × List Gate) (op : GateOp) (oa ob : Option ℕ) :
    List (Option ℕ) × List Gate :=
  match oa, ob with
  | some ka, some kb => (s.1 ++ [some (m + s.2.length)], s.2 ++ [⟨op, [ka, kb]⟩])
  | some k, none => (s.1 ++ [sel op k], s.2)
  | none, some k => (s.1 ++ [sel op k], s.2)
  | none, none => (s.1 ++ [none], s.2)

theorem ev_def (w : List Bool) (g : Gate) :
    ev w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem len_fold (gs : List Gate) : ∀ w : List Bool, (gs.foldl ev w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.length_cons, ev, List.length_append, List.length_nil]
    omega


def step3 (n : ℕ) (m : ℕ → Bool) (s : List (Option ℕ) × List Gate) (op : GateOp) (a b : ℕ) :
    List (Option ℕ) × List Gate :=
  if m s.1.length = true then step2 n s op (s.1.getD a none) (s.1.getD b none) else (s.1 ++ [none], s.2)

def step (n : ℕ) (m : ℕ → Bool) (s : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  step3 n m s g.op (g.inputs.getD 0 0) (g.inputs.getD 1 0)

def wv (C : Circuit) (x : List Bool) (i : ℕ) : Bool := (C.gates.foldl ev x).getD i false

theorem pre (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl ev w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i h; rfl
  | cons g gs ih =>
    intro w i h
    simp only [List.foldl_cons]
    rw [ih _ _ (by simp [ev]; omega), ev_def, app_lt _ _ _ _ h]

theorem wire_eq (gs : List Gate) : ∀ (w : List Bool) (j : ℕ), j < gs.length →
    (∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j) →
    (gs.foldl ev w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl ev w).getD i false) := by
  induction gs with
  | nil => intro w j h; simp at h
  | cons g gs ih =>
    intro w j h hr
    have key : ∀ i, i < w.length → (gs.foldl ev (ev w g)).getD i false = w.getD i false := by
      intro i hi
      rw [pre gs _ _ (by simp [ev]; omega), ev_def, app_lt _ _ _ _ hi]
    cases j with
    | zero =>
      simp only [List.foldl_cons]
      have e : (g :: gs).getD 0 ⟨GateOp.or, []⟩ = g := rfl
      rw [e] at hr ⊢
      have l1 : (gs.foldl ev (ev w g)).getD (w.length + 0) false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [pre gs _ _ (by simp [ev])]
        exact app_eq _ _ _ _ rfl
      rw [l1]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (key i (by have := hr i hi; omega)).symm
    | succ j =>
      simp only [List.foldl_cons]
      have e : (g :: gs).getD (j + 1) ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := rfl
      rw [e] at hr ⊢
      have h2 := ih (ev w g) j (by simpa using h) (by intro i hi; have := hr i hi; simp [ev]; omega)
      have e2 : (ev w g).length + j = w.length + (j + 1) := by simp [ev]; omega
      rw [e2] at h2
      exact h2

theorem b1 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (pa pb wa wb : Bool) :
    (pa = false → wa = false) → (pb = false → wb = false) → op.eval [pa, pb] = false →
    op.eval [wa, wb] = false := by
  rcases hop with rfl | rfl <;> cases pa <;> cases pb <;> cases wa <;> cases wb <;> decide

theorem b2 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (pa pb ma mb : Bool) :
    (pa && ma) = false → (pb && mb) = false →
    (op.eval [pa, pb] = true → (pa = true → ma = true) ∧ (pb = true → mb = true)) →
    op.eval [pa, pb] = false := by
  rcases hop with rfl | rfl <;> cases pa <;> cases pb <;> cases ma <;> cases mb <;> decide

theorem b3 (pa pb ma mb : Bool) :
    (pa && ma) = true → (pb && mb) = false →
    (GateOp.and.eval [pa, pb] = true → (pa = true → ma = true) ∧ (pb = true → mb = true)) →
    GateOp.and.eval [pa, pb] = false := by
  cases pa <;> cases pb <;> cases ma <;> cases mb <;> decide

theorem b4 (pa pb ma mb : Bool) :
    (pa && ma) = true → (pb && mb) = false →
    (GateOp.or.eval [pa, pb] = true → (pa = true → ma = true) ∧ (pb = true → mb = true)) →
    GateOp.or.eval [pa, pb] = true ∧ pb = false := by
  cases pa <;> cases pb <;> cases ma <;> cases mb <;> decide

theorem b5 (pa pb ma mb : Bool) :
    (pa && ma) = false → (pb && mb) = true →
    (GateOp.and.eval [pa, pb] = true → (pa = true → ma = true) ∧ (pb = true → mb = true)) →
    GateOp.and.eval [pa, pb] = false := by
  cases pa <;> cases pb <;> cases ma <;> cases mb <;> decide

theorem b6 (pa pb ma mb : Bool) :
    (pa && ma) = false → (pb && mb) = true →
    (GateOp.or.eval [pa, pb] = true → (pa = true → ma = true) ∧ (pb = true → mb = true)) →
    GateOp.or.eval [pa, pb] = true ∧ pa = false := by
  cases pa <;> cases pb <;> cases ma <;> cases mb <;> decide

theorem b7 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (pa pb ma mb : Bool) :
    (pa && ma) = true → (pb && mb) = true → op.eval [pa, pb] = true ∧ pa = true ∧ pb = true := by
  rcases hop with rfl | rfl <;> cases pa <;> cases pb <;> cases ma <;> cases mb <;> decide

theorem or_l (wa : Bool) : GateOp.or.eval [wa, false] = wa := by cases wa <;> rfl

theorem or_r (wb : Bool) : GateOp.or.eval [false, wb] = wb := by cases wb <;> rfl

def Inv (n : ℕ) (m AF WF : ℕ → Bool) (y0 : List Bool) (r : List (Option ℕ)) (ds : List Gate)
    (N : ℕ) : Prop :=
  r.length = N ∧
  (∀ i < N, (r.getD i none).isSome = (AF i && m i)) ∧
  (∀ i < N, AF i = false → WF i = false) ∧
  (∀ i < N, ∀ k, r.getD i none = some k → k < n + ds.length ∧ (ds.foldl ev y0).getD k false = WF i) ∧
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < ds.length, ∀ i ∈ (ds.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)

theorem extend (n : ℕ) (m AF WF : ℕ → Bool) (y0 : List Bool) (r : List (Option ℕ))
    (ds ds2 : List Gate) (N : ℕ) (x : Option ℕ) (h : Inv n m AF WF y0 r ds N)
    (hx1 : x.isSome = (AF N && m N)) (hx2 : AF N = false → WF N = false)
    (hx3 : ∀ k, x = some k → k < n + ds2.length ∧ (ds2.foldl ev y0).getD k false = WF N)
    (h4 : ∀ k, k < n + ds.length → (ds2.foldl ev y0).getD k false = (ds.foldl ev y0).getD k false)
    (h4b : ds.length ≤ ds2.length)
    (h5 : ∀ g ∈ ds2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h6 : ∀ j < ds2.length, ∀ i ∈ (ds2.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) :
    Inv n m AF WF y0 (r ++ [x]) ds2 (N + 1) := by
  obtain ⟨i1, i2, i3, i4, i6, i7⟩ := h
  refine ⟨by simp [i1], ?_, ?_, ?_, h5, h6⟩
  · intro i hi
    rcases Nat.lt_or_ge i N with hl | hl
    · rw [app_lt _ _ _ _ (by omega)]
      exact i2 i hl
    · have e : i = N := by omega
      subst e
      rw [app_eq _ _ _ _ i1.symm]
      exact hx1
  · intro i hi
    rcases Nat.lt_or_ge i N with hl | hl
    · exact i3 i hl
    · have e : i = N := by omega
      subst e
      exact hx2
  · intro i hi k hk
    rcases Nat.lt_or_ge i N with hl | hl
    · rw [app_lt _ _ _ _ (by omega)] at hk
      obtain ⟨a1, a2⟩ := i4 i hl k hk
      exact ⟨by omega, by rw [h4 k a1]; exact a2⟩
    · have e : i = N := by omega
      subst e
      rw [app_eq _ _ _ _ i1.symm] at hk
      exact hx3 k hk

theorem sel_and (k : ℕ) : sel GateOp.and k = none := rfl

theorem sel_or (k : ℕ) : sel GateOp.or k = some k := rfl

theorem step_inv (n : ℕ) (m AF WF : ℕ → Bool) (y0 : List Bool) (hy : y0.length = n) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b N : ℕ) (ha : a < N) (hb : b < N)
    (hAN : AF N = op.eval [AF a, AF b]) (hWN : WF N = op.eval [WF a, WF b])
    (hcl : m N = true → AF N = true → (AF a = true → m a = true) ∧ (AF b = true → m b = true))
    (r : List (Option ℕ)) (ds : List Gate) (h : Inv n m AF WF y0 r ds N) :
    Inv n m AF WF y0 (step3 n m (r, ds) op a b).1 (step3 n m (r, ds) op a b).2 (N + 1) ∧
    ((step3 n m (r, ds) op a b).2.length = ds.length ∨
      ((step3 n m (r, ds) op a b).2.length = ds.length + 1 ∧ m N = true ∧ AF a = true ∧
        AF b = true)) := by
  have hh := h
  obtain ⟨i1, i2, i3, i4, i6, i7⟩ := h
  have hA := i2 a ha
  have hB := i2 b hb
  have dA := i3 a ha
  have dB := i3 b hb
  have triv4 : ∀ k, k < n + ds.length → (ds.foldl ev y0).getD k false = (ds.foldl ev y0).getD k false :=
    fun _ _ => rfl
  have hd : AF N = false → WF N = false := by
    rw [hAN, hWN]
    exact b1 op hop _ _ _ _ dA dB
  by_cases hm : m N = true
  · have hs : step3 n m (r, ds) op a b = step2 n (r, ds) op (r.getD a none) (r.getD b none) := by
      show (if m r.length = true then _ else _) = _
      rw [i1, if_pos hm]
    have hcl2 := hcl hm
    rw [hAN] at hcl2
    rw [hs]
    cases ea : r.getD a none with
    | none =>
      rw [ea] at hA
      cases eb : r.getD b none with
      | none =>
        rw [eb] at hB
        refine ⟨?_, Or.inl rfl⟩
        show Inv n m AF WF y0 (r ++ [none]) ds _
        refine extend n m AF WF y0 r ds ds N none hh ?_ hd ?_ triv4 (le_refl _) i6 i7
        · rw [hAN, b2 op hop _ _ _ _ hA.symm hB.symm hcl2]
          rfl
        · intro k hk
          cases hk
      | some kb =>
        rw [eb] at hB
        obtain ⟨q1, q2⟩ := i4 b hb kb eb
        refine ⟨?_, Or.inl rfl⟩
        show Inv n m AF WF y0 (r ++ [sel op kb]) ds _
        refine extend n m AF WF y0 r ds ds N _ hh ?_ hd ?_ triv4 (le_refl _) i6 i7
        · rcases hop with ho | ho
          · subst ho
            rw [hAN, b5 _ _ _ _ hA.symm hB.symm hcl2]
            rfl
          · subst ho
            rw [hAN, (b6 _ _ _ _ hA.symm hB.symm hcl2).1, hm]
            rfl
        · intro k hk
          rcases hop with ho | ho
          · subst ho
            cases hk
          · subst ho
            rw [sel_or] at hk
            simp at hk
            subst hk
            refine ⟨q1, ?_⟩
            rw [hWN, dA (b6 _ _ _ _ hA.symm hB.symm hcl2).2, or_r]
            exact q2
    | some ka =>
      rw [ea] at hA
      obtain ⟨a1, a2⟩ := i4 a ha ka ea
      cases eb : r.getD b none with
      | none =>
        rw [eb] at hB
        refine ⟨?_, Or.inl rfl⟩
        show Inv n m AF WF y0 (r ++ [sel op ka]) ds _
        refine extend n m AF WF y0 r ds ds N _ hh ?_ hd ?_ triv4 (le_refl _) i6 i7
        · rcases hop with ho | ho
          · subst ho
            rw [hAN, b3 _ _ _ _ hA.symm hB.symm hcl2]
            rfl
          · subst ho
            rw [hAN, (b4 _ _ _ _ hA.symm hB.symm hcl2).1, hm]
            rfl
        · intro k hk
          rcases hop with ho | ho
          · subst ho
            cases hk
          · subst ho
            rw [sel_or] at hk
            simp at hk
            subst hk
            refine ⟨a1, ?_⟩
            rw [hWN, dB (b4 _ _ _ _ hA.symm hB.symm hcl2).2, or_l]
            exact a2
      | some kb =>
        rw [eb] at hB
        obtain ⟨q1, q2⟩ := i4 b hb kb eb
        have hlen : (ds.foldl ev y0).length = n + ds.length := by rw [len_fold, hy]
        obtain ⟨c1, c2, c3⟩ := b7 op hop _ _ _ _ hA.symm hB.symm
        refine ⟨?_, Or.inr ⟨by simp [step2], hm, c2, c3⟩⟩
        show Inv n m AF WF y0 (r ++ [some (n + ds.length)]) (ds ++ [⟨op, [ka, kb]⟩]) _
        refine extend n m AF WF y0 r ds (ds ++ [⟨op, [ka, kb]⟩]) N _ hh ?_ hd ?_ ?_ (by simp) ?_ ?_
        · rw [hAN, c1, hm]
          rfl
        · intro k hk
          simp at hk
          subst hk
          refine ⟨by simp, ?_⟩
          rw [List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [ev_def, app_eq _ _ _ _ hlen.symm, hWN, ← a2, ← q2]
          rfl
        · intro k hk
          rw [List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [ev_def, app_lt _ _ _ _ (by omega)]
        · intro g2 hg2
          rw [List.mem_append] at hg2
          rcases hg2 with hg2 | hg2
          · exact i6 g2 hg2
          · simp at hg2
            subst hg2
            exact ⟨hop, rfl⟩
        · intro j hj i hi
          simp at hj
          rcases Nat.lt_or_ge j ds.length with hl | hl
          · rw [app_lt _ _ _ _ hl] at hi
            exact i7 j hl i hi
          · rw [app_eq _ _ _ _ (by omega)] at hi
            simp at hi
            rcases hi with hi | hi <;> omega
  · have hs : step3 n m (r, ds) op a b = (r ++ [none], ds) := by
      show (if m r.length = true then _ else _) = _
      rw [i1, if_neg hm]
    rw [hs]
    refine ⟨?_, Or.inl rfl⟩
    refine extend n m AF WF y0 r ds ds N none hh ?_ hd ?_ triv4 (le_refl _) i6 i7
    · simp [hm]
    · intro k hk
      cases hk

open PEqualNP.MetaComplexity.NestedCover in
theorem take_succ2 (C : Circuit) (j : ℕ) (h : j < C.gates.length) :
    C.gates.take (j + 1) = C.gates.take j ++ [gateAt C j] := by
  rw [List.take_succ]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

open PEqualNP.MetaComplexity.NestedCover in
theorem gshape (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hm : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen := hC.2.2 _ hm
  have hrb := hC.2.1 j hj
  match hgi : (gateAt C j).inputs, hlen with
  | [a, b], _ =>
    rw [hgi] at hrb
    exact ⟨a, b, rfl, hrb a (by simp), hrb b (by simp), hC.1 _ hm⟩

open PEqualNP.MetaComplexity.NestedCover in
theorem gval (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (x : List Bool)
    (hx : x.length = n) :
    wv C x (n + j) = (gateAt C j).op.eval [wv C x a, wv C x b] := by
  have h := wire_eq C.gates x j hj (by rw [hx]; exact hC.2.1 j hj)
  rw [hx] at h
  show (C.gates.foldl ev x).getD (n + j) false = _
  rw [h]
  show (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.gates.foldl ev x).getD i false) = _
  rw [hin]
  rfl

theorem inp {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    wv C (List.ofFn x) i = x ⟨i, h⟩ := by
  unfold wv
  rw [pre _ _ _ (by simpa using h), ofFn_getD, dif_pos h]

open PEqualNP.MetaComplexity.NestedCover in
theorem main_ind (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (m : ℕ → Bool)
    (x0 x y0 : List Bool) (h0x : x0.length = n) (hx : x.length = n) (hy : y0.length = n)
    (r0 : List (Option ℕ))
    (hcl : ∀ j < C.gates.length, m (n + j) = true → wv C x0 (n + j) = true →
      ∀ i ∈ (gateAt C j).inputs, wv C x0 i = true → m i = true)
    (h0 : Inv n m (wv C x0) (wv C x) y0 r0 [] n) :
    ∀ j, j ≤ C.gates.length →
      Inv n m (wv C x0) (wv C x) y0 ((C.gates.take j).foldl (step n m) (r0, [])).1
        ((C.gates.take j).foldl (step n m) (r0, [])).2 (n + j) ∧
      ((C.gates.take j).foldl (step n m) (r0, [])).2.length ≤
        ((List.range j).filter fun g => m (n + g) && (gateAt C g).inputs.all (wv C x0)).length := by
  intro j
  induction j with
  | zero => intro _; exact ⟨h0, by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨I, cnt⟩ := ih (by omega)
    obtain ⟨a, b, hin, ha, hb, hop⟩ := gshape n C hC j hj
    rw [take_succ2 C j hj, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (C.gates.take j).foldl (step n m) (r0, []) = S at I cnt ⊢
    have hs : step n m S (gateAt C j) = step3 n m S (gateAt C j).op a b := by
      show step3 n m S (gateAt C j).op ((gateAt C j).inputs.getD 0 0) ((gateAt C j).inputs.getD 1 0) = _
      rw [hin]
      rfl
    rw [hs]
    obtain ⟨s1, s2⟩ := step_inv n m (wv C x0) (wv C x) y0 hy (gateAt C j).op hop a b (n + j) ha hb
      (gval n C hC j hj a b hin x0 h0x) (gval n C hC j hj a b hin x hx)
      (fun h1 h2 => ⟨hcl j hj h1 h2 a (by rw [hin]; simp), hcl j hj h1 h2 b (by rw [hin]; simp)⟩)
      S.1 S.2 I
    refine ⟨s1, ?_⟩
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases s2 with s2 | ⟨s2, sm, sa, sb⟩
    · have e : (step3 n m S (gateAt C j).op a b).2.length = S.2.length := s2
      omega
    · have e : (step3 n m S (gateAt C j).op a b).2.length = S.2.length + 1 := s2
      have pj : (m (n + j) && (gateAt C j).inputs.all (wv C x0)) = true := by
        rw [hin]
        simp [sm, sa, sb]
      have e3 : ([j].filter fun g => m (n + g) && (gateAt C g).inputs.all (wv C x0)).length = 1 := by
        simp [List.filter, pj]
      omega

end PEqualNP.Outside.L_meta_18938_aux

open PEqualNP.Outside.L_meta_18938_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18938 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : ℕ → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     have x6 : ℕ → Bool := PEqualNP.ReadTwo.wval x2 fun (x6 : Fin x1) => Decidable.decide (x6 ≠ x3);     x4 x2.output = Bool.true → (∀ x8 < x2.size, x4 (x1 + x8) = Bool.true → x6 (x1 + x8) = Bool.true → ∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, x6 x12 = Bool.true → x4 x12 = Bool.true) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x9 ∧ x9.size ≤ (List.filter (fun (x10 : ℕ) => x4 (x1 + x10) && (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs.all x6) (List.range x2.size)).length ∧ ∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x2.eval (List.ofFn fun (x11 : Fin x1) => if x11 = x3 then Bool.false else x10 x11) := by
  intro n C i0 m hC
  show m C.output = true → (∀ j < C.gates.length, m (n + j) = true → wv C (List.ofFn fun j : Fin n => decide (j ≠ i0)) (n + j) = true → ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, wv C (List.ofFn fun j : Fin n => decide (j ≠ i0)) i = true → m i = true) → ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ (List.filter (fun g : ℕ => m (n + g) && (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.all (wv C (List.ofFn fun j : Fin n => decide (j ≠ i0)))) (List.range C.gates.length)).length ∧ ∀ y : Fin n → Bool, D.eval (List.ofFn y) = wv C (List.ofFn fun j : Fin n => if j = i0 then false else y j) C.output
  intro hout hcl
  have init : ∀ y : Fin n → Bool, Inv n m (wv C (List.ofFn fun j : Fin n => decide (j ≠ i0)))
      (wv C (List.ofFn fun j : Fin n => if j = i0 then false else y j)) (List.ofFn y)
      (List.ofFn fun j : Fin n => if (m j.val && decide (j ≠ i0)) = true then some j.val else none) [] n := by
    intro y
    refine ⟨by simp, ?_, ?_, ?_, by simp, by simp⟩
    · intro i hi
      rw [ofFn_getD, dif_pos hi, inp C _ i hi]
      by_cases h1 : m i = true <;> by_cases h2 : (⟨i, hi⟩ : Fin n) = i0 <;> simp [h1, h2]
    · intro i hi h
      rw [inp C _ i hi] at h ⊢
      simp at h
      simp [h]
    · intro i hi k hk
      rw [ofFn_getD, dif_pos hi] at hk
      split_ifs at hk with hc
      simp at hk
      subst hk
      refine ⟨by simpa using hi, ?_⟩
      rw [inp C _ _ hi]
      show (List.ofFn y).getD i false = _
      rw [ofFn_getD, dif_pos hi]
      simp at hc
      simp [hc.2]
  have F := fun y : Fin n → Bool => main_ind n C hC m (List.ofFn fun j : Fin n => decide (j ≠ i0))
      (List.ofFn fun j : Fin n => if j = i0 then false else y j) (List.ofFn y) (by simp) (by simp) (by simp)
      _ hcl (init y) C.gates.length (le_refl _)
  simp only [List.take_length] at F
  obtain ⟨⟨_, _, _, _, k6, k7⟩, kc⟩ := F (fun _ => false)
  refine ⟨⟨(C.gates.foldl (step n m) (List.ofFn fun j : Fin n => if (m j.val && decide (j ≠ i0)) = true then some j.val else none, [])).2,
    match (C.gates.foldl (step n m) (List.ofFn fun j : Fin n => if (m j.val && decide (j ≠ i0)) = true then some j.val else none, [])).1.getD C.output none with
    | some k => k
    | none => n + (C.gates.foldl (step n m) (List.ofFn fun j : Fin n => if (m j.val && decide (j ≠ i0)) = true then some j.val else none, [])).2.length⟩,
    ⟨fun g hg => (k6 g hg).1, k7, fun g hg => (k6 g hg).2⟩, kc, ?_⟩
  intro y
  obtain ⟨⟨j1, j2, j3, j4, _, _⟩, _⟩ := F y
  show (List.foldl ev (List.ofFn y) _).getD _ false = _
  cases hr : (C.gates.foldl (step n m) (List.ofFn fun j : Fin n => if (m j.val && decide (j ≠ i0)) = true then some j.val else none, [])).1.getD C.output none with
  | none =>
    rw [far _ _ _ (by rw [len_fold]; simp)]
    by_cases ho : C.output < n + C.gates.length
    · have e := j2 _ ho
      rw [hr, hout] at e
      have e2 : wv C (List.ofFn fun j : Fin n => decide (j ≠ i0)) C.output = false := by
        simpa using e.symm
      exact (j3 _ ho e2).symm
    · symm
      exact far _ _ _ (by rw [len_fold]; simp; omega)
  | some k =>
    have ho : C.output < n + C.gates.length := by
      by_contra hc
      rw [far _ _ _ (by rw [j1]; omega)] at hr
      simp at hr
    exact (j4 _ ho _ hr).2
