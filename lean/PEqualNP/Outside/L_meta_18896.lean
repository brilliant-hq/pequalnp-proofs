import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18896_aux

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

def step (m : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate) : List (Option ℕ) × List Gate :=
  step2 m s g.op (s.1.getD (g.inputs.getD 0 0) none) (s.1.getD (g.inputs.getD 1 0) none)

theorem ev_def (w : List Bool) (g : Gate) :
    ev w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem len_fold (gs : List Gate) : ∀ w : List Bool, (gs.foldl ev w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.length_cons, ev, List.length_append, List.length_nil]
    omega

theorem mono_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), w.getD i false = true →
    (gs.foldl ev w).getD i false = true := by
  induction gs with
  | nil => intro w i h; exact h
  | cons g gs ih =>
    intro w i h
    simp only [List.foldl_cons]
    apply ih
    by_cases hi : i < w.length
    · unfold ev
      rw [app_lt _ _ _ _ hi]
      exact h
    · rw [far _ _ _ (by omega)] at h
      simp at h

def Inv (m : ℕ) (y0 : List Bool) (r : List (Option ℕ)) (ds : List Gate) (wC A : List Bool) : Prop :=
  r.length = wC.length ∧ A.length = wC.length ∧
  (∀ i, (r.getD i none).isSome = A.getD i false) ∧
  (∀ i, r.getD i none = none → wC.getD i false = false) ∧
  (∀ i k, r.getD i none = some k → k < m + ds.length ∧ (ds.foldl ev y0).getD k false = wC.getD i false) ∧
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < ds.length, ∀ i ∈ (ds.getD j ⟨GateOp.or, []⟩).inputs, i < m + j)

theorem extend (m : ℕ) (y0 : List Bool) (r : List (Option ℕ)) (ds ds' : List Gate) (wC A : List Bool)
    (x : Option ℕ) (vC vA : Bool) (h : Inv m y0 r ds wC A)
    (hx1 : x.isSome = vA) (hx2 : x = none → vC = false)
    (hx3 : ∀ k, x = some k → k < m + ds'.length ∧ (ds'.foldl ev y0).getD k false = vC)
    (h4 : ∀ k, k < m + ds.length → (ds'.foldl ev y0).getD k false = (ds.foldl ev y0).getD k false)
    (h4' : ds.length ≤ ds'.length)
    (h5 : ∀ g ∈ ds', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h6 : ∀ j < ds'.length, ∀ i ∈ (ds'.getD j ⟨GateOp.or, []⟩).inputs, i < m + j) :
    Inv m y0 (r ++ [x]) ds' (wC ++ [vC]) (A ++ [vA]) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h
  refine ⟨by simp [i1], by simp [i2], ?_, ?_, ?_, h5, h6⟩
  · intro i
    rcases lt_trichotomy i wC.length with hl | hl | hl
    · rw [app_lt _ _ _ _ (by omega), app_lt _ _ _ _ (by omega)]
      exact i3 i
    · rw [app_eq _ _ _ _ (by omega), app_eq _ _ _ _ (by omega)]
      exact hx1
    · rw [app_gt _ _ _ _ (by omega), app_gt _ _ _ _ (by omega)]
      rfl
  · intro i hi
    rcases lt_trichotomy i wC.length with hl | hl | hl
    · rw [app_lt _ _ _ _ (by omega)] at hi
      rw [app_lt _ _ _ _ (by omega)]
      exact i4 i hi
    · rw [app_eq _ _ _ _ (by omega)] at hi
      rw [app_eq _ _ _ _ (by omega)]
      exact hx2 hi
    · exact app_gt _ _ _ _ (by omega)
  · intro i k hi
    rcases lt_trichotomy i wC.length with hl | hl | hl
    · rw [app_lt _ _ _ _ (by omega)] at hi
      rw [app_lt _ _ _ _ (by omega)]
      obtain ⟨a1, a2⟩ := i5 i k hi
      exact ⟨by omega, by rw [h4 k a1]; exact a2⟩
    · rw [app_eq _ _ _ _ (by omega)] at hi
      rw [app_eq _ _ _ _ (by omega)]
      exact hx3 k hi
    · rw [app_gt _ _ _ _ (by omega)] at hi
      simp at hi

theorem sel_and (k : ℕ) : sel GateOp.and k = none := rfl

theorem sel_or (k : ℕ) : sel GateOp.or k = some k := rfl

theorem step_inv (m : ℕ) (y0 : List Bool) (hy : y0.length = m) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : ℕ) (hin : g.inputs = [a, b])
    (r : List (Option ℕ)) (ds : List Gate) (wC A : List Bool) (h : Inv m y0 r ds wC A) :
    Inv m y0 (step m (r, ds) g).1 (step m (r, ds) g).2 (ev wC g) (ev A g) ∧
    ((step m (r, ds) g).2.length = ds.length ∨
      ((step m (r, ds) g).2.length = ds.length + 1 ∧ A.getD a false = true ∧ A.getD b false = true)) := by
  have h' := h
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h
  have hA := i3 a
  have hB := i3 b
  have triv4 : ∀ k, k < m + ds.length → (ds.foldl ev y0).getD k false = (ds.foldl ev y0).getD k false :=
    fun _ _ => rfl
  have eA : (g.inputs.map fun i => A.getD i false) = [A.getD a false, A.getD b false] := by
    rw [hin]; rfl
  have eC : (g.inputs.map fun i => wC.getD i false) = [wC.getD a false, wC.getD b false] := by
    rw [hin]; rfl
  have hs0 : step m (r, ds) g = step2 m (r, ds) g.op (r.getD a none) (r.getD b none) := by
    show step2 m (r, ds) g.op (r.getD (g.inputs.getD 0 0) none) (r.getD (g.inputs.getD 1 0) none) = _
    rw [hin]; rfl
  rw [hs0, ev_def, ev_def, eA, eC]
  cases ha : r.getD a none with
  | none =>
    cases hb : r.getD b none with
    | none =>
      rw [ha] at hA
      rw [hb] at hB
      refine ⟨?_, Or.inl rfl⟩
      show Inv m y0 (r ++ [none]) ds _ _
      simp only [← hA, ← hB, i4 a ha, i4 b hb]
      refine extend m y0 r ds ds wC A none _ _ h' ?_ ?_ ?_ triv4 (le_refl _) i6 i7
      · rcases hop with ho | ho <;> simp [ho, GateOp.eval]
      · intro _
        rcases hop with ho | ho <;> simp [ho, GateOp.eval]
      · intro k hk
        simp at hk
    | some kb =>
      rw [ha] at hA
      rw [hb] at hB
      refine ⟨?_, Or.inl rfl⟩
      show Inv m y0 (r ++ [sel g.op kb]) ds _ _
      obtain ⟨b1, b2⟩ := i5 b kb hb
      simp only [← hA, ← hB, i4 a ha, ← b2]
      refine extend m y0 r ds ds wC A _ _ _ h' ?_ ?_ ?_ triv4 (le_refl _) i6 i7
      · rcases hop with ho | ho <;> simp [ho, GateOp.eval, sel_and, sel_or]
      · intro hn
        rcases hop with ho | ho
        · simp [ho, GateOp.eval]
        · rw [ho, sel_or] at hn
          simp at hn
      · intro k hk
        rcases hop with ho | ho
        · rw [ho, sel_and] at hk
          simp at hk
        · rw [ho, sel_or] at hk
          simp at hk
          subst hk
          refine ⟨b1, ?_⟩
          simp [ho, GateOp.eval]
  | some ka =>
    obtain ⟨a1, a2⟩ := i5 a ka ha
    cases hb : r.getD b none with
    | none =>
      rw [ha] at hA
      rw [hb] at hB
      refine ⟨?_, Or.inl rfl⟩
      show Inv m y0 (r ++ [sel g.op ka]) ds _ _
      simp only [← hA, ← hB, i4 b hb, ← a2]
      refine extend m y0 r ds ds wC A _ _ _ h' ?_ ?_ ?_ triv4 (le_refl _) i6 i7
      · rcases hop with ho | ho <;> simp [ho, GateOp.eval, sel_and, sel_or]
      · intro hn
        rcases hop with ho | ho
        · simp [ho, GateOp.eval]
        · rw [ho, sel_or] at hn
          simp at hn
      · intro k hk
        rcases hop with ho | ho
        · rw [ho, sel_and] at hk
          simp at hk
        · rw [ho, sel_or] at hk
          simp at hk
          subst hk
          refine ⟨a1, ?_⟩
          simp [ho, GateOp.eval]
    | some kb =>
      obtain ⟨b1, b2⟩ := i5 b kb hb
      rw [ha] at hA
      rw [hb] at hB
      have hlen : (ds.foldl ev y0).length = m + ds.length := by rw [len_fold, hy]
      refine ⟨?_, Or.inr ⟨by simp [step2], by simpa using hA.symm, by simpa using hB.symm⟩⟩
      show Inv m y0 (r ++ [some (m + ds.length)]) (ds ++ [⟨g.op, [ka, kb]⟩]) _ _
      simp only [← hA, ← hB, ← a2, ← b2]
      refine extend m y0 r ds (ds ++ [⟨g.op, [ka, kb]⟩]) wC A _ _ _ h' ?_ ?_ ?_ ?_ (by simp) ?_ ?_
      · rcases hop with ho | ho <;> simp [ho, GateOp.eval]
      · intro hn
        simp at hn
      · intro k hk
        simp at hk
        subst hk
        refine ⟨by simp, ?_⟩
        rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ev_def, app_eq _ _ _ _ hlen.symm]
        rfl
      · intro k hk
        rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ev_def, app_lt _ _ _ _ (by omega)]
      · intro g' hg'
        rw [List.mem_append] at hg'
        rcases hg' with hg' | hg'
        · exact i6 g' hg'
        · simp at hg'
          subst hg'
          exact ⟨hop, rfl⟩
      · intro j hj i hi
        simp at hj
        rcases Nat.lt_or_ge j ds.length with hl | hl
        · rw [app_lt _ _ _ _ hl] at hi
          exact i7 j hl i hi
        · rw [app_eq _ _ _ _ (by omega)] at hi
          simp at hi
          rcases hi with hi | hi <;> omega

theorem fold (m : ℕ) (y0 : List Bool) (hy : y0.length = m) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ (r : List (Option ℕ)) (ds : List Gate) (wC A : List Bool), Inv m y0 r ds wC A →
      Inv m y0 (gs.foldl (step m) (r, ds)).1 (gs.foldl (step m) (r, ds)).2 (gs.foldl ev wC) (gs.foldl ev A) ∧
      (gs.foldl (step m) (r, ds)).2.length ≤ ds.length +
        (gs.filter fun g => g.inputs.all fun i => (gs.foldl ev A).getD i false).length := by
  induction gs with
  | nil => intro r ds wC A h; exact ⟨h, by simp⟩
  | cons g gs ih =>
    intro r ds wC A h
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨a, b, hin⟩ : ∃ a b, g.inputs = [a, b] := by
      match hgi : g.inputs, hlen with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨s1, s2⟩ := step_inv m y0 hy g hop a b hin r ds wC A h
    obtain ⟨t1, t2⟩ := ih (fun g' hg' => hg g' (by simp [hg'])) _ _ _ _ s1
    have eta : ((step m (r, ds) g).1, (step m (r, ds) g).2) = step m (r, ds) g := rfl
    rw [eta] at t1 t2
    simp only [List.foldl_cons]
    refine ⟨t1, ?_⟩
    rw [List.filter_cons]
    rcases s2 with s2 | ⟨s2, sa, sb⟩
    · rw [s2] at t2
      split_ifs
      · simp only [List.length_cons]
        omega
      · exact t2
    · have la : a < A.length := by
        by_contra hc
        rw [far _ _ _ (by omega)] at sa
        simp at sa
      have lb : b < A.length := by
        by_contra hc
        rw [far _ _ _ (by omega)] at sb
        simp at sb
      have pa := mono_prefix gs (ev A g) a (by rw [ev_def, app_lt _ _ _ _ la]; exact sa)
      have pb := mono_prefix gs (ev A g) b (by rw [ev_def, app_lt _ _ _ _ lb]; exact sb)
      rw [if_pos (by rw [hin]; simp only [List.all_cons, List.all_nil, pa, pb]; rfl)]
      simp only [List.length_cons]
      omega

end PEqualNP.Outside.L_meta_18896_aux

open PEqualNP.Outside.L_meta_18896_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18896 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1 → Option (Fin x2)),   PEqualNP.TopForm.IsAO2 x1 x3 →     have x6 : List Bool := x3.wires (List.ofFn fun (x6 : Fin x1) => (x4 x6).isSome);     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x7 ∧ x7.size ≤ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.all fun (x9 : ℕ) => x6.getD x9 Bool.false) x3.gates).length ∧ ∀ (x8 : Fin x2 → Bool), x7.eval (List.ofFn x8) = x3.eval (List.ofFn fun (x9 : Fin x1) => (x4 x9).elim Bool.false x8) := by
  intro n m C σ hC
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩
  have init : ∀ y : Fin m → Bool, Inv m (List.ofFn y) (List.ofFn fun i : Fin n => (σ i).map Fin.val) []
      (List.ofFn fun i : Fin n => (σ i).elim false y) (List.ofFn fun i : Fin n => (σ i).isSome) := by
    intro y
    refine ⟨by simp, by simp, ?_, ?_, ?_, by simp, by simp⟩
    · intro i
      rw [ofFn_getD, ofFn_getD]
      split_ifs with hlt
      · cases σ ⟨i, hlt⟩ <;> rfl
      · rfl
    · intro i hi
      rw [ofFn_getD] at hi ⊢
      split_ifs at hi ⊢ with hlt
      · cases hσ : σ ⟨i, hlt⟩ with
        | none => rfl
        | some j => rw [hσ] at hi; simp at hi
      · rfl
    · intro i k hi
      rw [ofFn_getD] at hi
      rw [ofFn_getD]
      split_ifs at hi ⊢ with hlt
      · cases hσ : σ ⟨i, hlt⟩ with
        | none => rw [hσ] at hi; simp at hi
        | some j =>
          rw [hσ] at hi
          simp at hi
          subst hi
          refine ⟨by simp, ?_⟩
          show (List.ofFn y).getD _ false = _
          rw [ofFn_getD, dif_pos j.2]
          rfl
  have F := fun y : Fin m → Bool => fold m (List.ofFn y) (by simp) C.gates hgs _ _ _ _ (init y)
  show ∃ x7 : Circuit, PEqualNP.TopForm.IsAO2 m x7 ∧ x7.size ≤ (List.filter (fun g : Gate => g.inputs.all fun i => (C.wires (List.ofFn fun i : Fin n => (σ i).isSome)).getD i false) C.gates).length ∧ ∀ y : Fin m → Bool, x7.eval (List.ofFn y) = C.eval (List.ofFn fun i : Fin n => (σ i).elim false y)
  obtain ⟨⟨_, _, _, _, _, k6, k7⟩, kc⟩ := F (fun _ => false)
  refine ⟨⟨(C.gates.foldl (step m) (List.ofFn fun i : Fin n => (σ i).map Fin.val, [])).2,
    match (C.gates.foldl (step m) (List.ofFn fun i : Fin n => (σ i).map Fin.val, [])).1.getD C.output none with
    | some k => k
    | none => m + (C.gates.foldl (step m) (List.ofFn fun i : Fin n => (σ i).map Fin.val, [])).2.length⟩,
    ⟨fun g hg => (k6 g hg).1, k7, fun g hg => (k6 g hg).2⟩, ?_, ?_⟩
  · simp only [List.length_nil, Nat.zero_add] at kc
    exact kc
  · intro y
    obtain ⟨⟨_, _, _, j4, j5, _, _⟩, _⟩ := F y
    show (List.foldl ev (List.ofFn y) _).getD _ false = (List.foldl ev _ C.gates).getD C.output false
    cases hr : (C.gates.foldl (step m) (List.ofFn fun i : Fin n => (σ i).map Fin.val, [])).1.getD C.output none with
    | none =>
      rw [j4 _ hr]
      exact far _ _ _ (by rw [len_fold]; simp)
    | some k => exact (j5 _ _ hr).2
