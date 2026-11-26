import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20603

open PEqualNP.CircuitLowerBounds

namespace S98


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]

lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]

lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)

lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩

lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)

lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h

lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega

lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega

end S98

namespace Mono




def LeL (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : [v][i - l.length]? = none := by
      simp only [List.getElem?_eq_none_iff, List.length_singleton]; omega
    simp [this]

lemma step_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : LeL a b) :
    LeL (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hg with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro H r hr
      exact hle r (H r hr)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨v, ⟨r, hr, rfl⟩, hv⟩
      exact ⟨_, ⟨r, hr, rfl⟩, hle r hv⟩
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rw [getD_snoc] at hi ⊢
  rw [← hl]
  split_ifs at hi ⊢ <;> first | exact hle i hi | exact hv hi

lemma foldl_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, LeL a b →
      LeL (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_le g (hgs g List.mem_cons_self) a b h)

lemma wires_mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {m : ℕ}
    (x y : Fin m → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  have h0 : LeL (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun i hi => ?_⟩
    by_cases h : i < m
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] at hi ⊢
      exact hxy ⟨i, h⟩ hi
    · simp [List.getD_eq_getElem?_getD, h] at hi
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact (foldl_le C.gates hops _ _ h0).2 w


end Mono

namespace LB

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover S98

def Rd (N : ℕ) (C : Circuit) (j k : ℕ) : Prop :=
  j < k ∧ k < C.gates.length ∧ N + j ∈ (gateAt C k).inputs

def InCone (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  N ≤ C.output ∧ C.output - N < C.gates.length ∧ j < C.gates.length ∧
    Relation.ReflTransGen (Rd N C) j (C.output - N)

open Classical in
noncomputable def cone (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (InCone N C)

open Classical in
noncomputable def dset (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range N).filter (fun i => (∃ k ∈ cone N C, i ∈ (gateAt C k).inputs) ∨ i = C.output)

lemma mem_cone {N : ℕ} {C : Circuit} {j : ℕ} :
    j ∈ cone N C ↔ j < C.gates.length ∧ InCone N C j := by
  classical
  simp [cone]

lemma cone_closed {N : ℕ} {C : Circuit} {j k : ℕ} (hk : k ∈ cone N C) (hjk : j < k)
    (hr : N + j ∈ (gateAt C k).inputs) : j ∈ cone N C := by
  rw [mem_cone] at hk ⊢
  obtain ⟨hkl, h1, h2, -, h4⟩ := hk
  exact ⟨by omega, h1, h2, by omega, Relation.ReflTransGen.head ⟨hjk, hkl, hr⟩ h4⟩

lemma cone_reader {N : ℕ} {C : Circuit} {j : ℕ} (hj : j ∈ cone N C) (hne : j ≠ C.output - N) :
    ∃ k ∈ cone N C, N + j ∈ (gateAt C k).inputs := by
  rw [mem_cone] at hj
  obtain ⟨-, h1, h2, -, h4⟩ := hj
  rcases Relation.ReflTransGen.cases_head h4 with h | ⟨k, ⟨_, hkl, hr⟩, hrest⟩
  · exact absurd h hne
  · exact ⟨k, mem_cone.mpr ⟨hkl, h1, h2, hkl, hrest⟩, hr⟩

lemma agree {N : ℕ} {C : Circuit} (x x' : Fin N → Bool)
    (hx : ∀ i : Fin N, (i : ℕ) ∈ dset N C → x i = x' i) :
    W N C x C.output = W N C x' C.output := by
  classical
  have key : ∀ w, ((w < N ∧ w ∈ dset N C) ∨ (N ≤ w ∧ w - N ∈ cone N C)) →
      W N C x w = W N C x' w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      rintro (⟨hw, hd⟩ | ⟨hw, hc⟩)
      · rw [W_input N C x w hw, W_input N C x' w hw]
        exact hx ⟨w, hw⟩ hd
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j ∈ cone N C := by simpa using hc
        have hjl : j < C.gates.length := (mem_cone.mp hj).1
        rw [W_gate N C x j hjl, W_gate N C x' j hjl]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        split_ifs with hij
        · apply ih i hij
          by_cases hiN : i < N
          · left
            refine ⟨hiN, ?_⟩
            simp only [dset, Finset.mem_filter, Finset.mem_range]
            exact ⟨hiN, Or.inl ⟨j, hj, hi⟩⟩
          · right
            refine ⟨by omega, ?_⟩
            exact cone_closed hj (by omega) (by rwa [show N + (i - N) = i by omega])
        · rfl
  by_cases ho : C.output < N
  · apply key _ (Or.inl ⟨ho, ?_⟩)
    unfold dset
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨ho, Or.inr rfl⟩
  · by_cases ho2 : C.output < N + C.gates.length
    · apply key _ (Or.inr ⟨by omega, ?_⟩)
      exact mem_cone.mpr ⟨by omega, by omega, by omega, by omega, Relation.ReflTransGen.refl⟩
    · simp only [W]
      rw [getD_ge_length _ _ (by rw [wires_length]; omega),
        getD_ge_length _ _ (by rw [wires_length]; omega)]

lemma count (N : ℕ) (C : Circuit) (hm : Monotone2 C) :
    (dset N C).card ≤ (cone N C).card + 1 := by
  classical
  by_cases ho : N ≤ C.output ∧ C.output - N < C.gates.length
  · have hjo : C.output - N ∈ cone N C :=
      mem_cone.mpr ⟨ho.2, ho.1, ho.2, ho.2, Relation.ReflTransGen.refl⟩
    have hU : ((cone N C).biUnion fun k => (gateAt C k).inputs.toFinset).card ≤
        2 * (cone N C).card := by
      calc ((cone N C).biUnion fun k => (gateAt C k).inputs.toFinset).card
          ≤ ∑ k ∈ cone N C, ((gateAt C k).inputs.toFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ cone N C, 2 := Finset.sum_le_sum fun k hk => by
            have hkl : k < C.gates.length := (mem_cone.mp hk).1
            have h2 := (hm (gateAt C k) (by rw [gateAt_eq C k hkl]; exact List.getElem_mem _)).2
            exact (List.toFinset_card_le _).trans h2
        _ = 2 * (cone N C).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hD : dset N C ⊆
        ((cone N C).biUnion fun k => (gateAt C k).inputs.toFinset).filter (· < N) := by
      intro i hi
      simp only [dset, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hiN, h | h⟩ := hi
      · obtain ⟨k, hk, hik⟩ := h
        simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset]
        exact ⟨⟨k, hk, hik⟩, hiN⟩
      · omega
    have hG : ((cone N C).erase (C.output - N)).image (N + ·) ⊆
        ((cone N C).biUnion fun k => (gateAt C k).inputs.toFinset).filter (fun i => ¬ i < N) := by
      intro w hw
      simp only [Finset.mem_image, Finset.mem_erase] at hw
      obtain ⟨j, ⟨hne, hj⟩, rfl⟩ := hw
      obtain ⟨k, hk, hr⟩ := cone_reader hj hne
      simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset]
      exact ⟨⟨k, hk, hr⟩, by omega⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (cone N C).biUnion fun k => (gateAt C k).inputs.toFinset) (fun i => i < N)
    have h1 := Finset.card_le_card hD
    have h2 := Finset.card_le_card hG
    rw [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)] at h2
    have h3 := Finset.card_erase_of_mem hjo
    have h4 := Finset.card_pos.mpr ⟨_, hjo⟩
    omega
  · have hc : cone N C = ∅ := by
      ext j
      simp only [Finset.notMem_empty, iff_false]
      intro h
      obtain ⟨-, h1, h2, -⟩ := mem_cone.mp h
      exact ho ⟨h1, h2⟩
    have hs : dset N C ⊆ {C.output} := by
      intro i hi
      simp only [dset, Finset.mem_filter, Finset.mem_range, hc, Finset.notMem_empty, false_and,
        exists_false, false_or] at hi
      simp [hi.2]
    rw [hc, Finset.card_empty]
    exact (Finset.card_le_card hs).trans (by simp)

lemma oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v =
      List.ofFn (fun i : Fin (n + m) => decide ((i : ℕ) = u) || decide ((i : ℕ) = n + v)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  congr 1
  · congr 1
    funext i
    have : ¬ ((i : ℕ) = n + v) := by omega
    simp [Fin.ext_iff, this]
  · congr 1
    funext j
    have : ¬ (n + (j : ℕ) = u) := by omega
    simp [Fin.ext_iff, this]

def ess {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun u : Fin n => ∃ v : Fin m, ∃ u' : Fin n, A u v = true ∧ A u' v = false)).image
      (fun u : Fin n => (u : ℕ)) ∪
    (Finset.univ.filter (fun v : Fin m => ∃ u : Fin n, ∃ v' : Fin m, A u v = true ∧ A u v' = false)).image
      (fun v : Fin m => n + (v : ℕ))

theorem lower {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents A C) : (ess A).card ≤ C.size + 1 := by
  classical
  have hsub : ess A ⊆ dset (n + m) C := by
    intro w hw
    simp only [ess, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hw
    rcases hw with ⟨u, ⟨v, u', h1, h2⟩, rfl⟩ | ⟨v, ⟨u, v', h1, h2⟩, rfl⟩
    · by_contra hnot
      have hxx : ∀ i : Fin (n + m), (i : ℕ) ∈ dset (n + m) C →
          (fun i : Fin (n + m) => decide ((i : ℕ) = u) || decide ((i : ℕ) = n + v)) i =
          (fun i : Fin (n + m) => decide ((i : ℕ) = n + v)) i := by
        intro i hi
        have : (i : ℕ) ≠ u := fun h => hnot (h ▸ hi)
        simp [this]
      have e1 := agree _ _ hxx
      have hA1 := hr u v
      have hA2 := hr u' v
      rw [oneEach_eq, h1] at hA1
      rw [oneEach_eq, h2] at hA2
      have hmono := Mono.wires_mono C hm
        (fun i : Fin (n + m) => decide ((i : ℕ) = n + v))
        (fun i : Fin (n + m) => decide ((i : ℕ) = u') || decide ((i : ℕ) = n + v))
        (fun i h => by simp only [decide_eq_true_eq] at h; simp [h]) C.output
      have h5 : W (n + m) C (fun i : Fin (n + m) => decide ((i : ℕ) = n + v)) C.output = true := by
        rw [← e1]; exact hA1
      have h6 := hmono h5
      have h7 : (C.wires (List.ofFn fun i : Fin (n + m) => decide ((i : ℕ) = u') ||
          decide ((i : ℕ) = n + v))).getD C.output false = false := hA2
      rw [h7] at h6
      exact Bool.false_ne_true h6
    · by_contra hnot
      have hxx : ∀ i : Fin (n + m), (i : ℕ) ∈ dset (n + m) C →
          (fun i : Fin (n + m) => decide ((i : ℕ) = u) || decide ((i : ℕ) = n + v)) i =
          (fun i : Fin (n + m) => decide ((i : ℕ) = u)) i := by
        intro i hi
        have : (i : ℕ) ≠ n + v := fun h => hnot (h ▸ hi)
        simp [this]
      have e1 := agree _ _ hxx
      have hA1 := hr u v
      have hA2 := hr u v'
      rw [oneEach_eq, h1] at hA1
      rw [oneEach_eq, h2] at hA2
      have hmono := Mono.wires_mono C hm
        (fun i : Fin (n + m) => decide ((i : ℕ) = u))
        (fun i : Fin (n + m) => decide ((i : ℕ) = u) || decide ((i : ℕ) = n + v'))
        (fun i h => by simp only [decide_eq_true_eq] at h; simp [h]) C.output
      have h5 : W (n + m) C (fun i : Fin (n + m) => decide ((i : ℕ) = u)) C.output = true := by
        rw [← e1]; exact hA1
      have h6 := hmono h5
      have h7 : (C.wires (List.ofFn fun i : Fin (n + m) => decide ((i : ℕ) = u) ||
          decide ((i : ℕ) = n + v'))).getD C.output false = false := hA2
      rw [h7] at h6
      exact Bool.false_ne_true h6
  have hcone : (cone (n + m) C).card ≤ C.size := by
    have : cone (n + m) C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
    simpa [Circuit.size] using Finset.card_le_card this
  calc (ess A).card ≤ (dset (n + m) C).card := Finset.card_le_card hsub
    _ ≤ (cone (n + m) C).card + 1 := count _ C hm
    _ ≤ C.size + 1 := by omega

end LB

def circ : Circuit :=
  { gates := [
    { op := GateOp.or, inputs := [3, 8] },
    { op := GateOp.or, inputs := [2, 7] },
    { op := GateOp.or, inputs := [5, 6] },
    { op := GateOp.or, inputs := [4, 12] },
    { op := GateOp.or, inputs := [10, 11] },
    { op := GateOp.and, inputs := [13, 14] }],
    output := 15 }

theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20603

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20603 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12684288 : ℕ).testBit (5 * u.val + v.val)) 6 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12684288 : ℕ).testBit (5 * u.val + v.val)) 5) :=
  ⟨⟨PEqualNP.Outside.L_meta_20603.circ, PEqualNP.Outside.L_meta_20603.mono, by decide, by decide⟩, by
    rintro ⟨C, hm, hs, hr⟩
    have h := PEqualNP.Outside.L_meta_20603.LB.lower _ C hm hr
    have he : (PEqualNP.Outside.L_meta_20603.LB.ess (fun u v : Fin 5 => (12684288 : ℕ).testBit (5 * u.val + v.val))).card = 7 := by decide +kernel
    omega⟩
