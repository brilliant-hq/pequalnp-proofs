import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17824

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)))
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


open PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.LowMerge
def inp (P L : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
lemma toList (P L : Finset (Fin 13)) : List.ofFn (inp P L) = incidenceInput P L :=
  List.ofFn_fin_append _ _
def q : Fin 3 → Finset (Fin 13) := ![{0,1,2,5},{3,4,7,9},{6,8,10,12}]
def x (k : Fin 3) := inp (q k) (missLines singerLines3 (q k))
def active : Fin 3 → Finset (Fin 26) := ![{3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,22,23,24,25},{0,1,2,5,6,8,10,11,12,13,14,15,16,17,19,20,21,22,24},{0,1,2,3,4,5,7,9,11,14,16,18,19,20,21,22,23,24,25}]
def wit : Fin 3 → Fin 26 → Fin 13 × Fin 13 := ![![(0,0),(0,0),(0,0),(3,3),(4,3),(0,0),(6,3),(7,7),(8,7),(9,8),(10,7),(11,8),(12,3),(0,0),(1,1),(2,2),(0,0),(0,4),(1,5),(2,6),(0,0),(0,0),(5,9),(0,10),(1,11),(0,12)],![(0,10),(1,5),(2,12),(0,0),(0,0),(5,5),(6,5),(0,0),(8,5),(0,0),(10,10),(11,10),(12,12),(3,0),(4,1),(3,2),(3,3),(4,4),(0,0),(7,6),(3,7),(4,8),(9,9),(0,0),(7,11),(0,0)],![(0,0),(1,0),(2,2),(3,0),(4,4),(5,2),(0,0),(7,4),(0,0),(9,0),(0,0),(11,2),(0,0),(0,0),(10,1),(0,0),(6,3),(0,0),(6,5),(6,6),(8,7),(8,8),(10,9),(6,10),(12,11),(8,12)]]

set_option maxRecDepth 10000 in
theorem cover : ∀ a b : Fin 26, ∃ k : Fin 3, a ∈ active k ∧ b ∈ active k := by decide +kernel
theorem quad_ok : ∀ k, IsQuadrangle singerLines3 (q k) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem witness_ok : ∀ k i, i ∈ active k →
    (wit k i).1 ∈ singerLines3 (wit k i).2 ∧
    ∀ j, inp {(wit k i).1} {(wit k i).2} j ≤ Function.update (x k) i true j := by
  decide +kernel

def Changes (C : Circuit) (u : ℕ) (i : Fin 26) : Prop :=
  ∃ z : Fin 26 → Bool, wireVal C (List.ofFn z) u = false ∧
    wireVal C (List.ofFn (Function.update z i true)) u = true

lemma changes_of_low (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (u : ℕ)
    (hr : RightOnIncidentPairs singerLines3 ⟨C.gates,u⟩) (k : Fin 3)
    (low : wireVal C (incidenceInput (q k) (missLines singerLines3 (q k))) u = false)
    (i : Fin 26) (hi : i ∈ active k) : Changes C u i := by
  refine ⟨x k, by simpa only [x,toList] using low, ?_⟩
  obtain ⟨hpair, hin⟩ := witness_ok k i hi
  have hv := hr (wit k i).2 (wit k i).1 hpair
  have h := (fold_R C.gates (fun g hg => (hm g hg).1) _ _ (R_ofFn _ _ hin)).2 u
  change wireVal C (List.ofFn (inp {(wit k i).1} {(wit k i).2})) u ≤
    wireVal C (List.ofFn (Function.update (x k) i true)) u at h
  rw [toList] at h
  change wireVal C (incidenceInput {(wit k i).1} {(wit k i).2}) u = true at hv
  rw [hv] at h
  exact le_antisymm (Bool.le_true _) h

lemma index_lb (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (u : ℕ) (hu : u < 26 + C.size) (h : ∀ i, Changes C u i) : 50 ≤ u := by
  by_contra! small
  let k := min C.gates.length 24
  have hk : k ≤ C.gates.length := Nat.min_le_left _ _
  have hk' : k ≤ 24 := Nat.min_le_right _ _
  have bound : u < 26+k := by
    change u < 26 + min C.gates.length 24
    change u < 26+C.gates.length at hu
    omega
  obtain ⟨T,hT,hd⟩ := dep 26 C (fun j hj => (hm _ (gateAt_mem hj)).2) k hk {u} (by simpa using bound)
  have eq : T = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra ni
    obtain ⟨z,hl,hh⟩ := h i
    have he := hd z (Function.update z i true) (by
      intro j hj
      have ne : j ≠ i := fun e => ni (e ▸ hj)
      simp [Function.update_of_ne ne]) u (by simp)
    change wireVal C _ u = wireVal C _ u at he
    rw [hl,hh] at he
    contradiction
  simp [eq] at hT
  omega

end PEqualNP.Outside.L_meta_17824
open PEqualNP.Outside.L_meta_17824 in
theorem PEqualNP.Outside.L_meta_17824 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x10 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x10 → PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x2 = Bool.false ∨ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x3 = Bool.false) → (50 : ℕ) ≤ Max.max x2 x3 ∧ ∃ x11 ∈ [x2, x3], ∀ (x12 : Fin (26 : ℕ)), ∃ (x13 : Fin (26 : ℕ) → Bool), PEqualNP.LowMerge.wireVal x1 (List.ofFn x13) x11 = Bool.false ∧ PEqualNP.LowMerge.wireVal x1 (List.ofFn (Function.update x13 x12 Bool.true)) x11 = Bool.true := by
  intro C u v hm _ hu hv hru hrv reject
  by_cases h : ∀ i, Changes C u i
  · exact ⟨(index_lb C hm u hu h).trans (le_max_left ..), u, by simp, h⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hh : ∀ j, Changes C v j := by
      intro j
      obtain ⟨k,hk,hk'⟩ := cover i j
      rcases reject (q k) (quad_ok k) with ha|hb
      · exact (hi (changes_of_low C hm u hru k ha i hk)).elim
      · exact changes_of_low C hm v hrv k hb j hk'
    exact ⟨(index_lb C hm v hv hh).trans (le_max_right ..), v, by simp, hh⟩
