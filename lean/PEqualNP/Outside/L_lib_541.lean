import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_541

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepW x

def wv {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq_runW (C : Circuit) (x : List Bool) : C.wires x = runW C.gates x := rfl

lemma runW_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    runW (gs ++ [g]) x = stepW (runW gs x) g := by
  simp [runW, List.foldl_append]

lemma runW_length (gs : List Gate) (x : List Bool) :
    (runW gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runW]
  | append_singleton gs g ih =>
    rw [runW_snoc]; simp [stepW, ih]; omega

lemma getD_snoc_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma runW_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (runW gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [runW_snoc, stepW, getD_snoc_lt _ _ _ (by rw [runW_length]; omega)]
    exact ih

lemma runW_getD_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (runW gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (runW gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    rw [runW_snoc]
    by_cases hlt : j < gs.length
    · have hlen : x.length + j < (runW gs x).length := by rw [runW_length]; omega
      rw [stepW, getD_snoc_lt _ _ _ hlen, ih hlt]
      simp only [List.getElem_append_left hlt]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + j
      · rw [if_pos hi, if_pos hi, getD_snoc_lt _ _ _ (by rw [runW_length]; omega)]
      · rw [if_neg hi, if_neg hi]
    · have heq : j = gs.length := by simp at hj; omega
      subst heq
      have hlen : (runW gs x).length = x.length + gs.length := runW_length gs x
      rw [stepW, ← hlen, getD_snoc_eq]
      simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < (runW gs x).length
      · rw [if_pos hi, getD_snoc_lt _ _ _ hi]
      · rw [if_neg hi, getD_ge _ _ (by omega)]

lemma wv_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wv C x i.val = x i := by
  unfold wv
  rw [wires_eq_runW, runW_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wv_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.size ≤ w) :
    wv C x w = false := by
  unfold wv
  rw [wires_eq_runW]
  apply getD_ge
  rw [runW_length, List.length_ofFn]
  exact hw

lemma wv_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.size) :
    wv C x (n + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < n + j then wv C x i else false) := by
  unfold wv
  rw [wires_eq_runW]
  have h := runW_getD_gate C.gates (List.ofFn x) j hj
  simpa only [List.length_ofFn] using h

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

lemma eff_eval_eq (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((eff g).map f) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rfl
  · rfl
  · cases ins with
    | nil => rfl
    | cons a tl => rfl

def IsConst {n : ℕ} (h : (Fin n → Bool) → Bool) : Prop :=
  ∃ c : Bool, ∀ x, h x = c

def Drops {n : ℕ} (F : ℕ → (Fin n → Bool) → Bool) (j : ℕ) : Prop :=
  IsConst (F (n + j)) ∨ ∃ u < n + j, ∀ x, F (n + j) x = F u x

lemma gate_eval_fold_not (f : (Fin n → Bool) → Bool) :
    ∀ (c : Bool), (∀ x, f x = c) → ∀ x, GateOp.not.eval [f x] = !c := by
  intro c hc x; simp [GateOp.eval, hc x]

lemma eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma eval_not1 (a : Bool) : GateOp.not.eval [a] = !a := rfl

lemma eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl
lemma eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl
lemma eval_and0 : GateOp.and.eval [] = true := rfl
lemma eval_or0 : GateOp.or.eval [] = false := rfl
lemma eval_not0 : GateOp.not.eval [] = true := rfl

lemma restrict_build (n : ℕ) (gs : List Gate) (F : ℕ → (Fin n → Bool) → Bool)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i < n, IsConst (F i) ∨ ∃ k < n, ∀ x, F i x = (List.ofFn x).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (x : Fin n → Bool),
      F (n + j) x = gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i x else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drops F j) ∧
      ds.length ≤ S.card ∧
      ∀ w < n + K, IsConst (F w) ∨
        ∃ k < n + ds.length, ∀ x, F w x = (runW ds (List.ofFn x)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [runW] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drops F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drops F K
    · refine ⟨ds, S, h1, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun x => (he x).trans (hc x)⟩
          · exact Or.inr ⟨k, hk, fun x => (he x).trans (hk' x)⟩
    · have addg : ∀ g : Gate, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
          g.inputs.length ≤ 2 →
          (∀ x, F (n + K) x = g.op.eval (g.inputs.map fun i => (runW ds (List.ofFn x)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drops F j) ∧
            ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), IsConst (F w) ∨
              ∃ k < n + ds.length, ∀ x, F w x = (runW ds (List.ofFn x)).getD k false := by
        intro g ho hl hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.mp h]; exact ⟨ho, hl⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun x => ?_⟩
              rw [runW_snoc, stepW, getD_snoc_lt _ _ _ (by rw [runW_length, List.length_ofFn]; exact hk)]
              exact hk' x
          · refine Or.inr ⟨n + ds.length, by simp, fun x => ?_⟩
            have hl' : (runW ds (List.ofFn x)).length = n + ds.length := by
              rw [runW_length, List.length_ofFn]
            rw [show w = n + K by omega, runW_snoc, stepW, ← hl', getD_snoc_eq]
            exact hg x
      have hval : ∀ i, (∃ c, ∀ x, (if i < n + K then F i x else false) = c) ∨
          (∃ k < n + ds.length, ∀ x, (if i < n + K then F i x else false) =
            (runW ds (List.ofFn x)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun x => by rw [if_pos hi]; exact hc x⟩
          · exact Or.inr ⟨k, hk, fun x => by rw [if_pos hi]; exact hk' x⟩
        · exact Or.inl ⟨false, fun x => by rw [if_neg hi]⟩
      have hKlt : K < gs.length := by omega
      have hFK := hF K hKlt
      obtain ⟨hop, hlen⟩ := hfan gs[K] (List.getElem_mem hKlt)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hls : gs[K].inputs with _ | ⟨a, _ | ⟨b, tl⟩⟩
        · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩; rw [hFK, hop, hls]; rfl
        · exfalso; apply hd
          by_cases ha : a < n + K
          · exact Or.inr ⟨a, ha, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, if_pos ha, eval_and1]⟩
          · exact Or.inl ⟨false, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, if_neg ha, eval_and1]⟩
        · have htl : tl = [] := by
            rw [hls] at hlen; cases tl <;> simp at hlen ⊢
          subst htl
          rcases hval a with ⟨ca, hca⟩ | ⟨ka, _, hka⟩ <;>
            rcases hval b with ⟨cb, hcb⟩ | ⟨kb, _, hkb⟩
          · exfalso; apply hd; left; refine ⟨ca && cb, fun x => ?_⟩
            rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hcb x, eval_and2]
          · cases ca
            · exfalso; apply hd; left; refine ⟨false, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, eval_and2, Bool.false_and]
            · exfalso; apply hd
              by_cases hb : b < n + K
              · exact Or.inr ⟨b, hb, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, if_pos hb, eval_and2, Bool.true_and]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, if_neg hb, eval_and2, Bool.true_and]⟩
          · cases cb
            · exfalso; apply hd; left; refine ⟨false, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, eval_and2, Bool.and_false]
            · exfalso; apply hd
              by_cases ha : a < n + K
              · exact Or.inr ⟨a, ha, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, if_pos ha, eval_and2, Bool.and_true]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, if_neg ha, eval_and2, Bool.and_true]⟩
          · exact addg ⟨GateOp.and, [ka, kb]⟩ (by simp) (by simp) (fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hka x, hkb x, eval_and2])
      · rcases hls : gs[K].inputs with _ | ⟨a, _ | ⟨b, tl⟩⟩
        · exfalso; apply hd; left; refine ⟨false, fun x => ?_⟩; rw [hFK, hop, hls]; rfl
        · exfalso; apply hd
          by_cases ha : a < n + K
          · exact Or.inr ⟨a, ha, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, if_pos ha, eval_or1]⟩
          · exact Or.inl ⟨false, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, if_neg ha, eval_or1]⟩
        · have htl : tl = [] := by
            rw [hls] at hlen; cases tl <;> simp at hlen ⊢
          subst htl
          rcases hval a with ⟨ca, hca⟩ | ⟨ka, _, hka⟩ <;>
            rcases hval b with ⟨cb, hcb⟩ | ⟨kb, _, hkb⟩
          · exfalso; apply hd; left; refine ⟨ca || cb, fun x => ?_⟩
            rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hcb x, eval_or2]
          · cases ca
            · exfalso; apply hd
              by_cases hb : b < n + K
              · exact Or.inr ⟨b, hb, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, if_pos hb, eval_or2, Bool.false_or]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, if_neg hb, eval_or2, Bool.false_or]⟩
            · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, eval_or2, Bool.true_or]
          · cases cb
            · exfalso; apply hd
              by_cases ha : a < n + K
              · exact Or.inr ⟨a, ha, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, if_pos ha, eval_or2, Bool.or_false]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, if_neg ha, eval_or2, Bool.or_false]⟩
            · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, eval_or2, Bool.or_true]
          · exact addg ⟨GateOp.or, [ka, kb]⟩ (by simp) (by simp) (fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hka x, hkb x, eval_or2])
      · rcases hls : gs[K].inputs with _ | ⟨a, tl⟩
        · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩; rw [hFK, hop, hls]; rfl
        · rcases hval a with ⟨ca, hca⟩ | ⟨ka, _, hka⟩
          · exfalso; apply hd; left; refine ⟨!ca, fun x => ?_⟩
            rw [hFK, hop, hls]; simp only [List.map_cons, GateOp.eval, List.headD, hca x]
          · exact addg ⟨GateOp.not, [ka]⟩ (by simp) (by simp) (fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, GateOp.eval, List.headD, hka x])

lemma shrink_of_drop {n : ℕ} (D : Circuit) (hfan : FanInTwo D)
    (F : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀ i < n, IsConst (F i) ∨ ∃ k < n, ∀ x, F i x = (List.ofFn x).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < D.size) (x : Fin n → Bool),
      F (n + j) x = D.gates[j].op.eval (D.gates[j].inputs.map fun i => if i < n + j then F i x else false))
    (hout_lt : D.output < n + D.size)
    (hnc : ¬ IsConst (F D.output))
    (j0 : ℕ) (hj0 : j0 < D.size) (hdrop : Drops F j0) :
    ∃ E : Circuit, FanInTwo E ∧ E.size < D.size ∧ ∀ x : Fin n → Bool, E.eval (List.ofFn x) = F D.output x := by
  obtain ⟨ds, S, h1, h2, h3, h4⟩ := restrict_build n D.gates F hfan hin hF D.size le_rfl
  have hSsub : S ⊆ (Finset.range D.size).erase j0 := by
    intro j hj
    have ⟨hlt, hnd⟩ := h2 j hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hlt⟩
    rintro rfl; exact hnd hdrop
  have hScard : S.card < D.gates.length := by
    have hle := Finset.card_le_card hSsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj0), Finset.card_range] at hle
    change D.gates.length - 1 ≥ S.card at hle
    change j0 < D.gates.length at hj0
    omega
  rcases h4 D.output hout_lt with hc | ⟨k, _, hk⟩
  · exact (hnc hc).elim
  · refine ⟨⟨ds, k⟩, h1, by change ds.length < D.gates.length; omega, fun x => (hk x).symm⟩

lemma shrink_of_dead {n : ℕ} (D : Circuit) (hfan : FanInTwo D)
    (j0 : ℕ) (hj0 : j0 < D.size) (hne_out : D.output ≠ n + j0)
    (hdead : ∀ k (hk : k < D.size), j0 < k → n + j0 ∉ eff D.gates[k]) :
    ∃ E : Circuit, FanInTwo E ∧ E.size < D.size ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x) := by
  have hj0' : j0 < D.gates.length := hj0
  let shift (u : ℕ) : ℕ := if n + j0 < u then u - 1 else u
  let mapG (g : Gate) : Gate := ⟨g.op, (eff g).map shift⟩
  let ds : List Gate := (List.range (D.gates.length - 1)).map (fun k =>
    if k < j0 then mapG (D.gates.getD k ⟨.or, []⟩) else mapG (D.gates.getD (k + 1) ⟨.or, []⟩))
  let E : Circuit := ⟨ds, shift D.output⟩
  have hElen : E.gates.length = D.gates.length - 1 := by simp [E, ds]
  have hEsize : E.size = D.size - 1 := hElen
  have hEfan : FanInTwo E := by
    intro g hg
    simp only [E, ds, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    have hget : ∀ m (hm : m < D.gates.length),
        (mapG (D.gates.getD m ⟨.or, []⟩)).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (mapG (D.gates.getD m ⟨.or, []⟩)).inputs.length ≤ 2 := by
      intro m hm
      have heq : D.gates.getD m ⟨.or, []⟩ = D.gates[m] := by
        simp [List.getD_eq_getElem?_getD, hm]
      rw [heq]
      obtain ⟨hop, hlen⟩ := hfan D.gates[m] (List.getElem_mem hm)
      refine ⟨hop, ?_⟩
      simp only [mapG, List.length_map, eff]
      cases D.gates[m].op <;> simp at hlen ⊢ <;> omega
    split_ifs with h
    · exact hget k (by omega)
    · exact hget (k + 1) (by omega)
  have hval : ∀ (x : Fin n → Bool) (w : ℕ), w ≠ n + j0 → wv E x (shift w) = wv D x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hne
      by_cases hw : w < n
      · have hs : shift w = w := by simp [shift]; omega
        rw [hs, wv_input E x ⟨w, hw⟩, wv_input D x ⟨w, hw⟩]
      · by_cases hge : n + D.gates.length ≤ w
        · have hs : n + E.size ≤ shift w := by
            change n + E.gates.length ≤ shift w; simp only [shift, hElen]; split_ifs <;> omega
          rw [wv_ge E x _ hs, wv_ge D x _ hge]
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < D.gates.length := by omega
          have hkj : k ≠ j0 := by omega
          by_cases hlt : k < j0
          · have hs : shift (n + k) = n + k := by simp [shift]; omega
            have hkE : k < E.size := by change k < E.gates.length; omega
            rw [hs, wv_gate E x k hkE, wv_gate D x k hk]
            have hgE : E.gates[k]'hkE = mapG D.gates[k] := by
              simp [E, ds, hlt, List.getD_eq_getElem?_getD, hk]
            rw [hgE, eff_eval_eq _ (hfan _ (List.getElem_mem hk)).1]
            simp only [mapG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u _
            simp only [Function.comp_apply]
            by_cases hu : u < n + k
            · have hsu : shift u = u := by simp [shift]; omega
              rw [if_pos hu, hsu, if_pos hu]
              have := ih u hu (by omega)
              rwa [hsu] at this
            · by_cases hsu : shift u < n + k
              · exfalso; simp only [shift] at hsu; split_ifs at hsu <;> omega
              · rw [if_neg hsu, if_neg hu]
          · have hgt : j0 < k := by omega
            have hs : shift (n + k) = n + (k - 1) := by simp only [shift]; split_ifs <;> omega
            have hkE : k - 1 < E.size := by change k - 1 < E.gates.length; omega
            rw [hs, wv_gate E x (k - 1) hkE, wv_gate D x k hk]
            have hgE : E.gates[k - 1]'hkE = mapG D.gates[k] := by
              have hnot : ¬ (k - 1 < j0) := by omega
              have hadd : k - 1 + 1 = k := by omega
              simp [E, ds, hnot, hadd, List.getD_eq_getElem?_getD, hk]
            rw [hgE, eff_eval_eq _ (hfan _ (List.getElem_mem hk)).1]
            simp only [mapG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu_mem
            simp only [Function.comp_apply]
            have hune : u ≠ n + j0 := fun h => hdead k hk hgt (h ▸ hu_mem)
            by_cases hu : u < n + k
            · have hsu : shift u < n + (k - 1) := by simp only [shift]; split_ifs <;> omega
              rw [if_pos hsu, if_pos hu]
              exact ih u hu hune
            · have hsu : ¬ shift u < n + (k - 1) := by simp only [shift]; split_ifs <;> omega
              rw [if_neg hsu, if_neg hu]
  refine ⟨E, hEfan, by change E.gates.length < D.gates.length; omega, fun x => hval x D.output hne_out⟩

lemma eval_congr_essential {n : ℕ} (f : (Fin n → Bool) → Bool)
    (ess : Finset (Fin n))
    (hess : ∀ j : Fin n, j ∉ ess → ∀ x : Fin n → Bool,
      f (Function.update x j false) = f (Function.update x j true)) :
    ∀ x y : Fin n → Bool, (∀ j ∈ ess, x j = y j) → f x = f y := by
  have hstep : ∀ (S : Finset (Fin n)) (x y : Fin n → Bool),
      (∀ j, j ∉ S → x j = y j) → (∀ j ∈ S, j ∉ ess) → f x = f y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x y h _
      have : x = y := funext (fun j => h j (by simp))
      rw [this]
    | @insert a S ha ih =>
      intro x y hxy hS
      let x' : Fin n → Bool := Function.update x a (y a)
      have hx' : f x = f x' := by
        have hne : a ∉ ess := hS a (Finset.mem_insert_self a S)
        have h01 := hess a hne x
        have heq1 : x = Function.update x a (x a) := (Function.update_eq_self a x).symm
        rw [heq1]
        cases hx_a : x a <;> cases hy_a : y a
        · simp [x', hx_a, hy_a]
        · simp only [x', hy_a]; exact h01
        · simp only [x', hy_a]; exact h01.symm
        · simp [x', hx_a, hy_a]
      rw [hx']
      apply ih x' y
      · intro j hj
        by_cases hja : j = a
        · subst hja; simp [x']
        · simp [x', hja, hxy j (by simp [hj, hja])]
      · intro j hj; exact hS j (Finset.mem_insert_of_mem hj)
  intro x y hxy
  apply hstep essᶜ x y
  · intro j hj
    have hj' : j ∈ ess := by simpa using hj
    exact hxy j hj'
  · intro j hj; exact Finset.mem_compl.mp hj

private lemma bool_and_le {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ && b₁) ≤ (a₂ && b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp_all

private lemma bool_or_le {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ || b₁) ≤ (a₂ || b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp_all

private lemma bool_not_le {a b : Bool} (h : a ≤ b) : (!b) ≤ (!a) := by
  cases a <;> cases b <;> simp_all

lemma main_proof (n : ℕ) (C : Circuit) (hCfan : FanInTwo C)
    (a b c : Fin n) (x0 : Fin n → Bool) (t : Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h100 : C.eval (List.ofFn (Function.update (Function.update (Function.update x0 a true) b false) c false)) = t)
    (h011 : C.eval (List.ofFn (Function.update (Function.update (Function.update x0 a false) b true) c true)) = t)
    (h010 : C.eval (List.ofFn (Function.update (Function.update (Function.update x0 a false) b true) c false)) = !t)
    (h001 : C.eval (List.ofFn (Function.update (Function.update (Function.update x0 a false) b false) c true)) = !t)
    (h110 : C.eval (List.ofFn (Function.update (Function.update (Function.update x0 a true) b true) c false)) = !t)
    (hy : ∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y c false)) = t ∧
      C.eval (List.ofFn (Function.update y c true)) = !t) :
    ((Finset.univ : Finset (Fin n)).filter (fun j =>
      ∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update x j false)) ≠
        C.eval (List.ofFn (Function.update x j true)))).card + 2 ≤ C.size := by
  classical
  let f : (Fin n → Bool) → Bool := fun x => C.eval (List.ofFn x)
  let ess : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun j =>
    ∃ x : Fin n → Bool, f (Function.update x j false) ≠ f (Function.update x j true))

  have hb_nonunate : (∃ x, f (Function.update x b false) = false ∧ f (Function.update x b true) = true) ∧
      (∃ x, f (Function.update x b false) = true ∧ f (Function.update x b true) = false) := by
    let x1 := Function.update (Function.update x0 a true) c false
    let x2 := Function.update (Function.update x0 a false) c true
    have e10 : Function.update x1 b false = Function.update (Function.update (Function.update x0 a true) b false) c false := by
      funext i; by_cases hi : i = c <;> by_cases hi2 : i = b <;> by_cases hi3 : i = a <;>
        simp [x1, hi, hi2, hi3, hbc, hbc.symm, hac, hac.symm, hab, hab.symm]
    have e11 : Function.update x1 b true = Function.update (Function.update (Function.update x0 a true) b true) c false := by
      funext i; by_cases hi : i = c <;> by_cases hi2 : i = b <;> by_cases hi3 : i = a <;>
        simp [x1, hi, hi2, hi3, hbc, hbc.symm, hac, hac.symm, hab, hab.symm]
    have e20 : Function.update x2 b false = Function.update (Function.update (Function.update x0 a false) b false) c true := by
      funext i; by_cases hi : i = c <;> by_cases hi2 : i = b <;> by_cases hi3 : i = a <;>
        simp [x2, hi, hi2, hi3, hbc, hbc.symm, hac, hac.symm, hab, hab.symm]
    have e21 : Function.update x2 b true = Function.update (Function.update (Function.update x0 a false) b true) c true := by
      funext i; by_cases hi : i = c <;> by_cases hi2 : i = b <;> by_cases hi3 : i = a <;>
        simp [x2, hi, hi2, hi3, hbc, hbc.symm, hac, hac.symm, hab, hab.symm]
    cases t
    · exact ⟨⟨x1, by rw [e10]; exact h100, by rw [e11]; exact h110⟩,
        ⟨x2, by rw [e20]; exact h001, by rw [e21]; exact h011⟩⟩
    · exact ⟨⟨x2, by rw [e20]; exact h001, by rw [e21]; exact h011⟩,
        ⟨x1, by rw [e10]; exact h100, by rw [e11]; exact h110⟩⟩
  have hc_nonunate : (∃ x, f (Function.update x c false) = false ∧ f (Function.update x c true) = true) ∧
      (∃ x, f (Function.update x c false) = true ∧ f (Function.update x c true) = false) := by
    obtain ⟨y, hy0, hy1⟩ := hy
    let x3 := Function.update (Function.update x0 a false) b true
    cases t
    · exact ⟨⟨y, hy0, hy1⟩, ⟨x3, h010, h011⟩⟩
    · exact ⟨⟨x3, h010, h011⟩, ⟨y, hy0, hy1⟩⟩
  have hb_ess : b ∈ ess := by
    obtain ⟨x, hx0, hx1⟩ := hb_nonunate.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, by rw [hx0, hx1]; decide⟩
  have hc_ess : c ∈ ess := by
    obtain ⟨x, hx0, hx1⟩ := hc_nonunate.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, by rw [hx0, hx1]; decide⟩
  have hf_nc : ¬ IsConst f := by
    rintro ⟨val, hval⟩
    obtain ⟨x, hx0, hx1⟩ := hb_nonunate.1
    have := (hval (Function.update x b false)).trans (hval (Function.update x b true)).symm
    rw [hx0, hx1] at this; exact absurd this (by decide)

  let P (k : ℕ) : Prop := ∃ D : Circuit, FanInTwo D ∧ D.size = k ∧ ∀ x, D.eval (List.ofFn x) = f x
  have hPex : ∃ k, P k := ⟨C.size, C, hCfan, rfl, fun _ => rfl⟩
  obtain ⟨D, hDfan, hDsz, hDeval⟩ := Nat.find_spec hPex
  have hDleC : D.size ≤ C.size := hDsz ▸ Nat.find_min' hPex ⟨C, hCfan, rfl, fun _ => rfl⟩
  have hDmin : ∀ E : Circuit, FanInTwo E → (∀ x, E.eval (List.ofFn x) = f x) → D.size ≤ E.size := by
    intro E hEfan hEeval
    rw [hDsz]
    exact Nat.find_min' hPex ⟨E, hEfan, rfl, hEeval⟩
  change ess.card + 2 ≤ C.size
  suffices hgoal : ess.card + 2 ≤ D.size by omega

  have hout_lt : D.output < n + D.size := by
    by_contra hge
    apply hf_nc
    refine ⟨false, fun x => ?_⟩
    rw [← hDeval x]
    exact wv_ge D x D.output (by omega)
  have hout_ge : n ≤ D.output := by
    by_contra hlt
    have hlt' : D.output < n := by omega
    obtain ⟨x, hx0, hx1⟩ := hb_nonunate.1
    obtain ⟨y, hy0, hy1⟩ := hb_nonunate.2
    have hdep : ∀ z : Fin n → Bool, f z = z ⟨D.output, hlt'⟩ := fun z => by
      rw [← hDeval z]; exact wv_input D z ⟨D.output, hlt'⟩
    have heq1 : b = ⟨D.output, hlt'⟩ := by
      by_contra hne
      rw [hdep, Function.update_of_ne (Ne.symm hne)] at hx0 hx1
      rw [hx0] at hx1; exact absurd hx1 (by decide)
    rw [hdep, ← heq1, Function.update_self] at hy0
    exact absurd hy0 (by decide)

  have hno_drop : ∀ j < D.size, ¬ Drops (fun w (x : Fin n → Bool) => wv D x w) j := by
    intro j hj hdrop
    have hout_eq : ∀ x, wv D x D.output = f x := hDeval
    obtain ⟨E, hEfan, hElt, hEeval⟩ := shrink_of_drop D hDfan (fun w (x : Fin n → Bool) => wv D x w)
      (fun i hi => Or.inr ⟨i, hi, fun x => by
        rw [wv_input D x ⟨i, hi⟩]; simp [List.getD_eq_getElem?_getD, hi]⟩)
      (fun k hk x => wv_gate D x k hk) hout_lt (by simpa [hout_eq] using hf_nc) j hj hdrop
    have hle := hDmin E hEfan (fun x => (hEeval x).trans (hout_eq x))
    omega

  have hgate_clean : ∀ j (hj : j < D.size),
      (D.gates[j].op = GateOp.not → ∃ u < n + j, eff D.gates[j] = [u]) ∧
      ((D.gates[j].op = GateOp.and ∨ D.gates[j].op = GateOp.or) →
        ∃ u v, u < n + j ∧ v < n + j ∧ u ≠ v ∧ eff D.gates[j] = [u, v]) := by
    intro j hj
    obtain ⟨hop, hlen⟩ := hDfan D.gates[j] (List.getElem_mem hj)
    constructor
    · intro hnot
      rcases hls : D.gates[j].inputs with _ | ⟨u, tl⟩
      · exfalso; apply hno_drop j hj; left
        refine ⟨true, fun x => ?_⟩; dsimp only; rw [wv_gate D x j hj, hnot, hls]; rfl
      · by_cases hu : u < n + j
        · exact ⟨u, hu, by simp [eff, hnot, hls]⟩
        · exfalso; apply hno_drop j hj; left
          refine ⟨true, fun x => ?_⟩; dsimp only; rw [wv_gate D x j hj, hnot, hls]; simp [GateOp.eval, hu]
    · intro hbin
      have heff : eff D.gates[j] = D.gates[j].inputs := by
        rcases hbin with h | h <;> simp [eff, h]
      rcases hls : D.gates[j].inputs with _ | ⟨u, _ | ⟨v, tl⟩⟩
      · exfalso; apply hno_drop j hj; left
        rcases hbin with h | h
        · exact ⟨true, fun x => by dsimp only; rw [wv_gate D x j hj, h, hls]; rfl⟩
        · exact ⟨false, fun x => by dsimp only; rw [wv_gate D x j hj, h, hls]; rfl⟩
      · exfalso; apply hno_drop j hj
        by_cases hu : u < n + j
        · right; refine ⟨u, hu, fun x => ?_⟩
          rcases hbin with h | h <;> simp [wv_gate D x j hj, h, hls, hu, eval_and1, eval_or1]
        · left; refine ⟨false, fun x => ?_⟩
          rcases hbin with h | h <;> simp [wv_gate D x j hj, h, hls, hu, eval_and1, eval_or1]
      · have htl : tl = [] := by rw [hls] at hlen; cases tl <;> simp at hlen ⊢
        subst htl
        by_cases hu : u < n + j
        · by_cases hv : v < n + j
          · by_cases huv : u = v
            · subst huv
              exfalso; apply hno_drop j hj; right
              refine ⟨u, hu, fun x => ?_⟩
              rcases hbin with h | h <;>
                simp [wv_gate D x j hj, h, hls, hu, eval_and2, eval_or2]
            · exact ⟨u, v, hu, hv, huv, by rw [heff, hls]⟩
          · exfalso; apply hno_drop j hj
            rcases hbin with h | h
            · left; exact ⟨false, fun x => by simp [wv_gate D x j hj, h, hls, hu, hv, eval_and2]⟩
            · right; exact ⟨u, hu, fun x => by simp [wv_gate D x j hj, h, hls, hu, hv, eval_or2]⟩
        · exfalso; apply hno_drop j hj
          rcases hbin with h | h
          · left; exact ⟨false, fun x => by simp [wv_gate D x j hj, h, hls, hu, eval_and2]⟩
          · by_cases hv : v < n + j
            · right; exact ⟨v, hv, fun x => by simp [wv_gate D x j hj, h, hls, hu, hv, eval_or2]⟩
            · left; exact ⟨false, fun x => by simp [wv_gate D x j hj, h, hls, hu, hv, eval_or2]⟩

  have hread_ess : ∀ j (hj : j < D.size) (u : ℕ), u ∈ eff D.gates[j] →
      ∀ (hu : u < n), ⟨u, hu⟩ ∈ ess := by
    intro j hj u hu_mem hu_lt
    by_contra hnot_ess
    have hinv : ∀ x : Fin n → Bool, f (Function.update x ⟨u, hu_lt⟩ false) = f x := by
      intro x
      apply eval_congr_essential f ess (fun i hi z => by
        by_contra hne; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hne⟩))
      intro i hi
      have hne : i ≠ ⟨u, hu_lt⟩ := fun h => hnot_ess (h ▸ hi)
      simp [hne]
    let F : ℕ → (Fin n → Bool) → Bool := fun w x => wv D (Function.update x ⟨u, hu_lt⟩ false) w
    have hFout : ∀ x, F D.output x = f x := fun x => (hDeval _).trans (hinv x)
    have hFdrop : Drops F j := by
      have hFu : ∀ x, F u x = false := fun x => by
        dsimp only [F]; rw [wv_input D _ ⟨u, hu_lt⟩]; simp
      obtain ⟨hop, _⟩ := hDfan D.gates[j] (List.getElem_mem hj)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hand | hor | hnot
      · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean j hj).2 (Or.inl hand)
        have hins : D.gates[j].inputs = [p, q] := by simpa [eff, hand] using heff
        rw [heff] at hu_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
        left; refine ⟨false, fun x => ?_⟩
        dsimp only [F]; rw [wv_gate D _ j hj, hand, hins]
        simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_and2]
        rcases hu_mem with rfl | rfl
        · change (F u x && _) = false; rw [hFu x]; rfl
        · change (_ && F u x) = false; rw [hFu x]; simp
      · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean j hj).2 (Or.inr hor)
        have hins : D.gates[j].inputs = [p, q] := by simpa [eff, hor] using heff
        rw [heff] at hu_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
        rcases hu_mem with rfl | rfl
        · right; refine ⟨q, hq, fun x => ?_⟩
          dsimp only [F]; rw [wv_gate D _ j hj, hor, hins]
          simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_or2]
          change (F u x || F q x) = F q x; rw [hFu x]; rfl
        · right; refine ⟨p, hp, fun x => ?_⟩
          dsimp only [F]; rw [wv_gate D _ j hj, hor, hins]
          simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_or2]
          change (F p x || F u x) = F p x; rw [hFu x]; simp
      · obtain ⟨p, hp, heff⟩ := (hgate_clean j hj).1 hnot
        rw [heff, List.mem_singleton] at hu_mem; subst hu_mem
        left; refine ⟨true, fun x => ?_⟩
        dsimp only [F]; rw [wv_gate D _ j hj, eff_eval_eq _ (by simp [hnot]), heff, hnot]
        simp only [List.map_cons, List.map_nil, if_pos hp, eval_not1]
        change !(F u x) = true; rw [hFu x]; rfl
    have hFout_eq : F D.output = f := funext hFout
    obtain ⟨E, hEfan, hElt, hEeval⟩ := shrink_of_drop D hDfan F
      (fun i hi => by
        by_cases hiu : i = u
        · subst hiu; exact Or.inl ⟨false, fun x => by dsimp only [F]; rw [wv_input D _ ⟨i, hi⟩]; simp⟩
        · refine Or.inr ⟨i, hi, fun x => ?_⟩
          dsimp only [F]; rw [wv_input D _ ⟨i, hi⟩]
          have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨u, hu_lt⟩ := fun h => hiu (congrArg Fin.val h)
          simp [hne, List.getD_eq_getElem?_getD, hi])
      (fun k hk x => wv_gate D _ k hk) hout_lt (by rw [hFout_eq]; exact hf_nc) j hj hFdrop
    have hle := hDmin E hEfan (fun x => (hEeval x).trans (hFout x))
    omega

  have hgate_live : ∀ j < D.size, D.output ≠ n + j →
      ∃ k, ∃ hk : k < D.size, j < k ∧ n + j ∈ eff D.gates[k] := by
    intro j hj hne
    by_contra hdead
    push_neg at hdead
    obtain ⟨E, hEfan, hElt, hEeval⟩ := shrink_of_dead D hDfan j hj hne hdead
    have hle := hDmin E hEfan (fun x => (hEeval x).trans (hDeval x))
    omega

  have heff_lt : ∀ k (hk : k < D.size) u, u ∈ eff D.gates[k] → u < n + k := by
    intro k hk u hu
    obtain ⟨hop, _⟩ := hDfan D.gates[k] (List.getElem_mem hk)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inl h)
      rw [heff] at hu; simp at hu; rcases hu with rfl | rfl <;> assumption
    · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inr h)
      rw [heff] at hu; simp at hu; rcases hu with rfl | rfl <;> assumption
    · obtain ⟨p, hp, heff⟩ := (hgate_clean k hk).1 h
      rw [heff] at hu; simp at hu; subst hu; exact hp

  have hout_last : D.output = n + (D.size - 1) := by
    by_contra hne
    obtain ⟨k, hk, hlt, _⟩ := hgate_live (D.size - 1) (by omega) hne
    omega

  have hess_read : ∀ i ∈ ess, ∃ k, ∃ hk : k < D.size, i.val ∈ eff D.gates[k] := by
    intro i hi
    by_contra hno
    push_neg at hno
    have hsame : ∀ (x y : Fin n → Bool), (∀ j : Fin n, j ≠ i → x j = y j) →
        ∀ w, w ≠ i.val → wv D x w = wv D y w := by
      intro x y hxy w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hne
        by_cases hw : w < n
        · rw [wv_input D x ⟨w, hw⟩, wv_input D y ⟨w, hw⟩]
          exact hxy ⟨w, hw⟩ (fun h => hne (congrArg Fin.val h))
        · by_cases hge : n + D.size ≤ w
          · rw [wv_ge D x w hge, wv_ge D y w hge]
          · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
            have hk : k < D.size := by omega
            rw [wv_gate D x k hk, wv_gate D y k hk,
              eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1,
              eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := heff_lt k hk u hu
            rw [if_pos hult, if_pos hult]
            exact ih u hult (fun h => hno k hk (h ▸ hu))
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
    apply hx
    rw [← hDeval, ← hDeval]
    exact hsame _ _ (fun j hj => by simp [hj]) D.output (by have := i.isLt; omega)

  let Nodes : Finset ℕ := ess.image Fin.val ∪ (Finset.range D.size).image (n + ·)
  let readers (u : ℕ) : Finset ℕ :=
    (Finset.range D.size).filter (fun k => if hk : k < D.size then u ∈ eff D.gates[k] else false)
  let outdeg (u : ℕ) : ℕ := (readers u).card
  let Gnot : Finset ℕ := (Finset.range D.size).filter (fun k =>
    if hk : k < D.size then D.gates[k].op = GateOp.not else false)
  let Gbin : Finset ℕ := (Finset.range D.size).filter (fun k =>
    if hk : k < D.size then D.gates[k].op = GateOp.and ∨ D.gates[k].op = GateOp.or else false)
  have hNodes_card : Nodes.card = ess.card + D.size := by
    have hdisj : Disjoint (ess.image Fin.val) ((Finset.range D.size).image (n + ·)) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h2
      have := i.isLt; omega
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have hBN : Gbin.card + Gnot.card = D.size := by
    have hdisj : Disjoint Gbin Gnot := by
      rw [Finset.disjoint_left]
      intro k h1 h2
      simp only [Gbin, Gnot, Finset.mem_filter, Finset.mem_range] at h1 h2
      have hk := h1.1
      rw [dif_pos hk] at h1 h2
      rcases h1.2 with h | h <;> rw [h] at h2 <;> cases h2.2
    have hunion : Gbin ∪ Gnot = Finset.range D.size := by
      ext k
      simp only [Gbin, Gnot, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hk
        have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with h | h | h
        · left; exact ⟨hk, by rw [dif_pos hk]; exact Or.inl h⟩
        · left; exact ⟨hk, by rw [dif_pos hk]; exact Or.inr h⟩
        · right; exact ⟨hk, by rw [dif_pos hk]; exact h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
  have hsum_deg : ∑ u ∈ Nodes, outdeg u = 2 * Gbin.card + Gnot.card := by
    have hswap : ∑ u ∈ Nodes, outdeg u =
        ∑ k ∈ Finset.range D.size, (Nodes.filter (fun u =>
          if hk : k < D.size then u ∈ eff D.gates[k] else false)).card := by
      simp only [outdeg, readers, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    have hterm : ∀ k ∈ Finset.range D.size,
        (Nodes.filter (fun u => if hk : k < D.size then u ∈ eff D.gates[k] else false)).card =
          if k ∈ Gbin then 2 else 1 := by
      intro k hk
      have hk' : k < D.size := Finset.mem_range.mp hk
      have hmem_nodes : ∀ u, u ∈ eff D.gates[k] → u ∈ Nodes := by
        intro u hu
        have hlt := heff_lt k hk' u hu
        by_cases hun : u < n
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨u, hun⟩, hread_ess k hk' u hu hun, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u - n, Finset.mem_range.mpr (by omega), by omega⟩)
      have hop := (hDfan D.gates[k] (List.getElem_mem hk')).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · obtain ⟨p, q, _, _, hpq, heff⟩ := (hgate_clean k hk').2 (Or.inl h)
        have hkb : k ∈ Gbin := Finset.mem_filter.mpr ⟨hk, by rw [dif_pos hk']; exact Or.inl h⟩
        rw [if_pos hkb]
        have hfilt : Nodes.filter (fun u => if hk2 : k < D.size then u ∈ eff D.gates[k] else false) = {p, q} := by
          ext u
          simp only [Finset.mem_filter, dif_pos hk', heff, List.mem_cons, List.not_mem_nil, or_false,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨hmem_nodes u (by rw [heff]; simpa using h), h⟩⟩
        rw [hfilt, Finset.card_pair hpq]
      · obtain ⟨p, q, _, _, hpq, heff⟩ := (hgate_clean k hk').2 (Or.inr h)
        have hkb : k ∈ Gbin := Finset.mem_filter.mpr ⟨hk, by rw [dif_pos hk']; exact Or.inr h⟩
        rw [if_pos hkb]
        have hfilt : Nodes.filter (fun u => if hk2 : k < D.size then u ∈ eff D.gates[k] else false) = {p, q} := by
          ext u
          simp only [Finset.mem_filter, dif_pos hk', heff, List.mem_cons, List.not_mem_nil, or_false,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨hmem_nodes u (by rw [heff]; simpa using h), h⟩⟩
        rw [hfilt, Finset.card_pair hpq]
      · obtain ⟨p, _, heff⟩ := (hgate_clean k hk').1 h
        have hkb : k ∉ Gbin := by
          intro hm
          simp only [Gbin, Finset.mem_filter, dif_pos hk', h] at hm
          rcases hm.2 with h1 | h1 <;> cases h1
        rw [if_neg hkb]
        have hfilt : Nodes.filter (fun u => if hk2 : k < D.size then u ∈ eff D.gates[k] else false) = {p} := by
          ext u
          simp only [Finset.mem_filter, dif_pos hk', heff, List.mem_singleton, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨hmem_nodes u (by rw [heff]; simpa using h), h⟩⟩
        rw [hfilt, Finset.card_singleton]
    rw [Finset.sum_congr rfl hterm]
    have hsplit : ∑ k ∈ Finset.range D.size, (if k ∈ Gbin then (2 : ℕ) else 1) =
        2 * Gbin.card + (Finset.range D.size \ Gbin).card := by
      have hsub : Gbin ⊆ Finset.range D.size := Finset.filter_subset _ _
      rw [← Finset.sum_sdiff hsub]
      have h1 : ∑ k ∈ Gbin, (if k ∈ Gbin then (2 : ℕ) else 1) = 2 * Gbin.card := by
        rw [Finset.sum_congr rfl (fun k hk => if_pos hk), Finset.sum_const, smul_eq_mul, mul_comm]
      have h2 : ∑ k ∈ Finset.range D.size \ Gbin, (if k ∈ Gbin then (2 : ℕ) else 1) =
          (Finset.range D.size \ Gbin).card := by
        rw [Finset.sum_congr rfl (fun k hk => if_neg (Finset.mem_sdiff.mp hk).2),
          Finset.sum_const, smul_eq_mul, mul_one]
      rw [h1, h2, add_comm]
    rw [hsplit]
    have hsdiff : (Finset.range D.size \ Gbin).card = Gnot.card := by
      have hsub : Gbin ⊆ Finset.range D.size := Finset.filter_subset _ _
      have := Finset.card_sdiff (s := Gbin) (t := Finset.range D.size)
      rw [Finset.inter_eq_left.mpr hsub, Finset.card_range] at this
      omega
    rw [hsdiff]

  have hout_mem : D.output ∈ Nodes :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D.output - n, Finset.mem_range.mpr (by omega), by omega⟩)
  have hout_deg0 : outdeg D.output = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hk
    have hk' := hk.1
    rw [dif_pos hk'] at hk
    have hlt := heff_lt k hk' D.output hk.2
    omega
  have hpos_deg : ∀ u ∈ Nodes.erase D.output, 1 ≤ outdeg u := by
    intro u hu
    have ⟨hne, hmem⟩ := Finset.mem_erase.mp hu
    rcases Finset.mem_union.mp hmem with h1 | h2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨k, hk, hkin⟩ := hess_read i hi
      exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rw [dif_pos hk]; exact hkin⟩⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h2
      obtain ⟨k, hk, _, hkin⟩ := hgate_live j (Finset.mem_range.mp hj) hne.symm
      exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rw [dif_pos hk]; exact hkin⟩⟩
  let F : ℕ := ∑ u ∈ Nodes.erase D.output, (outdeg u - 1)
  have hF_eq : ess.card + D.size - 1 + F = 2 * Gbin.card + Gnot.card := by
    have h1 : ∑ u ∈ Nodes, outdeg u = outdeg D.output + ∑ u ∈ Nodes.erase D.output, outdeg u :=
      (Finset.add_sum_erase Nodes outdeg hout_mem).symm
    have h2 : ∑ u ∈ Nodes.erase D.output, outdeg u = (Nodes.erase D.output).card + F := by
      have hterm : ∀ u ∈ Nodes.erase D.output, outdeg u = 1 + (outdeg u - 1) := fun u hu => by
        have := hpos_deg u hu; omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hsum_deg, hout_deg0, zero_add, h2, Finset.card_erase_of_mem hout_mem, hNodes_card] at h1
    omega

  by_contra hlt_goal
  have hFN : F + Gnot.card ≤ 2 := by omega

  let Step (u w : ℕ) : Prop := ∃ k, ∃ hk : k < D.size, w = n + k ∧ u ∈ eff D.gates[k]
  let Reach (u w : ℕ) : Prop := Relation.ReflTransGen Step u w
  have hReach_le : ∀ u w, Reach u w → u ≤ w := by
    intro u w h
    induction h with
    | refl => exact le_rfl
    | @tail y z _ hstep ih =>
      obtain ⟨k, hk, rfl, hmem⟩ := hstep
      have := heff_lt k hk y hmem
      omega
  have hnot_reach_indep : ∀ (v : Fin n) (w : ℕ), ¬ Reach v.val w →
      ∀ x : Fin n → Bool, wv D (Function.update x v false) w = wv D (Function.update x v true) w := by
    intro v w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hnr x
      by_cases hw : w < n
      · rw [wv_input D _ ⟨w, hw⟩, wv_input D _ ⟨w, hw⟩]
        have hne : (⟨w, hw⟩ : Fin n) ≠ v := by
          intro h; apply hnr; rw [← congrArg Fin.val h]
        simp [hne]
      · by_cases hge : n + D.size ≤ w
        · rw [wv_ge D _ w hge, wv_ge D _ w hge]
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < D.size := by omega
          rw [wv_gate D _ k hk, wv_gate D _ k hk,
            eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1,
            eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := heff_lt k hk u hu
          rw [if_pos hult, if_pos hult]
          apply ih u hult
          intro hr
          exact hnr (Relation.ReflTransGen.tail hr ⟨k, hk, rfl, hu⟩)

  have hN_pos : 1 ≤ Gnot.card := by
    by_contra hN0
    have hnoNot : ∀ k (hk : k < D.size), D.gates[k].op ≠ GateOp.not := by
      intro k hk hnot
      have hmem : k ∈ Gnot := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rw [dif_pos hk]; exact hnot⟩
      have hpos : 0 < Gnot.card := Finset.card_pos.mpr ⟨k, hmem⟩
      omega
    have hmono : ∀ (x y : Fin n → Bool), (∀ i, x i ≤ y i) → ∀ w, wv D x w ≤ wv D y w := by
      intro x y hxy w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        by_cases hw : w < n
        · rw [wv_input D x ⟨w, hw⟩, wv_input D y ⟨w, hw⟩]; exact hxy ⟨w, hw⟩
        · by_cases hge : n + D.size ≤ w
          · rw [wv_ge D x w hge, wv_ge D y w hge]
          · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
            have hk : k < D.size := by omega
            have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hand | hor | hnot
            · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inl hand)
              rw [wv_gate D x k hk, wv_gate D y k hk,
                eff_eval_eq _ (by simp [hand]), eff_eval_eq _ (by simp [hand]), heff, hand]
              simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_and2]
              exact bool_and_le (ih p hp) (ih q hq)
            · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inr hor)
              rw [wv_gate D x k hk, wv_gate D y k hk,
                eff_eval_eq _ (by simp [hor]), eff_eval_eq _ (by simp [hor]), heff, hor]
              simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_or2]
              exact bool_or_le (ih p hp) (ih q hq)
            · exact (hnoNot k hk hnot).elim
    obtain ⟨y, hy0, hy1⟩ := hb_nonunate.2
    have hle : f (Function.update y b false) ≤ f (Function.update y b true) := by
      rw [← hDeval, ← hDeval]
      exact hmono (Function.update y b false) (Function.update y b true) (fun i => by
        by_cases hi : i = b <;> simp [hi]) D.output
    rw [hy0, hy1] at hle
    exact absurd hle (by decide)

  have heff_mem_Nodes : ∀ k (hk : k < D.size) u, u ∈ eff D.gates[k] → u ∈ Nodes := by
    intro k hk u hu
    have hlt := heff_lt k hk u hu
    by_cases hun : u < n
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨u, hun⟩, hread_ess k hk u hu hun, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u - n, Finset.mem_range.mpr (by omega), by omega⟩)

  have hstep_det : ∀ u w₁ w₂, outdeg u ≤ 1 → Step u w₁ → Step u w₂ → w₁ = w₂ := by
    intro u w₁ w₂ hd ⟨k₁, hk₁, h1eq, hm₁⟩ ⟨k₂, hk₂, h2eq, hm₂⟩
    have h1 : k₁ ∈ readers u := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk₁, by rw [dif_pos hk₁]; exact hm₁⟩
    have h2 : k₂ ∈ readers u := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk₂, by rw [dif_pos hk₂]; exact hm₂⟩
    have heq := Finset.card_le_one.mp hd k₁ h1 k₂ h2
    rw [h1eq, h2eq, heq]

  have hreach_total : ∀ u w₁ w₂, (∀ z, Reach u z → outdeg z ≤ 1) →
      Reach u w₁ → Reach u w₂ → Reach w₁ w₂ ∨ Reach w₂ w₁ := by
    intro u w₁ w₂ hout h1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => intro h2; exact Or.inl h2
    | @head a b hstep h1' ih =>
      intro h2
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨b', hstep', h2'⟩
      · exact Or.inr (Relation.ReflTransGen.head hstep h1')
      · have hbb : b = b' := hstep_det a b b' (hout a Relation.ReflTransGen.refl) hstep hstep'
        subst hbb
        exact ih (fun z hz => hout z (Relation.ReflTransGen.head hstep hz)) h2'

  have htree_unate : ∀ (v : Fin n) (stop : ℕ),
      (∀ u, Reach v.val u → u < stop → outdeg u ≤ 1) →
      (∀ x, wv D (Function.update x v false) stop ≤ wv D (Function.update x v true) stop) ∨
      (∀ x, wv D (Function.update x v true) stop ≤ wv D (Function.update x v false) stop) := by
    intro v stop hout1
    have haux : ∀ w ≤ stop,
        (∀ x, wv D (Function.update x v false) w ≤ wv D (Function.update x v true) w) ∨
        (∀ x, wv D (Function.update x v true) w ≤ wv D (Function.update x v false) w) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hwle
        by_cases hw : w < n
        · left; intro x
          rw [wv_input D _ ⟨w, hw⟩, wv_input D _ ⟨w, hw⟩]
          by_cases heq : (⟨w, hw⟩ : Fin n) = v <;> simp [heq]
        · by_cases hge : n + D.size ≤ w
          · left; intro x; rw [wv_ge D _ w hge, wv_ge D _ w hge]
          · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
            have hk : k < D.size := by omega
            have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hand | hor | hnot
            · obtain ⟨p, q, hp, hq, hpq, heff⟩ := (hgate_clean k hk).2 (Or.inl hand)
              have hnot_both : ¬ (Reach v.val p ∧ Reach v.val q) := by
                rintro ⟨hrp, hrq⟩
                have hout_lt : ∀ z, Reach v.val z → z < n + k → outdeg z ≤ 1 :=
                  fun z hz hlt => hout1 z hz (by omega)

                have htot_lt : ∀ u w₁ w₂, (∀ z, Reach u z → z < n + k → outdeg z ≤ 1) →
                    Reach u w₁ → w₁ < n + k → Reach u w₂ → w₂ < n + k → Reach w₁ w₂ ∨ Reach w₂ w₁ := by
                  intro u w₁ w₂ ho h1
                  induction h1 using Relation.ReflTransGen.head_induction_on with
                  | refl => intro _ h2 _; exact Or.inl h2
                  | @head a b hst h1' ih' =>
                    intro hw1 h2 hw2
                    rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨b', hst', h2'⟩
                    · exact Or.inr (Relation.ReflTransGen.head hst h1')
                    · have ha_lt : a < n + k := lt_of_le_of_lt (hReach_le a w₁ (Relation.ReflTransGen.head hst h1')) hw1
                      have hbb : b = b' := hstep_det a b b' (ho a Relation.ReflTransGen.refl ha_lt) hst hst'
                      subst hbb
                      exact ih' (fun z hz hzl => ho z (Relation.ReflTransGen.head hst hz) hzl) hw1 h2' hw2
                rcases htot_lt v.val p q hout_lt hrp hp hrq hq with hpq_r | hqp_r
                · rcases Relation.ReflTransGen.cases_head hpq_r with rfl | ⟨y, hpy, hyq⟩
                  · exact hpq rfl
                  · have hstep_pk : Step p (n + k) := ⟨k, hk, rfl, by rw [heff]; simp⟩
                    have hyeq : y = n + k := hstep_det p y (n + k) (hout_lt p hrp hp) hpy hstep_pk
                    subst hyeq
                    have := hReach_le (n + k) q hyq; omega
                · rcases Relation.ReflTransGen.cases_head hqp_r with rfl | ⟨y, hqy, hyp⟩
                  · exact hpq rfl
                  · have hstep_qk : Step q (n + k) := ⟨k, hk, rfl, by rw [heff]; simp⟩
                    have hyeq : y = n + k := hstep_det q y (n + k) (hout_lt q hrq hq) hqy hstep_qk
                    subst hyeq
                    have := hReach_le (n + k) p hyp; omega
              have hrew : ∀ x, wv D x (n + k) = (wv D x p && wv D x q) := fun x => by
                rw [wv_gate D x k hk, eff_eval_eq _ (by simp [hand]), heff, hand]
                simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_and2]
              by_cases hrp : Reach v.val p
              · have hrq : ¬ Reach v.val q := fun h => hnot_both ⟨hrp, h⟩
                have hq_eq := hnot_reach_indep v q hrq
                rcases ih p hp (by omega) with hinc | hdec
                · left; intro x; rw [hrew, hrew, hq_eq x]; exact bool_and_le (hinc x) le_rfl
                · right; intro x; rw [hrew, hrew, hq_eq x]; exact bool_and_le (hdec x) le_rfl
              · have hp_eq := hnot_reach_indep v p hrp
                rcases ih q hq (by omega) with hinc | hdec
                · left; intro x; rw [hrew, hrew, hp_eq x]; exact bool_and_le le_rfl (hinc x)
                · right; intro x; rw [hrew, hrew, hp_eq x]; exact bool_and_le le_rfl (hdec x)
            · obtain ⟨p, q, hp, hq, hpq, heff⟩ := (hgate_clean k hk).2 (Or.inr hor)
              have hnot_both : ¬ (Reach v.val p ∧ Reach v.val q) := by
                rintro ⟨hrp, hrq⟩
                have hout_lt : ∀ z, Reach v.val z → z < n + k → outdeg z ≤ 1 :=
                  fun z hz hlt => hout1 z hz (by omega)
                have htot_lt : ∀ u w₁ w₂, (∀ z, Reach u z → z < n + k → outdeg z ≤ 1) →
                    Reach u w₁ → w₁ < n + k → Reach u w₂ → w₂ < n + k → Reach w₁ w₂ ∨ Reach w₂ w₁ := by
                  intro u w₁ w₂ ho h1
                  induction h1 using Relation.ReflTransGen.head_induction_on with
                  | refl => intro _ h2 _; exact Or.inl h2
                  | @head a b hst h1' ih' =>
                    intro hw1 h2 hw2
                    rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨b', hst', h2'⟩
                    · exact Or.inr (Relation.ReflTransGen.head hst h1')
                    · have ha_lt : a < n + k := lt_of_le_of_lt (hReach_le a w₁ (Relation.ReflTransGen.head hst h1')) hw1
                      have hbb : b = b' := hstep_det a b b' (ho a Relation.ReflTransGen.refl ha_lt) hst hst'
                      subst hbb
                      exact ih' (fun z hz hzl => ho z (Relation.ReflTransGen.head hst hz) hzl) hw1 h2' hw2
                rcases htot_lt v.val p q hout_lt hrp hp hrq hq with hpq_r | hqp_r
                · rcases Relation.ReflTransGen.cases_head hpq_r with rfl | ⟨y, hpy, hyq⟩
                  · exact hpq rfl
                  · have hstep_pk : Step p (n + k) := ⟨k, hk, rfl, by rw [heff]; simp⟩
                    have hyeq : y = n + k := hstep_det p y (n + k) (hout_lt p hrp hp) hpy hstep_pk
                    subst hyeq
                    have := hReach_le (n + k) q hyq; omega
                · rcases Relation.ReflTransGen.cases_head hqp_r with rfl | ⟨y, hqy, hyp⟩
                  · exact hpq rfl
                  · have hstep_qk : Step q (n + k) := ⟨k, hk, rfl, by rw [heff]; simp⟩
                    have hyeq : y = n + k := hstep_det q y (n + k) (hout_lt q hrq hq) hqy hstep_qk
                    subst hyeq
                    have := hReach_le (n + k) p hyp; omega
              have hrew : ∀ x, wv D x (n + k) = (wv D x p || wv D x q) := fun x => by
                rw [wv_gate D x k hk, eff_eval_eq _ (by simp [hor]), heff, hor]
                simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_or2]
              by_cases hrp : Reach v.val p
              · have hrq : ¬ Reach v.val q := fun h => hnot_both ⟨hrp, h⟩
                have hq_eq := hnot_reach_indep v q hrq
                rcases ih p hp (by omega) with hinc | hdec
                · left; intro x; rw [hrew, hrew, hq_eq x]; exact bool_or_le (hinc x) le_rfl
                · right; intro x; rw [hrew, hrew, hq_eq x]; exact bool_or_le (hdec x) le_rfl
              · have hp_eq := hnot_reach_indep v p hrp
                rcases ih q hq (by omega) with hinc | hdec
                · left; intro x; rw [hrew, hrew, hp_eq x]; exact bool_or_le le_rfl (hinc x)
                · right; intro x; rw [hrew, hrew, hp_eq x]; exact bool_or_le le_rfl (hdec x)
            · obtain ⟨p, hp, heff⟩ := (hgate_clean k hk).1 hnot
              have hrew : ∀ x, wv D x (n + k) = !(wv D x p) := fun x => by
                rw [wv_gate D x k hk, eff_eval_eq _ (by simp [hnot]), heff, hnot]
                simp only [List.map_cons, List.map_nil, if_pos hp, eval_not1]
              rcases ih p hp (by omega) with hinc | hdec
              · right; intro x; rw [hrew, hrew]; exact bool_not_le (hinc x)
              · left; intro x; rw [hrew, hrew]; exact bool_not_le (hdec x)
    exact haux stop le_rfl

  by_cases hF0 : F = 0
  · have hout1 : ∀ u, Reach b.val u → u < D.output → outdeg u ≤ 1 := by
      intro u hu hlt
      by_cases hmem : u ∈ Nodes.erase D.output
      · have h0 : outdeg u - 1 = 0 := by
          have := Finset.single_le_sum (f := fun z => outdeg z - 1) (fun _ _ => Nat.zero_le _) hmem
          omega
        omega
      · have hu_in : u ∈ Nodes := by
          induction hu with
          | refl => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb_ess, rfl⟩)
          | @tail y z _ hstep _ =>
            obtain ⟨k, hk, rfl, _⟩ := hstep
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)
        exact (hmem (Finset.mem_erase.mpr ⟨by omega, hu_in⟩)).elim
    rcases htree_unate b D.output hout1 with hinc | hdec
    · obtain ⟨y, hy0, hy1⟩ := hb_nonunate.2
      have hle : f (Function.update y b false) ≤ f (Function.update y b true) := by
        rw [← hDeval, ← hDeval]; exact hinc y
      rw [hy0, hy1] at hle; exact absurd hle (by decide)
    · obtain ⟨x, hx0, hx1⟩ := hb_nonunate.1
      have hle : f (Function.update x b true) ≤ f (Function.update x b false) := by
        rw [← hDeval, ← hDeval]; exact hdec x
      rw [hx0, hx1] at hle; exact absurd hle (by decide)
  ·
    have hF1 : F = 1 := by omega
    have hN1 : Gnot.card = 1 := by omega
    obtain ⟨ν, hν_eq⟩ := Finset.card_eq_one.mp hN1
    have hν_mem : ν ∈ Gnot := by rw [hν_eq]; simp
    have hν_lt : ν < D.size := Finset.mem_range.mp (Finset.mem_filter.mp hν_mem).1
    have hν_op : D.gates[ν].op = GateOp.not := by
      have h := (Finset.mem_filter.mp hν_mem).2; rwa [dif_pos hν_lt] at h
    have hnot_unique : ∀ k (hk : k < D.size), D.gates[k].op = GateOp.not → k = ν := by
      intro k hk hnot
      have hm : k ∈ Gnot := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rw [dif_pos hk]; exact hnot⟩
      rw [hν_eq] at hm; exact Finset.mem_singleton.mp hm

    have hfork_ex : ∃ wstar ∈ Nodes.erase D.output, outdeg wstar = 2 ∧
        ∀ u ∈ Nodes.erase D.output, u ≠ wstar → outdeg u ≤ 1 := by
      have hex : ∃ wstar ∈ Nodes.erase D.output, 0 < outdeg wstar - 1 := by
        by_contra hall
        push_neg at hall
        have h0 : F = 0 := Finset.sum_eq_zero (fun u hu => Nat.le_zero.mp (hall u hu))
        omega
      obtain ⟨wstar, hw_mem, hw_pos⟩ := hex
      have hw_le : outdeg wstar - 1 ≤ F :=
        Finset.single_le_sum (f := fun z => outdeg z - 1) (fun _ _ => Nat.zero_le _) hw_mem
      have hw_val : outdeg wstar - 1 = 1 := by omega
      have hrest : ∑ u ∈ (Nodes.erase D.output).erase wstar, (outdeg u - 1) = 0 := by
        have hadd := Finset.add_sum_erase (Nodes.erase D.output) (fun z => outdeg z - 1) hw_mem
        omega
      refine ⟨wstar, hw_mem, by omega, fun u hu hne => ?_⟩
      have hu_er : u ∈ (Nodes.erase D.output).erase wstar := Finset.mem_erase.mpr ⟨hne, hu⟩
      have h0 : outdeg u - 1 = 0 :=
        (Finset.sum_eq_zero_iff.mp hrest) u hu_er
      omega
    obtain ⟨wstar, hw_mem, hw_deg2, hw_unique⟩ := hfork_ex
    have hw_ne_out : wstar ≠ D.output := (Finset.mem_erase.mp hw_mem).1
    have hw_in_Nodes : wstar ∈ Nodes := (Finset.mem_erase.mp hw_mem).2
    have hw_lt_out : wstar < D.output := by
      rcases Finset.mem_union.mp hw_in_Nodes with h1 | h2
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1; have := i.isLt; omega
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h2
        have := Finset.mem_range.mp hk; omega
    have hout1_ne : ∀ u, u ≠ wstar → outdeg u ≤ 1 := by
      intro u hne
      by_cases hu : u ∈ Nodes.erase D.output
      · exact hw_unique u hu hne
      · by_cases heq : u = D.output
        · rw [heq, hout_deg0]; omega
        · have hu_not : u ∉ Nodes := fun hm => hu (Finset.mem_erase.mpr ⟨heq, hm⟩)
          have h0 : outdeg u = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro k hk
            simp only [readers, Finset.mem_filter, Finset.mem_range] at hk
            have hk' := hk.1
            rw [dif_pos hk'] at hk
            exact hu_not (heff_mem_Nodes k hk' u hk.2)
          omega

    have hb_reach : Reach b.val wstar := by
      by_contra hnr
      have hout1 : ∀ u, Reach b.val u → u < D.output → outdeg u ≤ 1 := fun u hu _ =>
        hout1_ne u (fun heq => hnr (heq ▸ hu))
      rcases htree_unate b D.output hout1 with hinc | hdec
      · obtain ⟨y, hy0, hy1⟩ := hb_nonunate.2
        have hle : f (Function.update y b false) ≤ f (Function.update y b true) := by
          rw [← hDeval, ← hDeval]; exact hinc y
        rw [hy0, hy1] at hle; exact absurd hle (by decide)
      · obtain ⟨x, hx0, hx1⟩ := hb_nonunate.1
        have hle : f (Function.update x b true) ≤ f (Function.update x b false) := by
          rw [← hDeval, ← hDeval]; exact hdec x
        rw [hx0, hx1] at hle; exact absurd hle (by decide)
    have hc_reach : Reach c.val wstar := by
      by_contra hnr
      have hout1 : ∀ u, Reach c.val u → u < D.output → outdeg u ≤ 1 := fun u hu _ =>
        hout1_ne u (fun heq => hnr (heq ▸ hu))
      rcases htree_unate c D.output hout1 with hinc | hdec
      · obtain ⟨y, hy0, hy1⟩ := hc_nonunate.2
        have hle : f (Function.update y c false) ≤ f (Function.update y c true) := by
          rw [← hDeval, ← hDeval]; exact hinc y
        rw [hy0, hy1] at hle; exact absurd hle (by decide)
      · obtain ⟨x, hx0, hx1⟩ := hc_nonunate.1
        have hle : f (Function.update x c true) ≤ f (Function.update x c false) := by
          rw [← hDeval, ← hDeval]; exact hdec x
        rw [hx0, hx1] at hle; exact absurd hle (by decide)

    have hcut_step : ∀ k (hk : k < D.size) u, u ∈ eff D.gates[k] → ¬ Reach (n + k) wstar →
        ¬ Reach u wstar ∨ u = wstar := by
      intro k hk u hu hnk
      by_cases heq : u = wstar
      · exact Or.inr heq
      · left
        intro hru
        rcases Relation.ReflTransGen.cases_head hru with rfl | ⟨y, hstep_uy, hyw⟩
        · exact heq rfl
        · have hstep_uk : Step u (n + k) := ⟨k, hk, rfl, hu⟩
          have hyeq : y = n + k := hstep_det u y (n + k) (hout1_ne u heq) hstep_uy hstep_uk
          subst hyeq
          exact hnk hyw

    have hcut : ∀ x₁ x₂ : Fin n → Bool,
        (∀ i : Fin n, ¬ Reach i.val wstar → x₁ i = x₂ i) →
        wv D x₁ wstar = wv D x₂ wstar → f x₁ = f x₂ := by
      intro x₁ x₂ hag hw_eq
      have haux : ∀ z, (¬ Reach z wstar ∨ z = wstar) → wv D x₁ z = wv D x₂ z := by
        intro z
        induction z using Nat.strong_induction_on with
        | _ z ih =>
          intro hz
          rcases hz with hnr | rfl
          · by_cases hzn : z < n
            · rw [wv_input D x₁ ⟨z, hzn⟩, wv_input D x₂ ⟨z, hzn⟩]
              exact hag ⟨z, hzn⟩ hnr
            · by_cases hge : n + D.size ≤ z
              · rw [wv_ge D x₁ z hge, wv_ge D x₂ z hge]
              · obtain ⟨k, rfl⟩ : ∃ k, z = n + k := ⟨z - n, by omega⟩
                have hk : k < D.size := by omega
                rw [wv_gate D x₁ k hk, wv_gate D x₂ k hk,
                  eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1,
                  eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult := heff_lt k hk u hu
                rw [if_pos hult, if_pos hult]
                exact ih u hult (hcut_step k hk u hu hnr)
          · exact hw_eq
      rw [← hDeval x₁, ← hDeval x₂]
      exact haux D.output (Or.inl (fun hr => by have := hReach_le D.output wstar hr; omega))

    have hν_nr : ¬ Reach (n + ν) wstar := by
      intro hν_r

      have hmono_above : ∀ x₁ x₂ : Fin n → Bool,
          (∀ i : Fin n, ¬ Reach i.val wstar → x₁ i = x₂ i) →
          wv D x₁ wstar ≤ wv D x₂ wstar → f x₁ ≤ f x₂ := by
        intro x₁ x₂ hag hw_le
        have haux : ∀ z, (¬ Reach z wstar ∨ z = wstar) → wv D x₁ z ≤ wv D x₂ z := by
          intro z
          induction z using Nat.strong_induction_on with
          | _ z ih =>
            intro hz
            rcases hz with hnr | rfl
            · by_cases hzn : z < n
              · rw [wv_input D x₁ ⟨z, hzn⟩, wv_input D x₂ ⟨z, hzn⟩, hag ⟨z, hzn⟩ hnr]
              · by_cases hge : n + D.size ≤ z
                · rw [wv_ge D x₁ z hge, wv_ge D x₂ z hge]
                · obtain ⟨k, rfl⟩ : ∃ k, z = n + k := ⟨z - n, by omega⟩
                  have hk : k < D.size := by omega
                  have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
                  rcases hop with hand | hor | hnot
                  · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inl hand)
                    rw [wv_gate D x₁ k hk, wv_gate D x₂ k hk,
                      eff_eval_eq _ (by simp [hand]), eff_eval_eq _ (by simp [hand]), heff, hand]
                    simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_and2]
                    exact bool_and_le (ih p hp (hcut_step k hk p (by rw [heff]; simp) hnr))
                      (ih q hq (hcut_step k hk q (by rw [heff]; simp) hnr))
                  · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inr hor)
                    rw [wv_gate D x₁ k hk, wv_gate D x₂ k hk,
                      eff_eval_eq _ (by simp [hor]), eff_eval_eq _ (by simp [hor]), heff, hor]
                    simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_or2]
                    exact bool_or_le (ih p hp (hcut_step k hk p (by rw [heff]; simp) hnr))
                      (ih q hq (hcut_step k hk q (by rw [heff]; simp) hnr))
                  · have hkν : k = ν := hnot_unique k hk hnot
                    subst hkν
                    exact (hnr hν_r).elim
            · exact hw_le
        rw [← hDeval x₁, ← hDeval x₂]
        exact haux D.output (Or.inl (fun hr => by have := hReach_le D.output wstar hr; omega))

      rcases htree_unate b wstar (fun u _ hlt => hout1_ne u (by omega)) with hinc | hdec
      · obtain ⟨y, hy0, hy1⟩ := hb_nonunate.2
        have hle := hmono_above (Function.update y b false) (Function.update y b true)
          (fun i hi => by
            have hne : i ≠ b := fun h => hi (h ▸ hb_reach)
            simp [hne]) (hinc y)
        rw [hy0, hy1] at hle; exact absurd hle (by decide)
      · obtain ⟨x, hx0, hx1⟩ := hb_nonunate.1
        have hle := hmono_above (Function.update x b true) (Function.update x b false)
          (fun i hi => by
            have hne : i ≠ b := fun h => hi (h ▸ hb_reach)
            simp [hne]) (hdec x)
        rw [hx0, hx1] at hle; exact absurd hle (by decide)

    have hw_mono : ∀ x₁ x₂ : Fin n → Bool, (∀ i, x₁ i ≤ x₂ i) → wv D x₁ wstar ≤ wv D x₂ wstar := by
      intro x₁ x₂ hle
      have haux : ∀ z, Reach z wstar → wv D x₁ z ≤ wv D x₂ z := by
        intro z
        induction z using Nat.strong_induction_on with
        | _ z ih =>
          intro hrz
          by_cases hzn : z < n
          · rw [wv_input D x₁ ⟨z, hzn⟩, wv_input D x₂ ⟨z, hzn⟩]; exact hle ⟨z, hzn⟩
          · by_cases hge : n + D.size ≤ z
            · rw [wv_ge D x₁ z hge, wv_ge D x₂ z hge]
            · obtain ⟨k, rfl⟩ : ∃ k, z = n + k := ⟨z - n, by omega⟩
              have hk : k < D.size := by omega
              have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
              rcases hop with hand | hor | hnot
              · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inl hand)
                rw [wv_gate D x₁ k hk, wv_gate D x₂ k hk,
                  eff_eval_eq _ (by simp [hand]), eff_eval_eq _ (by simp [hand]), heff, hand]
                simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_and2]
                exact bool_and_le (ih p hp (Relation.ReflTransGen.head ⟨k, hk, rfl, by rw [heff]; simp⟩ hrz))
                  (ih q hq (Relation.ReflTransGen.head ⟨k, hk, rfl, by rw [heff]; simp⟩ hrz))
              · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inr hor)
                rw [wv_gate D x₁ k hk, wv_gate D x₂ k hk,
                  eff_eval_eq _ (by simp [hor]), eff_eval_eq _ (by simp [hor]), heff, hor]
                simp only [List.map_cons, List.map_nil, if_pos hp, if_pos hq, eval_or2]
                exact bool_or_le (ih p hp (Relation.ReflTransGen.head ⟨k, hk, rfl, by rw [heff]; simp⟩ hrz))
                  (ih q hq (Relation.ReflTransGen.head ⟨k, hk, rfl, by rw [heff]; simp⟩ hrz))
              · have hkν : k = ν := hnot_unique k hk hnot
                subst hkν; exact (hν_nr hrz).elim
      exact haux wstar Relation.ReflTransGen.refl

    let mk (u v w : Bool) : Fin n → Bool :=
      Function.update (Function.update (Function.update x0 a u) b v) c w
    let W (u v w : Bool) : Bool := wv D (mk u v w) wstar
    have hW_mono : ∀ u₁ u₂ v₁ v₂ w₁ w₂, u₁ ≤ u₂ → v₁ ≤ v₂ → w₁ ≤ w₂ → W u₁ v₁ w₁ ≤ W u₂ v₂ w₂ := by
      intro u₁ u₂ v₁ v₂ w₁ w₂ hu hv hw
      apply hw_mono
      intro i
      by_cases hic : i = c
      · subst hic; simp [mk, hw]
      · by_cases hib : i = b
        · subst hib; simp [mk, hbc, hv]
        · by_cases hia : i = a
          · subst hia; simp [mk, hac, hab, hu]
          · simp [mk, hic, hib, hia]
    have hf_ne_t : t ≠ !t := by cases t <;> decide

    have hW_010_ne_011 : W false true false ≠ W false true true := by
      intro heq
      have hfeq := hcut (mk false true false) (mk false true true) (fun i hi => by
        have hic : i ≠ c := fun h => hi (h ▸ hc_reach)
        simp [mk, hic]) heq
      change f (mk false true false) = f (mk false true true) at hfeq
      rw [show f (mk false true false) = !t from h010, show f (mk false true true) = t from h011] at hfeq
      exact hf_ne_t hfeq.symm
    have hW010 : W false true false = false := by
      have hle := hW_mono false false true true false true le_rfl le_rfl (by decide)
      cases h1 : W false true false <;> cases h2 : W false true true
      · rfl
      · rfl
      · rw [h1, h2] at hle; exact absurd hle (by decide)
      · rw [h1, h2] at hW_010_ne_011; exact absurd rfl hW_010_ne_011
    have hW011 : W false true true = true := by
      have hle := hW_mono false false true true false true le_rfl le_rfl (by decide)
      cases h1 : W false true false <;> cases h2 : W false true true
      · rw [h1, h2] at hW_010_ne_011; exact absurd rfl hW_010_ne_011
      · rfl
      · rw [h1, h2] at hle; exact absurd hle (by decide)
      · rfl
    have hW000 : W false false false = false := by
      have hle := hW_mono false false false true false false le_rfl (by decide) le_rfl
      rw [hW010] at hle
      cases h1 : W false false false
      · rfl
      · rw [h1] at hle; exact absurd hle (by decide)

    by_cases ha_reach : Reach a.val wstar
    · have hW100_ne_010 : W true false false ≠ W false true false := by
        intro heq
        have hfeq := hcut (mk true false false) (mk false true false) (fun i hi => by
          have hia : i ≠ a := fun h => hi (h ▸ ha_reach)
          have hib : i ≠ b := fun h => hi (h ▸ hb_reach)
          have hic : i ≠ c := fun h => hi (h ▸ hc_reach)
          simp [mk, hia, hib, hic]) heq
        change f (mk true false false) = f (mk false true false) at hfeq
        rw [show f (mk true false false) = t from h100, show f (mk false true false) = !t from h010] at hfeq
        exact hf_ne_t hfeq
      have hW100 : W true false false = true := by
        rw [hW010] at hW100_ne_010
        cases h1 : W true false false
        · exact absurd h1 hW100_ne_010
        · rfl
      have hW110 : W true true false = true := by
        have hle := hW_mono true true false true false false le_rfl (by decide) le_rfl
        rw [hW100] at hle
        cases h1 : W true true false
        · rw [h1] at hle; exact absurd hle (by decide)
        · rfl
      have hfeq := hcut (mk true true false) (mk false true true) (fun i hi => by
        have hia : i ≠ a := fun h => hi (h ▸ ha_reach)
        have hib : i ≠ b := fun h => hi (h ▸ hb_reach)
        have hic : i ≠ c := fun h => hi (h ▸ hc_reach)
        simp [mk, hia, hib, hic]) (by change W true true false = W false true true; rw [hW110, hW011])
      change f (mk true true false) = f (mk false true true) at hfeq
      rw [show f (mk true true false) = !t from h110, show f (mk false true true) = t from h011] at hfeq
      exact hf_ne_t hfeq.symm
    · have hW100 : W true false false = W false false false := by
        have h1 : mk true false false = Function.update (mk false false false) a true := by
          funext i; by_cases hic : i = c <;> by_cases hib : i = b <;> by_cases hia : i = a <;>
            simp [mk, hic, hib, hia, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
        have h2 : mk false false false = Function.update (mk false false false) a false := by
          funext i; by_cases hic : i = c <;> by_cases hib : i = b <;> by_cases hia : i = a <;>
            simp [mk, hic, hib, hia, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
        change wv D (mk true false false) wstar = wv D (mk false false false) wstar
        conv_lhs => rw [h1]
        conv_rhs => rw [h2]
        exact (hnot_reach_indep a wstar ha_reach (mk false false false)).symm
      have hW110 : W true true false = W false true false := by
        have h1 : mk true true false = Function.update (mk false true false) a true := by
          funext i; by_cases hic : i = c <;> by_cases hib : i = b <;> by_cases hia : i = a <;>
            simp [mk, hic, hib, hia, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
        have h2 : mk false true false = Function.update (mk false true false) a false := by
          funext i; by_cases hic : i = c <;> by_cases hib : i = b <;> by_cases hia : i = a <;>
            simp [mk, hic, hib, hia, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
        change wv D (mk true true false) wstar = wv D (mk false true false) wstar
        conv_lhs => rw [h1]
        conv_rhs => rw [h2]
        exact (hnot_reach_indep a wstar ha_reach (mk false true false)).symm
      have hfeq := hcut (mk true false false) (mk true true false) (fun i hi => by
        have hib : i ≠ b := fun h => hi (h ▸ hb_reach)
        by_cases hic : i = c <;> simp [mk, hic, hib]) (by
          change W true false false = W true true false; rw [hW100, hW000, hW110, hW010])
      change f (mk true false false) = f (mk true true false) at hfeq
      rw [show f (mk true false false) = t from h100, show f (mk true true false) = !t from h110] at hfeq
      exact hf_ne_t hfeq

end PEqualNP.Outside.L_lib_541

theorem PEqualNP.Outside.L_lib_541 : (∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C →
  let W := Fin n → Bool
  let f := fun (x : W) => C.eval (List.ofFn x)
  let essential := (Finset.univ : Finset (Fin n)).filter (fun j =>
    ∃ x : W, f (Function.update x j false) ≠ f (Function.update x j true))
  ∀ (a b c : Fin n) (x : W) (t : Bool), a ≠ b → a ≠ c → b ≠ c →
    let atBits := fun (u v w : Bool) =>
      f (Function.update (Function.update (Function.update x a u) b v) c w)
    atBits true false false = t → atBits false true true = t →
    atBits false true false = !t → atBits false false true = !t →
    atBits true true false = !t →
    (∃ y : W, f (Function.update y c false) = t ∧ f (Function.update y c true) = !t) →
    essential.card + 2 ≤ C.size) := by
  dsimp only
  intro n C hCfan a b c x t hab hac hbc h100 h011 h010 h001 h110 hy
  exact PEqualNP.Outside.L_lib_541.main_proof n C hCfan a b c x t hab hac hbc h100 h011 h010 h001 h110 hy
