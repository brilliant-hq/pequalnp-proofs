import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25487_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl gateStep w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (gateStep w g) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp [gateStep]
    omega

lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge_length (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wiresFrom_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
    i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [wiresFrom_cons, ih (gateStep w g) i (by simp [gateStep]; omega)]
    exact getD_append_left w _ i hi

lemma wiresFrom_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs x).getD (x.length + k) false =
      (gs.getD k ⟨GateOp.or, []⟩).op.eval
        ((gs.getD k ⟨GateOp.or, []⟩).inputs.map fun i =>
          if i < x.length + k then (wiresFrom gs x).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    have h2 : gs.drop k = gs[k] :: gs.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    exact h1
  have htake_len : (gs.take k).length = k := List.length_take_of_le (by omega)
  have hget : gs.getD k ⟨GateOp.or, []⟩ = gs[k] := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [hget]
  have hw_len : (wiresFrom (gs.take k) x).length = x.length + k := by
    rw [wiresFrom_length, htake_len]
  have h1 : wiresFrom gs x = wiresFrom (gs.drop (k + 1)) (gateStep (wiresFrom (gs.take k) x) gs[k]) := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
  have hstep_len : (gateStep (wiresFrom (gs.take k) x) gs[k]).length = x.length + k + 1 := by
    simp [gateStep, hw_len]
  have hval : (wiresFrom gs x).getD (x.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (wiresFrom (gs.take k) x).getD i false) := by
    rw [h1, wiresFrom_prefix _ _ _ (by omega)]
    unfold gateStep
    rw [← hw_len, getD_snoc_eq]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + k
  · rw [ite_eq_left hi]
    have hpref1 : (wiresFrom gs x).getD i false = (gateStep (wiresFrom (gs.take k) x) gs[k]).getD i false := by
      rw [h1, wiresFrom_prefix _ _ _ (by omega)]
    rw [hpref1]
    exact (getD_append_left (wiresFrom (gs.take k) x) _ i (by omega)).symm
  · rw [ite_eq_right hi]
    exact getD_ge_length (wiresFrom (gs.take k) x) i (by omega)

lemma wires_eq_wiresFrom (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wires_gate_of_readsBack (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (x : List Bool) (hx : x.length = N) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (N + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_eq_wiresFrom, ← hx, wiresFrom_gate C.gates x k hk]
  change (gateAt C k).op.eval _ = (gateAt C k).op.eval _
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < N + k := hrb k hk i hi
  rw [ite_eq_left (by omega)]

lemma gate_mono (g : Gate) (hgm : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hgm with hop | hop <;> rw [hop]
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    rintro h _ ⟨i, hi, rfl⟩
    exact hle i (h _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨_, ⟨i, hi, rfl⟩, ht⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hle i ht⟩

lemma wiresFrom_mono (gs : List Gate) (hgm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (wiresFrom gs w1).getD i false = true → (wiresFrom gs w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ hle i hi; exact hle i hi
  | cons g gs ih =>
    intro w1 w2 hlen hle
    apply ih (fun g' hg' => hgm g' (List.mem_cons_of_mem g hg'))
    · simp [gateStep, hlen]
    · intro i hi
      by_cases hlt : i < w1.length
      · rw [gateStep, getD_append_left w1 _ i hlt] at hi
        rw [gateStep, getD_append_left w2 _ i (by omega)]
        exact hle i hi
      · by_cases heq : i = w1.length
        · subst heq
          rw [gateStep, getD_snoc_eq] at hi
          rw [gateStep, hlen, getD_snoc_eq]
          exact gate_mono g (hgm g (List.mem_cons_self ..)) w1 w2 hle hi
        · rw [gateStep, getD_ge_length _ i (by simp; omega)] at hi
          cases hi

lemma wires_mono (C : Circuit) (hM : Monotone2 C) (x y : List Bool)
    (hlen : x.length = y.length) (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
  apply wiresFrom_mono C.gates _ x y hlen hle
  intro g hg
  have h := (hM g hg).1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

lemma trace_diff_avoid (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (a z : ℕ) (hdiff_in : ∀ i, i ≠ a → x.getD i false = y.getD i false)
    (hz : (C.wires x).getD z false = (C.wires y).getD z false) :
    ∀ t : ℕ, (C.wires x).getD t false ≠ (C.wires y).getD t false →
      a ≠ z ∧ t ≠ z ∧ Relation.ReflTransGen
        (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧
          ∃ idx : Fin C.gates.length, next = N + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) a t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro hne
    have htz : t ≠ z := fun h => hne (h ▸ hz)
    by_cases hltN : t < N
    · have hxt : (C.wires x).getD t false = x.getD t false := by
        rw [wires_eq_wiresFrom, wiresFrom_prefix _ _ _ (by omega)]
      have hyt : (C.wires y).getD t false = y.getD t false := by
        rw [wires_eq_wiresFrom, wiresFrom_prefix _ _ _ (by omega)]
      rw [hxt, hyt] at hne
      have hta : t = a := by
        by_contra h
        exact hne (hdiff_in t h)
      subst hta
      exact ⟨htz, htz, Relation.ReflTransGen.refl⟩
    · by_cases hltG : t < N + C.gates.length
      · let k := t - N
        have hk : k < C.gates.length := by omega
        have htk : t = N + k := by omega
        rw [htk, wires_gate_of_readsBack N C hrb x hx k hk,
            wires_gate_of_readsBack N C hrb y hy k hk] at hne
        have hex : ∃ s ∈ (gateAt C k).inputs, (C.wires x).getD s false ≠ (C.wires y).getD s false := by
          by_contra hall
          apply hne
          congr 1
          apply List.map_congr_left
          intro s hs
          by_contra hsne
          exact hall ⟨s, hs, hsne⟩
        obtain ⟨s, hs_mem, hs_ne⟩ := hex
        have hs_lt : s < t := by
          have := hrb k hk s hs_mem
          omega
        obtain ⟨haz, hsz, hpath⟩ := ih s hs_lt hs_ne
        refine ⟨haz, htz, Relation.ReflTransGen.tail hpath ?_⟩
        exact ⟨hsz, htz, ⟨⟨k, hk⟩, htk, hs_mem⟩⟩
      · have hxt : (C.wires x).getD t false = false := by
          rw [wires_eq_wiresFrom, getD_ge_length _ _ (by rw [wiresFrom_length, hx]; omega)]
        have hyt : (C.wires y).getD t false = false := by
          rw [wires_eq_wiresFrom, getD_ge_length _ _ (by rw [wiresFrom_length, hy]; omega)]
        rw [hxt, hyt] at hne
        exact absurd rfl hne

lemma rtg_mono {r1 r2 : ℕ → ℕ → Prop} (h : ∀ x y, r1 x y → r2 x y) {a b : ℕ}
    (hp : Relation.ReflTransGen r1 a b) : Relation.ReflTransGen r2 a b := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (h _ _ hstep)

lemma trace_diff (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (a : ℕ) (hdiff_in : ∀ i, i ≠ a → x.getD i false = y.getD i false)
    (t : ℕ) (hne : (C.wires x).getD t false ≠ (C.wires y).getD t false) :
    Relation.ReflTransGen
      (fun prev next : ℕ => ∃ idx : Fin C.gates.length,
        next = N + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) a t := by
  let z := N + C.gates.length
  have hz : (C.wires x).getD z false = (C.wires y).getD z false := by
    rw [wires_eq_wiresFrom, wires_eq_wiresFrom,
        getD_ge_length _ _ (by rw [wiresFrom_length, hx]),
        getD_ge_length _ _ (by rw [wiresFrom_length, hy])]
  obtain ⟨_, _, hpath⟩ := trace_diff_avoid N C hrb x y hx hy a z hdiff_in hz t hne
  exact rtg_mono (fun _ _ hs => hs.2.2) hpath

lemma col_le_oneEach {n m : ℕ} (a : Fin n) (c : Fin m) :
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    col.length = n + m ∧ (oneEach a c).length = n + m ∧
    (∀ i, col.getD i false = true → (oneEach a c).getD i false = true) ∧
    (∀ i, i ≠ a.val → col.getD i false = (oneEach a c).getD i false) := by
  dsimp only
  have hcol_len : (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).length = n + m := by
    simp
  have hoe_len : (oneEach a c).length = n + m := by
    simp [oneEach]
  refine ⟨hcol_len, hoe_len, ?_, ?_⟩
  · intro i hi
    by_cases hlt : i < n
    · rw [getD_append_left _ _ i (by simp; omega)] at hi
      simp [List.getD_eq_getElem?_getD, hlt] at hi
    · by_cases hlt2 : i < n + m
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)] at hi
        rw [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simpa using hi
      · rw [getD_ge_length _ i (by omega)] at hi
        cases hi
  · intro i hne
    by_cases hlt : i < n
    · rw [getD_append_left _ _ i (by simp; omega)]
      rw [oneEach, getD_append_left _ _ i (by simp; omega)]
      have ha_ne : (⟨i, hlt⟩ : Fin n) ≠ a := fun h => hne (congrArg Fin.val h)
      simp [List.getD_eq_getElem?_getD, hlt, ha_ne]
    · by_cases hlt2 : i < n + m
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        rw [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp
      · rw [getD_ge_length _ i (by omega), getD_ge_length _ i (by omega)]

end PEqualNP.Outside.L_meta_25487_aux

open PEqualNP.Outside.L_meta_25487_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25487 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let g := n + m + j.val
  let edge := fun source target : ℕ => ∃ idx : Fin C.gates.length,
    target = n + m + idx.val ∧ source ∈ (gate idx.val).inputs
  let cuts := fun (z start : ℕ) =>
    ¬ (start ≠ z ∧ C.output ≠ z ∧ Relation.ReflTransGen
      (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ edge prev next) start C.output)
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C → u ≠ v →
  (gate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  q ∈ (gate j.val).inputs →
  cuts g u.val → cuts q v.val → ¬ Relation.ReflTransGen edge u.val q →
  ∀ c : Fin m, (∃ w : Fin n, G w c = false) →
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    let value := (C.wires col).getD q false
    (G u c = true → value = true) ∧ (G v c = true → value = false)) := by
  intro n m G C u v j q gate g edge cuts hM hrb hRep _ hand hq hcut_u hcut_v hno_reach c ⟨w, hwc⟩ col value
  have hcol_out : (C.wires col).getD C.output false = false := by
    obtain ⟨hcl, hwl, hle, _⟩ := col_le_oneEach w c
    cases hout : (C.wires col).getD C.output false
    · rfl
    · have h1 := wires_mono C hM col (oneEach w c) (hcl.trans hwl.symm) hle C.output hout
      have h2 : (C.wires (oneEach w c)).getD C.output false = G w c := hRep w c
      rw [h2, hwc] at h1
      cases h1
  constructor
  · intro huc
    obtain ⟨hcl, hul, hle_u, hdiff_u⟩ := col_le_oneEach u c
    have hout_ne : (C.wires col).getD C.output false ≠ (C.wires (oneEach u c)).getD C.output false := by
      have h2 : (C.wires (oneEach u c)).getD C.output false = G u c := hRep u c
      rw [hcol_out, h2, huc]
      decide
    have hg_ne : (C.wires col).getD g false ≠ (C.wires (oneEach u c)).getD g false := by
      intro hgeq
      exact hcut_u (trace_diff_avoid (n + m) C hrb col (oneEach u c) hcl hul u.val g hdiff_u hgeq C.output hout_ne)
    have hg_u : (C.wires (oneEach u c)).getD g false = true := by
      cases hgu : (C.wires (oneEach u c)).getD g false
      · exfalso
        cases hgc : (C.wires col).getD g false
        · exact hg_ne (hgc.trans hgu.symm)
        · have := wires_mono C hM col (oneEach u c) (hcl.trans hul.symm) hle_u g hgc
          rw [hgu] at this
          cases this
      · rfl
    have hq_u : (C.wires (oneEach u c)).getD q false = true := by
      have hgeval := wires_gate_of_readsBack (n + m) C hrb (oneEach u c) hul j.val j.isLt
      change (C.wires (oneEach u c)).getD g false =
        (gate j.val).op.eval ((gate j.val).inputs.map fun i => (C.wires (oneEach u c)).getD i false) at hgeval
      rw [hg_u, hand] at hgeval
      have hall := (List.all_eq_true).mp hgeval.symm
      exact hall _ (List.mem_map_of_mem hq)
    have hq_eq : (C.wires col).getD q false = (C.wires (oneEach u c)).getD q false := by
      by_contra hqne
      exact hno_reach (trace_diff (n + m) C hrb col (oneEach u c) hcl hul u.val hdiff_u q hqne)
    exact hq_eq.trans hq_u
  · intro hvc
    obtain ⟨hcl, hvl, hle_v, hdiff_v⟩ := col_le_oneEach v c
    have hout_ne : (C.wires col).getD C.output false ≠ (C.wires (oneEach v c)).getD C.output false := by
      have h2 : (C.wires (oneEach v c)).getD C.output false = G v c := hRep v c
      rw [hcol_out, h2, hvc]
      decide
    have hq_ne : (C.wires col).getD q false ≠ (C.wires (oneEach v c)).getD q false := by
      intro hqeq
      exact hcut_v (trace_diff_avoid (n + m) C hrb col (oneEach v c) hcl hvl v.val q hdiff_v hqeq C.output hout_ne)
    cases hqc : (C.wires col).getD q false
    · exact hqc
    · exfalso
      have hqv := wires_mono C hM col (oneEach v c) (hcl.trans hvl.symm) hle_v q hqc
      exact hq_ne (hqc.trans hqv.symm)
