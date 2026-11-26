import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19316

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def xorGraph (n : ℕ) (u v : Fin n) : Bool :=
  xor (decide (u.val = 0)) (decide (v.val = 0))

theorem oneEach_len {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < 2 * n) :
    (oneEach u v).getD i false = if i < n then decide (i = u.val) else decide (i - n = v.val) := by
  by_cases hn : i < n
  · simp only [hn, ↓reduceIte, oneEach, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp; omega : i < (List.ofFn (fun a : Fin n => decide (a = u))).length),
      List.getElem?_ofFn, ↓reduceDIte, Option.getD_some]
    simp [Fin.ext_iff]
  · have hlen : (List.ofFn (fun a : Fin n => decide (a = u))).length = n := by simp
    have hlt : i - n < n := by omega
    simp only [hn, ↓reduceIte, oneEach, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : (List.ofFn (fun a : Fin n => decide (a = u))).length ≤ i),
      hlen, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
    simp [Fin.ext_iff]

def xorCircuit (n : ℕ) : Circuit :=
  ⟨[⟨GateOp.or, [0, n]⟩,
    ⟨GateOp.and, [0, n]⟩,
    ⟨GateOp.not, [2 * n + 1]⟩,
    ⟨GateOp.and, [2 * n, 2 * n + 2]⟩],
   2 * n + 3⟩

theorem xorCircuit_fanInTwo (n : ℕ) : FanInTwo (xorCircuit n) := by
  intro g hg
  simp only [xorCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem xorCircuit_size (n : ℕ) : (xorCircuit n).size ≤ 4 := by
  simp [xorCircuit, Circuit.size]

theorem xorCircuit_represents (n : ℕ) (hn : 2 ≤ n) : Represents (xorGraph n) (xorCircuit n) := by
  intro u v
  unfold Circuit.eval Circuit.wires xorCircuit xorGraph
  dsimp only
  set x := oneEach u v
  have hxlen : x.length = 2 * n := oneEach_len u v
  have h0 : x.getD 0 false = decide (u.val = 0) := by
    rw [oneEach_getD u v 0 (by omega)]
    simp [show (0 : ℕ) < n by omega, eq_comm]
  have hn_val : x.getD n false = decide (v.val = 0) := by
    rw [oneEach_getD u v n (by omega)]
    simp [Nat.lt_irrefl, eq_comm]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval,
    List.any_cons, List.any_nil, Bool.or_false, List.all_cons, List.all_nil, Bool.and_true,
    List.headD_cons, id_eq]
  have hg1_0 : (x ++ [x.getD 0 false || x.getD n false]).getD 0 false = x.getD 0 false :=
    List.getD_append x _ _ 0 (by omega)
  have hg1_n : (x ++ [x.getD 0 false || x.getD n false]).getD n false = x.getD n false :=
    List.getD_append x _ _ n (by omega)
  rw [hg1_0, hg1_n]
  set b0 := x.getD 0 false || x.getD n false
  set b1 := x.getD 0 false && x.getD n false
  have hg2_2n1 : (x ++ [b0] ++ [b1]).getD (2 * n + 1) false = b1 := by
    rw [List.append_assoc, List.getD_append_right x _ _ _ (by omega : x.length ≤ 2 * n + 1)]
    rw [hxlen]; simp
  rw [hg2_2n1]
  have hg3_2n : (x ++ [b0] ++ [b1] ++ [!b1]).getD (2 * n) false = b0 := by
    rw [List.append_assoc, List.append_assoc, List.getD_append_right x _ _ _ (by omega : x.length ≤ 2 * n)]
    rw [hxlen]; simp
  have hg3_2n2 : (x ++ [b0] ++ [b1] ++ [!b1]).getD (2 * n + 2) false = !b1 := by
    rw [List.append_assoc, List.append_assoc, List.getD_append_right x _ _ _ (by omega : x.length ≤ 2 * n + 2)]
    rw [hxlen]; simp
  rw [hg3_2n, hg3_2n2]
  have hg4_2n3 : (x ++ [b0] ++ [b1] ++ [!b1] ++ [b0 && !b1]).getD (2 * n + 3) false = (b0 && !b1) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.getD_append_right x _ _ _ (by omega : x.length ≤ 2 * n + 3)]
    rw [hxlen]; simp
  rw [hg4_2n3]
  dsimp only [b0, b1]
  rw [h0, hn_val]
  cases decide (u.val = 0) <;> cases decide (v.val = 0) <;> rfl

def effIn (m j : ℕ) (g : Gate) : List ℕ :=
  g.inputs.filter (· < m + j)

theorem effIn_lt {m j : ℕ} {g : Gate} {u : ℕ} (hu : u ∈ effIn m j g) : u < m + j := by
  unfold effIn at hu
  simp only [List.mem_filter, decide_eq_true_eq] at hu
  exact hu.2

def cone (m : ℕ) (gs : List Gate) (w : ℕ) : Finset ℕ :=
  if h : m ≤ w ∧ w < m + gs.length then
    insert w ((effIn m (w - m) gs[w - m]).attach.foldr (fun u acc => cone m gs u.1 ∪ acc) ∅)
  else
    {w}
termination_by w
decreasing_by
  have hlt := effIn_lt u.2
  omega

theorem foldr_attach_union {α : Type} (l : List α) (f : α → Finset ℕ) :
    l.attach.foldr (fun u acc => f u.1 ∪ acc) ∅ = l.foldr (fun u acc => f u ∪ acc) ∅ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.attach_cons, List.foldr_cons, List.foldr_map]
    exact congrArg (f a ∪ ·) ih

theorem cone_unfold (m : ℕ) (gs : List Gate) (w : ℕ) :
    cone m gs w = if h : m ≤ w ∧ w < m + gs.length then
      insert w ((effIn m (w - m) gs[w - m]).foldr (fun u acc => cone m gs u ∪ acc) ∅)
    else {w} := by
  conv_lhs => rw [cone]
  split_ifs with h
  · rw [foldr_attach_union]
  · rfl

theorem self_mem_cone (m : ℕ) (gs : List Gate) (w : ℕ) : w ∈ cone m gs w := by
  rw [cone_unfold]; split_ifs <;> simp

theorem cone_subset_of_mem_eff (m : ℕ) (gs : List Gate) {w u : ℕ}
    (hw : m ≤ w ∧ w < m + gs.length) (hu : u ∈ effIn m (w - m) gs[w - m]) :
    cone m gs u ⊆ cone m gs w := by
  conv_rhs => rw [cone_unfold]
  simp only [hw, ↓reduceDIte]
  intro z hz
  apply Finset.mem_insert_of_mem
  have hfold : ∀ (l : List ℕ), u ∈ l → cone m gs u ⊆ l.foldr (fun a acc => cone m gs a ∪ acc) ∅ := by
    intro l; induction l with
    | nil => intro h; cases h
    | cons a t ih =>
      intro h; simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | ht
      · exact Finset.subset_union_left
      · exact (ih ht).trans Finset.subset_union_right
  exact hfold _ hu hz

theorem wires_len (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  unfold Circuit.wires; dsimp only
  have h : ∀ (l : List Gate) (acc : List Bool),
      (l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
        acc.length + l.length := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons g rest ih => intro acc; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega
  exact h gs x

theorem wires_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (Circuit.wires ⟨gs, 0⟩ x).getD i false = x.getD i false := by
  unfold Circuit.wires; dsimp only
  have h : ∀ (l : List Gate) (acc : List Bool), i < acc.length →
      (l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
        acc.getD i false := by
    intro l; induction l with
    | nil => intro acc _; rfl
    | cons g rest ih =>
      intro acc hacc; simp only [List.foldl_cons]
      rw [ih _ (by simp; omega)]
      exact List.getD_append acc _ _ i hacc
  exact h gs x hi

theorem wires_getD_gate (m : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = m)
    {j : ℕ} (hj : j < gs.length) :
    (Circuit.wires ⟨gs, 0⟩ x).getD (m + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k => if k < m + j then (Circuit.wires ⟨gs, 0⟩ x).getD k false else false) := by
  unfold Circuit.wires; dsimp only
  set f : List Bool → Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have hlen : ∀ (l : List Gate) (acc : List Bool), (l.foldl f acc).length = acc.length + l.length := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons g rest ih => intro acc; simp only [List.foldl_cons, ih, f, List.length_append, List.length_cons, List.length_nil]; omega
  have hpref : ∀ (l : List Gate) (acc : List Bool) (i : ℕ), i < acc.length →
      (l.foldl f acc).getD i false = acc.getD i false := by
    intro l; induction l with
    | nil => intro acc i _; rfl
    | cons g rest ih =>
      intro acc i hi; simp only [List.foldl_cons]
      rw [ih _ i (by simp [f]; omega)]
      exact List.getD_append acc _ _ i hi
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) gs]
    rw [List.take_succ_eq_append_getElem hj]
  let wj := (gs.take j).foldl f x
  have hwjlen : wj.length = m + j := by
    dsimp [wj]; rw [hlen, hx, List.length_take, Nat.min_eq_left hj.le]
  have hfull_eq : ∀ i < m + j, (gs.foldl f x).getD i false = wj.getD i false := by
    intro i hi
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    exact hpref (gs.drop j) wj i (by omega)
  have hval : (gs.foldl f x).getD (m + j) false = gs[j].op.eval (gs[j].inputs.map fun k => wj.getD k false) := by
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [hpref (gs.drop (j + 1)) ((gs.take j ++ [gs[j]]).foldl f x) (m + j)
      (by rw [hlen, hx]; simp; omega)]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (wj ++ [gs[j].op.eval (gs[j].inputs.map fun k => wj.getD k false)]).getD (m + j) false = _
    rw [← hwjlen]; simp
  rw [hval]
  congr 1; apply List.map_congr_left; intro k _
  by_cases hk : k < m + j
  · simp only [hk, ↓reduceIte]; exact (hfull_eq k hk).symm
  · simp only [hk, ↓reduceIte]; exact List.getD_eq_default wj false (by omega)

theorem mono_on_cone_eval (m : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : List Bool) (hx : x.length = m) (hy : y.length = m)
    (w : ℕ)
    (hle : ∀ i < m, i ∈ cone m gs w → x.getD i false = true → y.getD i false = true) :
    (Circuit.wires ⟨gs, 0⟩ x).getD w false = true → (Circuit.wires ⟨gs, 0⟩ y).getD w false = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hwm : w < m
    · rw [wires_getD_lt gs x (by omega), wires_getD_lt gs y (by omega)]
      exact hle w hwm (self_mem_cone m gs w)
    · by_cases hwlen : w < m + gs.length
      · have hw : m ≤ w ∧ w < m + gs.length := ⟨by omega, hwlen⟩
        have hj : w - m < gs.length := by omega
        have heq : m + (w - m) = w := by omega
        rw [← heq, wires_getD_gate m gs x hx hj, wires_getD_gate m gs y hy hj]
        set g := gs[w - m]
        have hg := hmono g (List.getElem_mem hj)
        rcases hg.1 with hop | hop
        · rw [hop]
          simp only [GateOp.eval, List.all_eq_true, id_eq]
          intro hall b hb
          rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
          have hax := hall _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
          by_cases halt : a < m + (w - m)
          · simp only [halt, ↓reduceIte] at hax ⊢
            have ha_eff : a ∈ effIn m (w - m) g := by simp [effIn, ha, halt]
            have hsub := cone_subset_of_mem_eff m gs hw ha_eff
            exact ih a (by omega) (fun i hi hic => hle i hi (hsub hic)) hax
          · simp only [halt, ↓reduceIte] at hax; cases hax
        · rw [hop]
          simp only [GateOp.eval, List.any_eq_true, id_eq]
          rintro ⟨b, hb, hbx⟩
          rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
          by_cases halt : a < m + (w - m)
          · simp only [halt, ↓reduceIte] at hbx
            have ha_eff : a ∈ effIn m (w - m) g := by simp [effIn, ha, halt]
            have hsub := cone_subset_of_mem_eff m gs hw ha_eff
            refine ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
            simp only [halt, ↓reduceIte]
            exact ih a (by omega) (fun i hi hic => hle i hi (hsub hic)) hbx
          · simp only [halt, ↓reduceIte] at hbx; cases hbx
      · rw [List.getD_eq_default _ false (by rw [wires_len, hx]; omega)]
        intro h; cases h

def activeGates (m : ℕ) (gs : List Gate) (w : ℕ) : Finset ℕ :=
  (cone m gs w).filter fun z => m ≤ z ∧ z < m + gs.length

def activeInputs (m : ℕ) (gs : List Gate) (w : ℕ) : Finset ℕ :=
  (cone m gs w).filter fun z => z < m

theorem activeGates_card_le (m : ℕ) (gs : List Gate) (w : ℕ) :
    (activeGates m gs w).card ≤ gs.length := by
  have hsub : (activeGates m gs w).image (· - m) ⊆ Finset.range gs.length := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have := (Finset.mem_filter.mp hz).2
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (· - m) (activeGates m gs w : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    dsimp only at hab
    omega
  rw [← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_card hsub).trans (by simp)

theorem active_erase_subset_readers (m : ℕ) (gs : List Gate) (w : ℕ) :
    (cone m gs w).erase w ⊆ (activeGates m gs w).biUnion fun g => (effIn m (g - m) (gs.getD (g - m) ⟨GateOp.and, []⟩)).toFinset := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro z hz
    have hzw : z ≠ w := (Finset.mem_erase.mp hz).1
    have hzc : z ∈ cone m gs w := (Finset.mem_erase.mp hz).2
    rw [cone_unfold] at hzc
    split_ifs at hzc with hw
    · rcases Finset.mem_insert.mp hzc with rfl | hmem
      · exact absurd rfl hzw
      · have hex : ∀ (l : List ℕ), z ∈ l.foldr (fun u acc => cone m gs u ∪ acc) ∅ → ∃ u ∈ l, z ∈ cone m gs u := by
          intro l; induction l with
          | nil => intro h; simp at h
          | cons a t iht =>
            intro h; simp only [List.foldr_cons, Finset.mem_union] at h
            rcases h with ha | ht
            · exact ⟨a, List.mem_cons_self, ha⟩
            · obtain ⟨u, hu, hzu⟩ := iht ht; exact ⟨u, List.mem_cons_of_mem _ hu, hzu⟩
        obtain ⟨u, hu, hzu⟩ := hex _ hmem
        by_cases hzu_eq : z = u
        · subst hzu_eq
          rw [Finset.mem_biUnion]
          refine ⟨w, Finset.mem_filter.mpr ⟨self_mem_cone m gs w, hw⟩, ?_⟩
          rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by omega)]
          exact hu
        · have hu_lt : u < w := by have := effIn_lt hu; omega
          have hsub := ih u hu_lt (Finset.mem_erase.mpr ⟨hzu_eq, hzu⟩)
          rw [Finset.mem_biUnion] at hsub ⊢
          obtain ⟨g, hg, hzg⟩ := hsub
          refine ⟨g, ?_, hzg⟩
          have hgc := Finset.mem_filter.mp hg
          exact Finset.mem_filter.mpr ⟨cone_subset_of_mem_eff m gs hw hu hgc.1, hgc.2⟩
    · simp at hzc; exact absurd hzc hzw

theorem mono_size_ge_inputs_sub_one (m : ℕ) (C : Circuit) (hmono : Monotone2 C) :
    (activeInputs m C.gates C.output).card - 1 ≤ C.size := by
  have hdisj : Disjoint (activeInputs m C.gates C.output) (activeGates m C.gates C.output) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hunion : activeInputs m C.gates C.output ∪ activeGates m C.gates C.output ⊆ cone m C.gates C.output := by
    intro z hz; rcases Finset.mem_union.mp hz with h | h <;> exact (Finset.mem_filter.mp h).1
  have h1 : (activeInputs m C.gates C.output).card + (activeGates m C.gates C.output).card ≤ (cone m C.gates C.output).card := by
    rw [← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_card hunion
  have herase : ((cone m C.gates C.output).erase C.output).card = (cone m C.gates C.output).card - 1 :=
    Finset.card_erase_of_mem (self_mem_cone m C.gates C.output)
  have h2 := Finset.card_le_card (active_erase_subset_readers m C.gates C.output)
  have h3 : ((activeGates m C.gates C.output).biUnion fun g => (effIn m (g - m) (C.gates.getD (g - m) ⟨GateOp.and, []⟩)).toFinset).card ≤
      ∑ g ∈ activeGates m C.gates C.output, ((effIn m (g - m) (C.gates.getD (g - m) ⟨GateOp.and, []⟩)).toFinset).card :=
    Finset.card_biUnion_le
  have h4 : ∑ g ∈ activeGates m C.gates C.output, ((effIn m (g - m) (C.gates.getD (g - m) ⟨GateOp.and, []⟩)).toFinset).card ≤
      ∑ g ∈ activeGates m C.gates C.output, (effIn m (g - m) (C.gates.getD (g - m) ⟨GateOp.and, []⟩)).length :=
    Finset.sum_le_sum fun g _ => List.toFinset_card_le _
  have h5 : ∑ g ∈ activeGates m C.gates C.output, (effIn m (g - m) (C.gates.getD (g - m) ⟨GateOp.and, []⟩)).length ≤
      2 * (activeGates m C.gates C.output).card := by
    calc ∑ g ∈ activeGates m C.gates C.output, (effIn m (g - m) (C.gates.getD (g - m) ⟨GateOp.and, []⟩)).length
        ≤ ∑ _g ∈ activeGates m C.gates C.output, 2 := by
          apply Finset.sum_le_sum; intro g hg
          have hga := (Finset.mem_filter.mp hg).2
          rw [List.getD_eq_getElem _ _ (by omega)]
          exact (List.length_filter_le _ _).trans (hmono C.gates[g - m] (List.getElem_mem (by omega))).2
      _ = 2 * (activeGates m C.gates C.output).card := by simp [Nat.mul_comm]
  have h6 : (activeGates m C.gates C.output).card ≤ C.size := activeGates_card_le m C.gates C.output
  omega

theorem xorGraph_mono_lower (n : ℕ) (hn : 2 ≤ n) (C : Circuit) (hmono : Monotone2 C)
    (hrep : Represents (xorGraph n) C) : 2 * n - 1 ≤ C.size := by
  have hmem_row : ∀ (u1 u2 v : Fin n), xorGraph n u1 v = true → xorGraph n u2 v = false →
      u1.val ∈ activeInputs (2 * n) C.gates C.output := by
    intro u1 u2 v h1 h2; by_contra hnot
    have hle : ∀ i < 2 * n, i ∈ cone (2 * n) C.gates C.output →
        (oneEach u1 v).getD i false = true → (oneEach u2 v).getD i false = true := by
      intro i hi2n hic hx
      rw [oneEach_getD u1 v i hi2n] at hx; rw [oneEach_getD u2 v i hi2n]
      by_cases hlt : i < n
      · simp only [hlt, ↓reduceIte] at hx ⊢
        simp only [decide_eq_true_eq] at hx
        exact absurd (hx ▸ Finset.mem_filter.mpr ⟨hic, hi2n⟩) hnot
      · simp only [hlt, ↓reduceIte] at hx ⊢; exact hx
    have hres := mono_on_cone_eval (2 * n) C.gates hmono _ _ (oneEach_len u1 v) (oneEach_len u2 v) C.output hle
      (by change C.eval (oneEach u1 v) = true; rw [hrep u1 v]; exact h1)
    change C.eval (oneEach u2 v) = true at hres
    rw [hrep u2 v, h2] at hres; cases hres
  have hmem_col : ∀ (u v1 v2 : Fin n), xorGraph n u v1 = true → xorGraph n u v2 = false →
      (n + v1.val) ∈ activeInputs (2 * n) C.gates C.output := by
    intro u v1 v2 h1 h2; by_contra hnot
    have hle : ∀ i < 2 * n, i ∈ cone (2 * n) C.gates C.output →
        (oneEach u v1).getD i false = true → (oneEach u v2).getD i false = true := by
      intro i hi2n hic hx
      rw [oneEach_getD u v1 i hi2n] at hx; rw [oneEach_getD u v2 i hi2n]
      by_cases hlt : i < n
      · simp only [hlt, ↓reduceIte] at hx ⊢; exact hx
      · simp only [hlt, ↓reduceIte] at hx ⊢
        simp only [decide_eq_true_eq] at hx
        have heq : n + v1.val = i := by omega
        exact absurd (heq ▸ Finset.mem_filter.mpr ⟨hic, hi2n⟩) hnot
    have hres := mono_on_cone_eval (2 * n) C.gates hmono _ _ (oneEach_len u v1) (oneEach_len u v2) C.output hle
      (by change C.eval (oneEach u v1) = true; rw [hrep u v1]; exact h1)
    change C.eval (oneEach u v2) = true at hres
    rw [hrep u v2, h2] at hres; cases hres
  let f0 : Fin n := ⟨0, by omega⟩
  let f1 : Fin n := ⟨1, by omega⟩
  have hall : Finset.range (2 * n) ⊆ activeInputs (2 * n) C.gates C.output := by
    intro i hi
    have hi2n : i < 2 * n := Finset.mem_range.mp hi
    by_cases hlt : i < n
    · by_cases hi0 : i = 0
      · subst hi0
        exact hmem_row f0 f1 f1 (by simp [xorGraph, f0, f1]) (by simp [xorGraph, f1])
      · let fi : Fin n := ⟨i, hlt⟩
        exact hmem_row fi f0 f0 (by simp [xorGraph, fi, f0, hi0]) (by simp [xorGraph, f0])
    · by_cases hin : i = n
      · subst hin
        have := hmem_col f1 f0 f1 (by simp [xorGraph, f0, f1]) (by simp [xorGraph, f1])
        simpa [f0] using this
      · let fj : Fin n := ⟨i - n, by omega⟩
        have hne0 : fj.val ≠ 0 := by dsimp [fj]; omega
        have := hmem_col f0 fj f0 (by simp [xorGraph, f0, hne0]) (by simp [xorGraph, f0])
        have heq : n + fj.val = i := by dsimp [fj]; omega
        rwa [heq] at this
  have hcard : 2 * n ≤ (activeInputs (2 * n) C.gates C.output).card := by
    have := Finset.card_le_card hall
    simpa using this
  have hsz := mono_size_ge_inputs_sub_one (2 * n) C hmono
  omega

theorem main_proof :
    ¬ ∃ a b : ℕ, ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (s : ℕ) (C : Circuit),
      FanInTwo C → C.size ≤ s → Represents A C → RepSizeAtMost A (a * s + b) := by
  rintro ⟨a, b, h⟩
  let n := 4 * a + b + 2
  have hn : 2 ≤ n := by omega
  obtain ⟨M, hmono, hMsz, hMrep⟩ :=
    h n (xorGraph n) 4 (xorCircuit n) (xorCircuit_fanInTwo n) (xorCircuit_size n) (xorCircuit_represents n hn)
  have hlb := xorGraph_mono_lower n hn M hmono hMrep
  omega

end PEqualNP.Outside.L_meta_19316

theorem PEqualNP.Outside.L_meta_19316 : (¬ ∃ a b : ℕ, ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (s : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → PEqualNP.Represents.RepSizeAtMost A (a * s + b)) :=
  PEqualNP.Outside.L_meta_19316.main_proof
