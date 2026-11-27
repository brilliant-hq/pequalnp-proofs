import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27623

open PEqualNP.CircuitLowerBounds

def perm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

lemma perm3_mono (x y : Fin 9 → Bool) (hle : ∀ i, x i = true → y i = true)
    (hx : perm3 x = true) : perm3 y = true := by
  unfold perm3 at hx ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (((((⟨⟨a, b⟩, c⟩ | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩)
  · left; left; left; left; left; exact ⟨⟨hle _ a, hle _ b⟩, hle _ c⟩
  · left; left; left; left; right; exact ⟨⟨hle _ a, hle _ b⟩, hle _ c⟩
  · left; left; left; right; exact ⟨⟨hle _ a, hle _ b⟩, hle _ c⟩
  · left; left; right; exact ⟨⟨hle _ a, hle _ b⟩, hle _ c⟩
  · left; right; exact ⟨⟨hle _ a, hle _ b⟩, hle _ c⟩
  · right; exact ⟨⟨hle _ a, hle _ b⟩, hle _ c⟩

def high (v i : Fin 9) : Bool :=
  (([273, 266, 140, 140, 273, 161, 98, 161, 273] : List Nat).getD v.val 0).testBit i.val

def low (v i : Fin 9) : Bool := if i = v then false else high v i

lemma separates (v : Fin 9) : perm3 (high v) ≠ perm3 (low v) := by
  fin_cases v <;> decide

lemma or_fixed (v : Fin 9) : (high v 0 || high v 4) = (low v 0 || low v 4) := by
  fin_cases v <;> decide

lemma and_fixed (v : Fin 9) : (high v 1 && high v 5) = (low v 1 && low v 5) := by
  fin_cases v <;> decide

def g0 : Gate := ⟨.or, [0, 4]⟩
def g1 : Gate := ⟨.and, [1, 5]⟩

def gateVal (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gateVal g w]) w

def warm (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [x 0 || x 4]) ++ [x 1 && x 5]

lemma ofFn_getD {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma warm_length (x : Fin 9 → Bool) : (warm x).length = 11 := by
  simp [warm]

lemma warm_getD_lt9 (x : Fin 9 → Bool) (i : Fin 9) :
    (warm x).getD i.val false = x i := by
  unfold warm
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append _ _ _ _ (by simp), ofFn_getD]

lemma warm_getD_9 (x : Fin 9 → Bool) : (warm x).getD 9 false = (x 0 || x 4) := by
  unfold warm
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
  simp

lemma warm_getD_10 (x : Fin 9 → Bool) : (warm x).getD 10 false = (x 1 && x 5) := by
  unfold warm
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
  simp

lemma prefix_run (gs : List Gate) (out : Nat) (x : Fin 9 → Bool) :
    (Circuit.mk (g0 :: g1 :: gs) out).wires (List.ofFn x) = run gs (warm x) := by
  have hx (i : Fin 9) : (List.ofFn x ++ [x 0 || x 4]).getD i.val false = x i := by
    rw [List.getD_append _ _ _ _ (by simp), ofFn_getD]
  have h0 : (List.ofFn x).getD 0 false = x 0 := ofFn_getD x 0
  have h4 : (List.ofFn x).getD 4 false = x 4 := ofFn_getD x 4
  have h1 : (List.ofFn x ++ [x 0 || x 4]).getD 1 false = x 1 := hx 1
  have h5 : (List.ofFn x ++ [x 0 || x 4]).getD 5 false = x 5 := hx 5
  change run gs ((List.ofFn x ++ [gateVal g0 (List.ofFn x)]) ++
    [gateVal g1 (List.ofFn x ++ [gateVal g0 (List.ofFn x)])]) = run gs (warm x)
  have hg0v : gateVal g0 (List.ofFn x) = (x 0 || x 4) := by
    change ((List.ofFn x).getD 0 false || ((List.ofFn x).getD 4 false || false)) = _
    rw [h0, h4, Bool.or_false]
  have hg1v : gateVal g1 (List.ofFn x ++ [x 0 || x 4]) = (x 1 && x 5) := by
    change ((List.ofFn x ++ [x 0 || x 4]).getD 1 false &&
      ((List.ofFn x ++ [x 0 || x 4]).getD 5 false && true)) = _
    rw [h1, h5, Bool.and_true]
  rw [hg0v, hg1v, warm]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g tl ih =>
    simp only [run, List.foldl_cons]
    have h := ih (w ++ [gateVal g w])
    unfold run at h
    rw [h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_prefix (gs : List Gate) (w : List Bool) {i : Nat} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tl ih =>
    simp only [run, List.foldl_cons]
    have h := ih (w ++ [gateVal g w]) (by simp; omega)
    unfold run at h
    rw [h, List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
      List.getElem_append_left hi]

lemma run_at (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]'hj).inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (run gs w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]'hj] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j]'hj :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp [List.append_assoc, h1]
  have hpre_len : (run (gs.take j) w).length = w.length + j := by
    rw [run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have happ : ∀ gs1 gs2 w, run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
    intro gs1 gs2 w; unfold run; rw [List.foldl_append]
  have hstep : (run (gs.take j ++ [gs[j]'hj]) w).getD (w.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (run (gs.take j) w).getD i false) := by
    rw [happ]
    set u := run (gs.take j) w
    unfold run
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hpre_len, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
    simp [gateVal]
  have hfull : (run gs w).getD (w.length + j) false =
      (run (gs.take j ++ [gs[j]'hj]) w).getD (w.length + j) false := by
    conv_lhs => rw [hsplit]
    rw [happ]
    exact run_prefix (gs.drop (j + 1)) _
      (by rw [run_length, List.length_append, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hj), List.length_singleton]; omega)
  rw [hfull, hstep]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hrb i hi
  conv_rhs => rw [hsplit]
  rw [happ, happ]
  rw [run_prefix (gs.drop (j + 1)) _ (by rw [run_length, hpre_len, List.length_singleton]; omega),
    run_prefix [gs[j]'hj] _ (by rw [hpre_len]; exact hlt)]

def Agree (v : Nat) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, i ≠ v → w.getD i false = w'.getD i false

lemma agree_append {v : Nat} {w w' : List Bool} (h : Agree v w w')
    {a a' : Bool} (ha : a = a') : Agree v (w ++ [a]) (w' ++ [a']) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro i hi
  by_cases hb : i < w.length
  · have hb' : i < w'.length := h.1 ▸ hb
    rw [List.getD_append _ _ _ _ hb, List.getD_append _ _ _ _ hb']
    exact h.2 i hi
  · have hb' : w'.length ≤ i := by rw [← h.1]; omega
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ hb', h.1, ha]

lemma agree_warm (v : Fin 9) : Agree v.val (warm (high v)) (warm (low v)) := by
  have h : Agree v.val (List.ofFn (high v)) (List.ofFn (low v)) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hb : i < 9
    · let j : Fin 9 := ⟨i, hb⟩
      have hj : j ≠ v := fun he => hi (congrArg Fin.val he)
      change (List.ofFn (high v)).getD j.val false = (List.ofFn (low v)).getD j.val false
      rw [ofFn_getD, ofFn_getD]
      simp [low, hj]
    · rw [List.getD_eq_default _ _ (by simpa using (show 9 ≤ i by omega)),
        List.getD_eq_default _ _ (by simpa using (show 9 ≤ i by omega))]
  exact agree_append (agree_append h (or_fixed v)) (and_fixed v)

lemma agree_run {v : Nat} {w w' : List Bool} (h : Agree v w w')
    (gs : List Gate) (hz : v ∉ gs.flatMap Gate.inputs) : Agree v (run gs w) (run gs w') := by
  induction gs generalizing w w' with
  | nil => exact h
  | cons g gs ih =>
    have hn : v ∉ g.inputs ∧ v ∉ gs.flatMap Gate.inputs := by simpa using hz
    have hv : gateVal g w = gateVal g w' := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      exact h.2 i (fun e => hn.1 (e ▸ hi))
    exact ih (agree_append h hv) hn.2

lemma flatMap_len_le (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g tl ih =>
    have hg := h g (by simp)
    have hs := ih (fun d hd => h d (by simp [hd]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

lemma flatMap_len_eq_all2 (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (heq : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => intro g hg; cases hg
  | cons g tl ih =>
    have hg := h g (by simp)
    have htl := flatMap_len_le tl (fun d hd => h d (by simp [hd]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at heq
    have hg2 : g.inputs.length = 2 := by omega
    have htl_eq : (tl.flatMap Gate.inputs).length = 2 * tl.length := by omega
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hg2
    · exact ih (fun d' hd' => h d' (by simp [hd'])) htl_eq d hd

lemma nodup_of_toFinset_card {α : Type*} [DecidableEq α] (l : List α)
    (h : l.toFinset.card = l.length) : l.Nodup := by
  have h1 : l.dedup.length = l.length := by
    rw [List.card_toFinset] at h
    exact h
  have hsub : l.dedup.Sublist l := List.dedup_sublist l
  have heq : l.dedup = l := hsub.eq_of_length h1
  rw [← heq]
  exact List.nodup_dedup l

lemma nodup_flatMap_unique {α β : Type*} [DecidableEq β] (f : α → List β) (gs : List α)
    (hnd : (gs.flatMap f).Nodup) {i j : Nat} (hi : i < gs.length) (hj : j < gs.length)
    {x : β} (hxi : x ∈ f (gs[i]'hi)) (hxj : x ∈ f (gs[j]'hj)) : i = j := by
  induction gs generalizing i j with
  | nil => cases hi
  | cons g tl ih =>
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso
        simp only [List.getElem_cons_zero] at hxi
        simp only [List.getElem_cons_succ] at hxj
        have hmem : x ∈ tl.flatMap f := List.mem_flatMap.mpr ⟨tl[j']'(Nat.lt_of_succ_lt_succ hj), List.getElem_mem _, hxj⟩
        exact hnd.2.2 x hxi x hmem rfl
    | succ i' =>
      cases j with
      | zero =>
        exfalso
        simp only [List.getElem_cons_succ] at hxi
        simp only [List.getElem_cons_zero] at hxj
        have hmem : x ∈ tl.flatMap f := List.mem_flatMap.mpr ⟨tl[i']'(Nat.lt_of_succ_lt_succ hi), List.getElem_mem _, hxi⟩
        exact hnd.2.2 x hxj x hmem rfl
      | succ j' =>
        simp only [List.getElem_cons_succ] at hxi hxj
        have := ih hnd.2.1 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) hxi hxj
        omega

def leaves (gs : List Gate) (w : Nat) : Finset Nat :=
  if h : 11 ≤ w ∧ w < 11 + gs.length then
    (gs[w - 11]'(by omega)).inputs.foldr (fun u acc =>
      if _ : u < w then leaves gs u ∪ acc else acc) ∅
  else if w < 11 then {w}
  else ∅

def tree (gs : List Gate) (w : Nat) : Finset (Fin gs.length) :=
  if h : 11 ≤ w ∧ w < 11 + gs.length then
    insert ⟨w - 11, by omega⟩ ((gs[w - 11]'(by omega)).inputs.foldr (fun u acc =>
      if _ : u < w then tree gs u ∪ acc else acc) ∅)
  else ∅

def rVec (p q : Fin 9) (S : Finset (Fin 9)) : Fin 9 → Bool :=
  fun i => if i = p then true else if i = q then false else decide (i ∈ S)

lemma rVec_agree_on {p q : Fin 9} {S1 S2 A : Finset (Fin 9)}
    (h : ∀ i ∈ A, (i ∈ S1 ↔ i ∈ S2)) :
    ∀ i ∈ A, rVec p q S1 i = rVec p q S2 i := by
  intro i hi
  unfold rVec
  split_ifs
  · rfl
  · rfl
  · simp [h i hi]

lemma no_and_split_gen (p q : Fin 9) (hpq : p ≠ q)
    (V M1 M2 : Finset (Fin 9)) (hV : ∀ i : Fin 9, i ∈ V ↔ i ≠ p ∧ i ≠ q)
    (hM1V : M1 ⊆ V) (hM2V : M2 ⊆ V) (hdisj : Disjoint M1 M2)
    (hM1 : perm3 (rVec p q M1) = true) (hM2 : perm3 (rVec p q M2) = true)
    (hess : ∀ i ∈ V, ∃ S : Finset (Fin 9),
      perm3 (rVec p q (S.erase i)) ≠ perm3 (rVec p q (insert i S)))
    (hcross : ∀ X : Finset (Fin 9), X ⊆ M1 ∪ M2 → ¬(M1 ⊆ X) → ¬(M2 ⊆ X) →
      perm3 (rVec p q X) = false)
    (A : Finset (Fin 9)) (hAV : A ⊆ V) (hAne : A.Nonempty) (hBne : (V \ A).Nonempty)
    (g1 g2 : (Fin 9 → Bool) → Bool)
    (hm1 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g1 x1 = true → g1 x2 = true)
    (hm2 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g2 x1 = true → g2 x2 = true)
    (hd1 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → g1 (rVec p q S1) = g1 (rVec p q S2))
    (hd2 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ V \ A, i ∈ S1 ↔ i ∈ S2) → g2 (rVec p q S1) = g2 (rVec p q S2))
    (heq : ∀ S : Finset (Fin 9), perm3 (rVec p q S) = (g1 (rVec p q S) && g2 (rVec p q S))) :
    False := by
  have hle_empty : ∀ S : Finset (Fin 9), ∀ i, rVec p q ∅ i = true → rVec p q S i = true := by
    intro S i hi
    unfold rVec at hi ⊢
    split_ifs at hi ⊢ <;> simp_all
  have hg1_empty : g1 (rVec p q ∅) = false := by
    by_contra h1
    have h1t : g1 (rVec p q ∅) = true := by cases h : g1 (rVec p q ∅) <;> simp_all
    have hg1_all : ∀ S, g1 (rVec p q S) = true := fun S => hm1 _ _ (hle_empty S) h1t
    rcases hAne with ⟨a, ha⟩
    rcases hess a (hAV ha) with ⟨S, hS⟩
    have hagree : ∀ i ∈ V \ A, i ∈ S.erase a ↔ i ∈ insert a S := by
      intro i hi
      have hne : i ≠ a := fun h => (Finset.mem_sdiff.mp hi).2 (h ▸ ha)
      simp [hne]
    have h2 := hd2 _ _ hagree
    rw [heq, heq, hg1_all, hg1_all, h2] at hS
    exact hS rfl
  have hg2_empty : g2 (rVec p q ∅) = false := by
    by_contra h2
    have h2t : g2 (rVec p q ∅) = true := by cases h : g2 (rVec p q ∅) <;> simp_all
    have hg2_all : ∀ S, g2 (rVec p q S) = true := fun S => hm2 _ _ (hle_empty S) h2t
    rcases hBne with ⟨b, hb⟩
    rcases hess b (Finset.mem_sdiff.mp hb).1 with ⟨S, hS⟩
    have hagree : ∀ i ∈ A, i ∈ S.erase b ↔ i ∈ insert b S := by
      intro i hi
      have hne : i ≠ b := fun h => (Finset.mem_sdiff.mp hb).2 (h ▸ hi)
      simp [hne]
    have h1 := hd1 _ _ hagree
    rw [heq, heq, hg2_all, hg2_all, h1] at hS
    exact hS rfl
  have hhit : ∀ M : Finset (Fin 9), M ⊆ V → perm3 (rVec p q M) = true →
      (M ∩ A).Nonempty ∧ (M ∩ (V \ A)).Nonempty := by
    intro M hMV hM
    rw [heq, Bool.and_eq_true] at hM
    constructor
    · by_contra hno
      rw [Finset.not_nonempty_iff_eq_empty] at hno
      have hagree : ∀ i ∈ A, i ∈ M ↔ i ∈ (∅ : Finset (Fin 9)) := by
        intro i hi
        simp only [Finset.notMem_empty, iff_false]
        intro hiM
        have : i ∈ M ∩ A := Finset.mem_inter.mpr ⟨hiM, hi⟩
        rw [hno] at this; exact Finset.notMem_empty _ this
      have := hd1 M ∅ hagree
      rw [hM.1, hg1_empty] at this; cases this
    · by_contra hno
      rw [Finset.not_nonempty_iff_eq_empty] at hno
      have hagree : ∀ i ∈ V \ A, i ∈ M ↔ i ∈ (∅ : Finset (Fin 9)) := by
        intro i hi
        simp only [Finset.notMem_empty, iff_false]
        intro hiM
        have : i ∈ M ∩ (V \ A) := Finset.mem_inter.mpr ⟨hiM, hi⟩
        rw [hno] at this; exact Finset.notMem_empty _ this
      have := hd2 M ∅ hagree
      rw [hM.2, hg2_empty] at this; cases this
  rcases hhit M1 hM1V hM1 with ⟨hM1A, ⟨q1, hq1⟩⟩
  rcases hhit M2 hM2V hM2 with ⟨⟨p2, hp2⟩, hM2B⟩
  set X : Finset (Fin 9) := (M1 ∩ A) ∪ (M2 ∩ (V \ A))
  have hX_sub : X ⊆ M1 ∪ M2 :=
    Finset.union_subset (Finset.inter_subset_left.trans Finset.subset_union_left)
      (Finset.inter_subset_left.trans Finset.subset_union_right)
  have hM1_not : ¬(M1 ⊆ X) := by
    intro hsub
    have hq1M1 : q1 ∈ M1 := (Finset.mem_inter.mp hq1).1
    have hq1nA : q1 ∉ A := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq1).2).2
    rcases Finset.mem_union.mp (hsub hq1M1) with h | h
    · exact hq1nA (Finset.mem_inter.mp h).2
    · exact Finset.disjoint_left.mp hdisj hq1M1 (Finset.mem_inter.mp h).1
  have hM2_not : ¬(M2 ⊆ X) := by
    intro hsub
    have hp2M2 : p2 ∈ M2 := (Finset.mem_inter.mp hp2).1
    have hp2A : p2 ∈ A := (Finset.mem_inter.mp hp2).2
    rcases Finset.mem_union.mp (hsub hp2M2) with h | h
    · exact Finset.disjoint_right.mp hdisj hp2M2 (Finset.mem_inter.mp h).1
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2 hp2A
  have hX_g1 : g1 (rVec p q X) = true := by
    have hagree : ∀ i ∈ A, i ∈ X ↔ i ∈ M1 := by
      intro i hi
      simp only [X, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, _, hna⟩)
        · exact h1
        · exact (hna hi).elim
      · intro h1; left; exact ⟨h1, hi⟩
    rw [hd1 X M1 hagree]
    rw [heq, Bool.and_eq_true] at hM1; exact hM1.1
  have hX_g2 : g2 (rVec p q X) = true := by
    have hagree : ∀ i ∈ V \ A, i ∈ X ↔ i ∈ M2 := by
      intro i hi
      have hna : i ∉ A := (Finset.mem_sdiff.mp hi).2
      simp only [X, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨_, ha⟩ | ⟨h2, _⟩)
        · exact (hna ha).elim
        · exact h2
      · intro h2; right; exact ⟨h2, hi⟩
    rw [hd2 X M2 hagree]
    rw [heq, Bool.and_eq_true] at hM2; exact hM2.2
  have hX_true : perm3 (rVec p q X) = true := by
    rw [heq, hX_g1, hX_g2]; rfl
  rw [hcross X hX_sub hM1_not hM2_not] at hX_true
  cases hX_true

lemma or_minterm_same (p q : Fin 9) (V M A : Finset (Fin 9)) (hMV : M ⊆ V)
    (g1 g2 : (Fin 9 → Bool) → Bool)
    (hd1 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → g1 (rVec p q S1) = g1 (rVec p q S2))
    (hd2 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ V \ A, i ∈ S1 ↔ i ∈ S2) → g2 (rVec p q S1) = g2 (rVec p q S2))
    (heq : ∀ S : Finset (Fin 9), perm3 (rVec p q S) = (g1 (rVec p q S) || g2 (rVec p q S)))
    (hM : perm3 (rVec p q M) = true)
    (hmin : ∀ x ∈ M, perm3 (rVec p q (M.erase x)) = false) :
    ∀ a ∈ M, ∀ b ∈ M, (a ∈ A ↔ b ∈ A) := by
  have hsub_or : M ⊆ A ∨ M ⊆ V \ A := by
    rw [heq, Bool.or_eq_true] at hM
    rcases hM with h1 | h2
    · left
      intro i hi
      by_contra hni
      have hagree : ∀ j ∈ A, j ∈ M ∩ A ↔ j ∈ M := by
        intro j hj; simp [hj]
      have hval : perm3 (rVec p q (M ∩ A)) = true := by
        rw [heq, hd1 _ _ hagree, h1]; rfl
      have hle : ∀ j, rVec p q (M ∩ A) j = true → rVec p q (M.erase i) j = true := by
        intro j hj
        unfold rVec at hj ⊢
        split_ifs at hj ⊢
        · rfl
        · simp only [decide_eq_true_eq, Finset.mem_inter, Finset.mem_erase] at hj ⊢
          exact ⟨fun h => hni (h ▸ hj.2), hj.1⟩
      have hval2 := perm3_mono _ _ hle hval
      rw [hmin i hi] at hval2; cases hval2
    · right
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨hMV hi, ?_⟩
      intro hiA
      have hagree : ∀ j ∈ V \ A, j ∈ M ∩ (V \ A) ↔ j ∈ M := by
        intro j hj; simp [hj]
      have hval : perm3 (rVec p q (M ∩ (V \ A))) = true := by
        rw [heq, hd2 _ _ hagree, h2]; simp
      have hle : ∀ j, rVec p q (M ∩ (V \ A)) j = true → rVec p q (M.erase i) j = true := by
        intro j hj
        unfold rVec at hj ⊢
        split_ifs at hj ⊢
        · rfl
        · simp only [decide_eq_true_eq, Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff] at hj ⊢
          exact ⟨fun h => hj.2.2 (h ▸ hiA), hj.1⟩
      have hval2 := perm3_mono _ _ hle hval
      rw [hmin i hi] at hval2; cases hval2
  intro a ha b hb
  rcases hsub_or with hA | hB
  · exact ⟨fun _ => hA hb, fun _ => hA ha⟩
  · have hna : a ∉ A := (Finset.mem_sdiff.mp (hB ha)).2
    have hnb : b ∉ A := (Finset.mem_sdiff.mp (hB hb)).2
    exact ⟨fun h => (hna h).elim, fun h => (hnb h).elim⟩

lemma no_split_01 (A : Finset (Fin 9))
    (hAV : A ⊆ ({2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)))
    (hAne : A.Nonempty) (hBne : (({2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) \ A).Nonempty)
    (g1 g2 : (Fin 9 → Bool) → Bool)
    (hm1 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g1 x1 = true → g1 x2 = true)
    (hm2 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g2 x1 = true → g2 x2 = true)
    (hd1 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → g1 (rVec 0 1 S1) = g1 (rVec 0 1 S2))
    (hd2 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ ({2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) \ A, i ∈ S1 ↔ i ∈ S2) →
      g2 (rVec 0 1 S1) = g2 (rVec 0 1 S2))
    (heq : (∀ S, perm3 (rVec 0 1 S) = (g1 (rVec 0 1 S) && g2 (rVec 0 1 S))) ∨
           (∀ S, perm3 (rVec 0 1 S) = (g1 (rVec 0 1 S) || g2 (rVec 0 1 S)))) : False := by
  set V : Finset (Fin 9) := {2, 3, 4, 5, 6, 7, 8}
  rcases heq with hand | hor
  · apply no_and_split_gen 0 1 (by decide) V {4, 8} {5, 7} (by intro i; fin_cases i <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ A hAV hAne hBne g1 g2 hm1 hm2 hd1 hd2 hand
    · intro i hi
      fin_cases i
      · simp [V] at hi
      · simp [V] at hi
      · exact ⟨{3, 7}, by decide⟩
      · exact ⟨{2, 7}, by decide⟩
      · exact ⟨{8}, by decide⟩
      · exact ⟨{7}, by decide⟩
      · exact ⟨{2, 4}, by decide⟩
      · exact ⟨{5}, by decide⟩
      · exact ⟨{4}, by decide⟩
    · intro X hX hM1 hM2
      have hno2 : (2 : Fin 9) ∉ X := fun h => by have := hX h; revert this; decide
      by_contra htrue
      have ht : perm3 (rVec 0 1 X) = true := by cases h : perm3 (rVec 0 1 X) <;> simp_all
      unfold perm3 rVec at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with (((((⟨⟨_, h4⟩, h8⟩ | ⟨⟨_, h5⟩, h7⟩) | ⟨⟨h1, _⟩, _⟩) | ⟨⟨h1, _⟩, _⟩) | ⟨⟨h2, _⟩, _⟩) | ⟨⟨h2, _⟩, _⟩)
      · exact hM1 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h4); exact (by simpa using h8))
      · exact hM2 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h5); exact (by simpa using h7))
      · simp at h1
      · simp at h1
      · simp [hno2] at h2
      · simp [hno2] at h2
  · have hM1 := or_minterm_same 0 1 V {4, 8} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM2 := or_minterm_same 0 1 V {5, 7} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM3 := or_minterm_same 0 1 V {2, 3, 7} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM4 := or_minterm_same 0 1 V {2, 4, 6} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hall : ∀ i ∈ V, (i ∈ A ↔ (2 : Fin 9) ∈ A) := by
      have e48 : (8 : Fin 9) ∈ A ↔ (4 : Fin 9) ∈ A := hM1 8 (by decide) 4 (by decide)
      have e57 : (5 : Fin 9) ∈ A ↔ (7 : Fin 9) ∈ A := hM2 5 (by decide) 7 (by decide)
      have e32 : (3 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 3 (by decide) 2 (by decide)
      have e72 : (7 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 7 (by decide) 2 (by decide)
      have e42 : (4 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM4 4 (by decide) 2 (by decide)
      have e62 : (6 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM4 6 (by decide) 2 (by decide)
      intro i hi
      fin_cases i
      · simp [V] at hi
      · simp [V] at hi
      · rfl
      · exact e32
      · exact e42
      · exact e57.trans e72
      · exact e62
      · exact e72
      · exact e48.trans e42
    rcases hAne with ⟨a, ha⟩
    rcases hBne with ⟨b, hb⟩
    exact (Finset.mem_sdiff.mp hb).2 ((hall b (Finset.mem_sdiff.mp hb).1).mpr ((hall a (hAV ha)).mp ha))

lemma no_split_05 (A : Finset (Fin 9))
    (hAV : A ⊆ ({1, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)))
    (hAne : A.Nonempty) (hBne : (({1, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)) \ A).Nonempty)
    (g1 g2 : (Fin 9 → Bool) → Bool)
    (hm1 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g1 x1 = true → g1 x2 = true)
    (hm2 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g2 x1 = true → g2 x2 = true)
    (hd1 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → g1 (rVec 0 5 S1) = g1 (rVec 0 5 S2))
    (hd2 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ ({1, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)) \ A, i ∈ S1 ↔ i ∈ S2) →
      g2 (rVec 0 5 S1) = g2 (rVec 0 5 S2))
    (heq : (∀ S, perm3 (rVec 0 5 S) = (g1 (rVec 0 5 S) && g2 (rVec 0 5 S))) ∨
           (∀ S, perm3 (rVec 0 5 S) = (g1 (rVec 0 5 S) || g2 (rVec 0 5 S)))) : False := by
  set V : Finset (Fin 9) := {1, 2, 3, 4, 6, 7, 8}
  rcases heq with hand | hor
  · apply no_and_split_gen 0 5 (by decide) V {4, 8} {2, 3, 7} (by intro i; fin_cases i <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ A hAV hAne hBne g1 g2 hm1 hm2 hd1 hd2 hand
    · intro i hi
      fin_cases i
      · simp [V] at hi
      · exact ⟨{3, 8}, by decide⟩
      · exact ⟨{3, 7}, by decide⟩
      · exact ⟨{2, 7}, by decide⟩
      · exact ⟨{8}, by decide⟩
      · simp [V] at hi
      · exact ⟨{2, 4}, by decide⟩
      · exact ⟨{2, 3}, by decide⟩
      · exact ⟨{4}, by decide⟩
    · intro X hX hM1 hM2
      have hno1 : (1 : Fin 9) ∉ X := fun h => by have := hX h; revert this; decide
      have hno6 : (6 : Fin 9) ∉ X := fun h => by have := hX h; revert this; decide
      by_contra htrue
      have ht : perm3 (rVec 0 5 X) = true := by cases h : perm3 (rVec 0 5 X) <;> simp_all
      unfold perm3 rVec at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with (((((⟨⟨_, h4⟩, h8⟩ | ⟨⟨_, h5⟩, _⟩) | ⟨⟨h1, _⟩, _⟩) | ⟨⟨h1, _⟩, _⟩) | ⟨⟨h2, h3⟩, h7⟩) | ⟨⟨_, _⟩, h6⟩)
      · exact hM1 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h4); exact (by simpa using h8))
      · simp at h5
      · simp [hno1] at h1
      · simp [hno1] at h1
      · exact hM2 (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl; exact (by simpa using h2); exact (by simpa using h3); exact (by simpa using h7))
      · simp [hno6] at h6
  · have hM1 := or_minterm_same 0 5 V {4, 8} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM2 := or_minterm_same 0 5 V {1, 3, 8} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM3 := or_minterm_same 0 5 V {2, 3, 7} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM4 := or_minterm_same 0 5 V {2, 4, 6} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hall : ∀ i ∈ V, (i ∈ A ↔ (2 : Fin 9) ∈ A) := by
      have e48 : (8 : Fin 9) ∈ A ↔ (4 : Fin 9) ∈ A := hM1 8 (by decide) 4 (by decide)
      have e18 : (1 : Fin 9) ∈ A ↔ (8 : Fin 9) ∈ A := hM2 1 (by decide) 8 (by decide)
      have e32 : (3 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 3 (by decide) 2 (by decide)
      have e72 : (7 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 7 (by decide) 2 (by decide)
      have e42 : (4 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM4 4 (by decide) 2 (by decide)
      have e62 : (6 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM4 6 (by decide) 2 (by decide)
      intro i hi
      fin_cases i
      · simp [V] at hi
      · exact e18.trans (e48.trans e42)
      · rfl
      · exact e32
      · exact e42
      · simp [V] at hi
      · exact e62
      · exact e72
      · exact e48.trans e42
    rcases hAne with ⟨a, ha⟩
    rcases hBne with ⟨b, hb⟩
    exact (Finset.mem_sdiff.mp hb).2 ((hall b (Finset.mem_sdiff.mp hb).1).mpr ((hall a (hAV ha)).mp ha))

lemma no_split_41 (A : Finset (Fin 9))
    (hAV : A ⊆ ({0, 2, 3, 5, 6, 7, 8} : Finset (Fin 9)))
    (hAne : A.Nonempty) (hBne : (({0, 2, 3, 5, 6, 7, 8} : Finset (Fin 9)) \ A).Nonempty)
    (g1 g2 : (Fin 9 → Bool) → Bool)
    (hm1 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g1 x1 = true → g1 x2 = true)
    (hm2 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g2 x1 = true → g2 x2 = true)
    (hd1 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → g1 (rVec 4 1 S1) = g1 (rVec 4 1 S2))
    (hd2 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ ({0, 2, 3, 5, 6, 7, 8} : Finset (Fin 9)) \ A, i ∈ S1 ↔ i ∈ S2) →
      g2 (rVec 4 1 S1) = g2 (rVec 4 1 S2))
    (heq : (∀ S, perm3 (rVec 4 1 S) = (g1 (rVec 4 1 S) && g2 (rVec 4 1 S))) ∨
           (∀ S, perm3 (rVec 4 1 S) = (g1 (rVec 4 1 S) || g2 (rVec 4 1 S)))) : False := by
  set V : Finset (Fin 9) := {0, 2, 3, 5, 6, 7, 8}
  rcases heq with hand | hor
  · apply no_and_split_gen 4 1 (by decide) V {0, 8} {2, 6} (by intro i; fin_cases i <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ A hAV hAne hBne g1 g2 hm1 hm2 hd1 hd2 hand
    · intro i hi
      fin_cases i
      · exact ⟨{8}, by decide⟩
      · simp [V] at hi
      · exact ⟨{6}, by decide⟩
      · exact ⟨{2, 7}, by decide⟩
      · simp [V] at hi
      · exact ⟨{0, 7}, by decide⟩
      · exact ⟨{2}, by decide⟩
      · exact ⟨{0, 5}, by decide⟩
      · exact ⟨{0}, by decide⟩
    · intro X hX hM1 hM2
      have hno7 : (7 : Fin 9) ∉ X := fun h => by have := hX h; revert this; decide
      by_contra htrue
      have ht : perm3 (rVec 4 1 X) = true := by cases h : perm3 (rVec 4 1 X) <;> simp_all
      unfold perm3 rVec at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with (((((⟨⟨h0, _⟩, h8⟩ | ⟨⟨_, _⟩, h7⟩) | ⟨⟨h1, _⟩, _⟩) | ⟨⟨h1, _⟩, _⟩) | ⟨⟨_, _⟩, h7⟩) | ⟨⟨h2, _⟩, h6⟩)
      · exact hM1 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h0); exact (by simpa using h8))
      · simp [hno7] at h7
      · simp at h1
      · simp at h1
      · simp [hno7] at h7
      · exact hM2 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h2); exact (by simpa using h6))
  · have hM1 := or_minterm_same 4 1 V {0, 8} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM2 := or_minterm_same 4 1 V {0, 5, 7} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM3 := or_minterm_same 4 1 V {2, 3, 7} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM4 := or_minterm_same 4 1 V {2, 6} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hall : ∀ i ∈ V, (i ∈ A ↔ (2 : Fin 9) ∈ A) := by
      have e80 : (8 : Fin 9) ∈ A ↔ (0 : Fin 9) ∈ A := hM1 8 (by decide) 0 (by decide)
      have e07 : (0 : Fin 9) ∈ A ↔ (7 : Fin 9) ∈ A := hM2 0 (by decide) 7 (by decide)
      have e57 : (5 : Fin 9) ∈ A ↔ (7 : Fin 9) ∈ A := hM2 5 (by decide) 7 (by decide)
      have e32 : (3 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 3 (by decide) 2 (by decide)
      have e72 : (7 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 7 (by decide) 2 (by decide)
      have e62 : (6 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM4 6 (by decide) 2 (by decide)
      intro i hi
      fin_cases i
      · exact e07.trans e72
      · simp [V] at hi
      · rfl
      · exact e32
      · simp [V] at hi
      · exact e57.trans e72
      · exact e62
      · exact e72
      · exact e80.trans (e07.trans e72)
    rcases hAne with ⟨a, ha⟩
    rcases hBne with ⟨b, hb⟩
    exact (Finset.mem_sdiff.mp hb).2 ((hall b (Finset.mem_sdiff.mp hb).1).mpr ((hall a (hAV ha)).mp ha))

lemma no_split_45 (A : Finset (Fin 9))
    (hAV : A ⊆ ({0, 1, 2, 3, 6, 7, 8} : Finset (Fin 9)))
    (hAne : A.Nonempty) (hBne : (({0, 1, 2, 3, 6, 7, 8} : Finset (Fin 9)) \ A).Nonempty)
    (g1 g2 : (Fin 9 → Bool) → Bool)
    (hm1 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g1 x1 = true → g1 x2 = true)
    (hm2 : ∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → g2 x1 = true → g2 x2 = true)
    (hd1 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → g1 (rVec 4 5 S1) = g1 (rVec 4 5 S2))
    (hd2 : ∀ S1 S2 : Finset (Fin 9), (∀ i ∈ ({0, 1, 2, 3, 6, 7, 8} : Finset (Fin 9)) \ A, i ∈ S1 ↔ i ∈ S2) →
      g2 (rVec 4 5 S1) = g2 (rVec 4 5 S2))
    (heq : (∀ S, perm3 (rVec 4 5 S) = (g1 (rVec 4 5 S) && g2 (rVec 4 5 S))) ∨
           (∀ S, perm3 (rVec 4 5 S) = (g1 (rVec 4 5 S) || g2 (rVec 4 5 S)))) : False := by
  set V : Finset (Fin 9) := {0, 1, 2, 3, 6, 7, 8}
  rcases heq with hand | hor
  · apply no_and_split_gen 4 5 (by decide) V {0, 8} {2, 6} (by intro i; fin_cases i <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ A hAV hAne hBne g1 g2 hm1 hm2 hd1 hd2 hand
    · intro i hi
      fin_cases i
      · exact ⟨{8}, by decide⟩
      · exact ⟨{3, 8}, by decide⟩
      · exact ⟨{6}, by decide⟩
      · exact ⟨{2, 7}, by decide⟩
      · simp [V] at hi
      · simp [V] at hi
      · exact ⟨{2}, by decide⟩
      · exact ⟨{2, 3}, by decide⟩
      · exact ⟨{0}, by decide⟩
    · intro X hX hM1 hM2
      have hno3 : (3 : Fin 9) ∉ X := fun h => by have := hX h; revert this; decide
      by_contra htrue
      have ht : perm3 (rVec 4 5 X) = true := by cases h : perm3 (rVec 4 5 X) <;> simp_all
      unfold perm3 rVec at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with (((((⟨⟨h0, _⟩, h8⟩ | ⟨⟨_, h5⟩, _⟩) | ⟨⟨_, h3⟩, _⟩) | ⟨⟨_, h5⟩, _⟩) | ⟨⟨_, h3⟩, _⟩) | ⟨⟨h2, _⟩, h6⟩)
      · exact hM1 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h0); exact (by simpa using h8))
      · simp at h5
      · simp [hno3] at h3
      · simp at h5
      · simp [hno3] at h3
      · exact hM2 (by intro x hx; simp at hx; rcases hx with rfl | rfl; exact (by simpa using h2); exact (by simpa using h6))
  · have hM1 := or_minterm_same 4 5 V {0, 8} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM2 := or_minterm_same 4 5 V {1, 3, 8} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM3 := or_minterm_same 4 5 V {2, 3, 7} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hM4 := or_minterm_same 4 5 V {2, 6} A (by decide) g1 g2 hd1 hd2 hor (by decide) (by decide)
    have hall : ∀ i ∈ V, (i ∈ A ↔ (2 : Fin 9) ∈ A) := by
      have e08 : (0 : Fin 9) ∈ A ↔ (8 : Fin 9) ∈ A := hM1 0 (by decide) 8 (by decide)
      have e13 : (1 : Fin 9) ∈ A ↔ (3 : Fin 9) ∈ A := hM2 1 (by decide) 3 (by decide)
      have e83 : (8 : Fin 9) ∈ A ↔ (3 : Fin 9) ∈ A := hM2 8 (by decide) 3 (by decide)
      have e32 : (3 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 3 (by decide) 2 (by decide)
      have e72 : (7 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM3 7 (by decide) 2 (by decide)
      have e62 : (6 : Fin 9) ∈ A ↔ (2 : Fin 9) ∈ A := hM4 6 (by decide) 2 (by decide)
      intro i hi
      fin_cases i
      · exact e08.trans (e83.trans e32)
      · exact e13.trans e32
      · rfl
      · exact e32
      · simp [V] at hi
      · simp [V] at hi
      · exact e62
      · exact e72
      · exact e83.trans e32
    rcases hAne with ⟨a, ha⟩
    rcases hBne with ⟨b, hb⟩
    exact (Finset.mem_sdiff.mp hb).2 ((hall b (Finset.mem_sdiff.mp hb).1).mpr ((hall a (hAV ha)).mp ha))

end PEqualNP.Outside.L_meta_27623

theorem PEqualNP.Outside.L_meta_27623 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩)) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_27623 in
  rintro ⟨⟨gates, out⟩, hfan, hsize, heval, hout, hnf, _, hused, h0, h1⟩
  cases gates with
  | nil => simp at h0
  | cons a rest =>
    cases rest with
    | nil => simp at h1
    | cons b gs =>
      have ha_eq : a = g0 := Option.some.inj h0
      have hb_eq : b = g1 := Option.some.inj h1
      subst ha_eq hb_eq
      change (g0 :: g1 :: gs).length ≤ 12 at hsize
      change out + 1 = 9 + (g0 :: g1 :: gs).length at hout
      simp only [List.length_cons] at hsize hout
      have hprim : ∀ v : Fin 9, v.val ∈ gs.flatMap Gate.inputs := by
        intro v
        by_contra hn
        have ha := (agree_run (agree_warm v) gs hn).2 out (by omega)
        rw [← prefix_run gs out, ← prefix_run gs out] at ha
        change (Circuit.mk (g0 :: g1 :: gs) out).eval (List.ofFn (high v)) =
          (Circuit.mk (g0 :: g1 :: gs) out).eval (List.ofFn (low v)) at ha
        exact separates v ((heval (high v)).symm.trans (ha.trans (heval (low v))))
      have hreq : Finset.range (10 + gs.length) ⊆ (gs.flatMap Gate.inputs).toFinset := by
        intro z hz
        rw [Finset.mem_range] at hz
        rw [List.mem_toFinset]
        by_cases hz9 : z < 9
        · exact hprim ⟨z, hz9⟩
        · let j : Fin (g0 :: g1 :: gs).length := ⟨z - 9, by simp; omega⟩
          obtain ⟨k, _, hk⟩ := hused j (by simp [j]; omega)
          let g := (g0 :: g1 :: gs).get k
          have hg : z ∈ g.inputs := by
            have eq : 9 + j.val = z := by dsimp [j]; omega
            rwa [eq] at hk
          have hmem : g ∈ g0 :: g1 :: gs := List.get_mem _ _
          have htail : g ∈ gs := by
            rcases List.mem_cons.mp hmem with e | hrest
            · have hh : z ∈ g0.inputs := e ▸ hg
              simp [g0] at hh; omega
            · rcases List.mem_cons.mp hrest with e | htail
              · have hh : z ∈ g1.inputs := e ▸ hg
                simp [g1] at hh; omega
              · exact htail
          exact List.mem_flatMap.mpr ⟨g, htail, hg⟩
      have hcard_ge : 10 + gs.length ≤ (gs.flatMap Gate.inputs).toFinset.card := by
        simpa [Finset.card_range] using Finset.card_le_card hreq
      have hcard_le_len : (gs.flatMap Gate.inputs).toFinset.card ≤ (gs.flatMap Gate.inputs).length :=
        List.toFinset_card_le _
      have hlen_le : (gs.flatMap Gate.inputs).length ≤ 2 * gs.length :=
        flatMap_len_le gs (fun g hg => (hfan g (by simp [hg])).2)
      have hgs_len : gs.length = 10 := by omega
      have hout_eq : out = 20 := by omega
      have hflat_len : (gs.flatMap Gate.inputs).length = 20 := by omega
      have hflat_card : (gs.flatMap Gate.inputs).toFinset.card = 20 := by omega
      have hnd : (gs.flatMap Gate.inputs).Nodup :=
        nodup_of_toFinset_card _ (by omega)
      have hall2 : ∀ g ∈ gs, g.inputs.length = 2 :=
        flatMap_len_eq_all2 gs (fun g hg => (hfan g (by simp [hg])).2) (by omega)
      have hgs_nf : ∀ (j : Fin gs.length),
          ((gs[j.val]'j.isLt).op = .and ∨ (gs[j.val]'j.isLt).op = .or) ∧
          ∃ u v, u < v ∧ v < 11 + j.val ∧ (gs[j.val]'j.isLt).inputs = [u, v] := by
        intro j
        have h := hnf ⟨j.val + 2, by simp⟩
        simp only [List.get_eq_getElem, List.getElem_cons_succ] at h
        rcases h with ⟨_, a', _, hins⟩ | ⟨hop, u, v, huv, hv, hins⟩
        · have h2 := hall2 (gs[j.val]'j.isLt) (List.getElem_mem _)
          rw [hins] at h2; simp at h2
        · refine ⟨hop, u, v, huv, ?_, hins⟩
          omega
      have hrb : ∀ (j : Nat) (hj : j < gs.length), ∀ i ∈ (gs[j]'hj).inputs, i < 11 + j := by
        intro j hj i hi
        rcases hgs_nf ⟨j, hj⟩ with ⟨_, u, v, huv, hv, hins⟩
        simp only [Fin.val_mk] at hv
        rw [hins] at hi; simp at hi
        rcases hi with rfl | rfl <;> omega
      let F : Nat → (Fin 9 → Bool) → Bool := fun w x => (run gs (warm x)).getD w false
      have hF_out : ∀ x, F 20 x = perm3 x := by
        intro x
        have h := heval x
        change ((Circuit.mk (g0 :: g1 :: gs) out).wires (List.ofFn x)).getD out false = perm3 x at h
        rw [prefix_run, hout_eq] at h
        exact h
      have hF_lt11 : ∀ w < 11, ∀ x, F w x = (warm x).getD w false := by
        intro w hw x
        exact run_prefix gs (warm x) (by rw [warm_length]; exact hw)
      have hF_at : ∀ (j : Nat) (hj : j < gs.length) (x : Fin 9 → Bool),
          F (11 + j) x = (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => F i x) := by
        intro j hj x
        have h := run_at gs (warm x) j hj (by rw [warm_length]; exact hrb j hj)
        rw [warm_length] at h
        exact h
      have hleaves_lt : ∀ w < 11, leaves gs w = {w} := by
        intro w hw
        rw [leaves]
        split_ifs
        · omega
        · rfl
      have hleaves_gate : ∀ j : Fin gs.length,
          leaves gs (11 + j.val) =
            (gs[j.val]'j.isLt).inputs.foldr (fun u acc => leaves gs u ∪ acc) ∅ := by
        intro j
        rw [leaves]
        split_ifs
        · simp only [Nat.add_sub_cancel_left]
          have hfold : ∀ l : List Nat, (∀ u ∈ l, u < 11 + j.val) →
              l.foldr (fun u acc => if _ : u < 11 + j.val then leaves gs u ∪ acc else acc) ∅ =
              l.foldr (fun u acc => leaves gs u ∪ acc) ∅ := by
            intro l hl
            induction l with
            | nil => rfl
            | cons a' tl ih =>
              simp only [List.foldr_cons, hl a' List.mem_cons_self, ↓reduceDIte]
              rw [ih (fun u hu => hl u (List.mem_cons_of_mem a' hu))]
          exact hfold _ (hrb j.val j.isLt)
        · omega
        · omega
      have htree_lt : ∀ w < 11, tree gs w = ∅ := by
        intro w hw
        rw [tree]
        split_ifs
        · omega
        · rfl
      have htree_gate : ∀ j : Fin gs.length,
          tree gs (11 + j.val) =
            insert j ((gs[j.val]'j.isLt).inputs.foldr (fun u acc => tree gs u ∪ acc) ∅) := by
        intro j
        rw [tree]
        split_ifs
        · have hj_eq : (⟨11 + j.val - 11, by omega⟩ : Fin gs.length) = j := by ext; simp
          rw [hj_eq]
          simp only [Nat.add_sub_cancel_left]
          congr 1
          have hfold : ∀ l : List Nat, (∀ u ∈ l, u < 11 + j.val) →
              l.foldr (fun u acc => if _ : u < 11 + j.val then tree gs u ∪ acc else acc) ∅ =
              l.foldr (fun u acc => tree gs u ∪ acc) ∅ := by
            intro l hl
            induction l with
            | nil => rfl
            | cons a' tl ih =>
              simp only [List.foldr_cons, hl a' List.mem_cons_self, ↓reduceDIte]
              rw [ih (fun u hu => hl u (List.mem_cons_of_mem a' hu))]
          exact hfold _ (hrb j.val j.isLt)
        · omega
      have hprops : ∀ w < 21,
          (leaves gs w ⊆ Finset.range 11) ∧
          (leaves gs w).Nonempty ∧
          (∀ j ∈ tree gs w, 11 + j.val ≤ w) ∧
          (∀ j ∈ tree gs w, 11 + j.val ≠ w → ∃ k ∈ tree gs w, 11 + j.val ∈ (gs[k.val]'k.isLt).inputs) ∧
          (∀ z ∈ leaves gs w, w = z ∨ ∃ k ∈ tree gs w, z ∈ (gs[k.val]'k.isLt).inputs) ∧
          (∀ x1 x2, (∀ i, x1 i = true → x2 i = true) → F w x1 = true → F w x2 = true) ∧
          (∀ x1 x2, (∀ z ∈ leaves gs w, (warm x1).getD z false = (warm x2).getD z false) →
            F w x1 = F w x2) ∧
          (leaves gs w ⊆ {9, 10} → ∀ b : Bool, ∀ x,
            (warm x).getD 9 false = b → (warm x).getD 10 false = b → F w x = b) := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hw11 : w < 11
          · rw [hleaves_lt w hw11, htree_lt w hw11]
            refine ⟨by intro z hz; simp at hz; subst hz; simp [hw11], ⟨w, by simp⟩,
              fun j hj => by simp at hj, fun j hj => by simp at hj,
              fun z hz => Or.inl (by simp at hz; omega), ?_, ?_, ?_⟩
            · intro x1 x2 hle hx1
              rw [hF_lt11 w hw11] at hx1 ⊢
              by_cases hw9 : w < 9
              · have h1 : w = (⟨w, hw9⟩ : Fin 9).val := rfl
                rw [h1, warm_getD_lt9] at hx1
                rw [h1, warm_getD_lt9]
                exact hle ⟨w, hw9⟩ hx1
              · by_cases hw9eq : w = 9
                · subst hw9eq
                  rw [warm_getD_9] at hx1 ⊢
                  simp only [Bool.or_eq_true] at hx1 ⊢
                  rcases hx1 with h | h
                  · exact Or.inl (hle 0 h)
                  · exact Or.inr (hle 4 h)
                · have hw10 : w = 10 := by omega
                  subst hw10
                  rw [warm_getD_10] at hx1 ⊢
                  simp only [Bool.and_eq_true] at hx1 ⊢
                  exact ⟨hle 1 hx1.1, hle 5 hx1.2⟩
            · intro x1 x2 hagree
              rw [hF_lt11 w hw11, hF_lt11 w hw11]
              exact hagree w (by simp)
            · intro hsub b x h9 h10
              rw [hF_lt11 w hw11]
              have hw_in : w ∈ ({9, 10} : Finset Nat) := hsub (by simp)
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw_in
              rcases hw_in with rfl | rfl
              · exact h9
              · exact h10
          · set j : Fin gs.length := ⟨w - 11, by omega⟩
            have hwj : w = 11 + j.val := by simp [j]; omega
            rcases hgs_nf j with ⟨hop, u, v, huv, hv, hins⟩
            have ihu := ih u (by omega) (by omega)
            have ihv := ih v (by omega) (by omega)
            rw [hwj, hleaves_gate j, htree_gate j, hins]
            simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
            refine ⟨Finset.union_subset ihu.1 ihv.1, ihu.2.1.mono Finset.subset_union_left,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro j' hj'
              rcases Finset.mem_insert.mp hj' with rfl | hj'
              · exact le_refl _
              · rcases Finset.mem_union.mp hj' with hj' | hj'
                · exact Nat.le_trans (ihu.2.2.1 j' hj') (by omega)
                · exact Nat.le_trans (ihv.2.2.1 j' hj') (by omega)
            · intro j' hj' hne
              rcases Finset.mem_insert.mp hj' with rfl | hj'
              · exact (hne rfl).elim
              · rcases Finset.mem_union.mp hj' with hj' | hj'
                · by_cases hju : 11 + j'.val = u
                  · exact ⟨j, Finset.mem_insert_self _ _, by rw [hins, hju]; exact List.mem_cons_self⟩
                  · rcases ihu.2.2.2.1 j' hj' hju with ⟨k, hk, hkin⟩
                    exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
                · by_cases hjv : 11 + j'.val = v
                  · exact ⟨j, Finset.mem_insert_self _ _,
                      by rw [hins, hjv]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
                  · rcases ihv.2.2.2.1 j' hj' hjv with ⟨k, hk, hkin⟩
                    exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
            · intro z hz
              right
              rcases Finset.mem_union.mp hz with hz | hz
              · rcases ihu.2.2.2.2.1 z hz with heq | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _, by rw [hins, ← heq]; exact List.mem_cons_self⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkin⟩
              · rcases ihv.2.2.2.2.1 z hz with heq | ⟨k, hk, hkin⟩
                · exact ⟨j, Finset.mem_insert_self _ _,
                    by rw [hins, ← heq]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkin⟩
            · intro x1 x2 hle hx1
              rw [hF_at j.val j.isLt x1, hins] at hx1
              rw [hF_at j.val j.isLt x2, hins]
              rcases hop with hop | hop
              · rw [hop] at hx1 ⊢
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true, Bool.and_eq_true] at hx1 ⊢
                exact ⟨ihu.2.2.2.2.2.1 x1 x2 hle hx1.1, ihv.2.2.2.2.2.1 x1 x2 hle hx1.2⟩
              · rw [hop] at hx1 ⊢
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false, Bool.or_eq_true] at hx1 ⊢
                rcases hx1 with h | h
                · exact Or.inl (ihu.2.2.2.2.2.1 x1 x2 hle h)
                · exact Or.inr (ihv.2.2.2.2.2.1 x1 x2 hle h)
            · intro x1 x2 hagree
              rw [hF_at j.val j.isLt x1, hF_at j.val j.isLt x2, hins]
              simp only [List.map_cons, List.map_nil]
              rw [ihu.2.2.2.2.2.2.1 x1 x2 (fun z hz => hagree z (Finset.mem_union_left _ hz)),
                ihv.2.2.2.2.2.2.1 x1 x2 (fun z hz => hagree z (Finset.mem_union_right _ hz))]
            · intro hsub bv x h9 h10
              rw [hF_at j.val j.isLt x, hins]
              simp only [List.map_cons, List.map_nil]
              have hfu := ihu.2.2.2.2.2.2.2 (Finset.subset_union_left.trans hsub) bv x h9 h10
              have hfv := ihv.2.2.2.2.2.2.2 (Finset.subset_union_right.trans hsub) bv x h9 h10
              rw [hfu, hfv]
              rcases hop with hop | hop <;> (rw [hop]; cases bv <;> rfl)
      set jtop : Fin gs.length := ⟨9, by omega⟩
      rcases hgs_nf jtop with ⟨hop_top, u, v, huv, hv_lt, hins_top⟩
      have hu_lt21 : u < 21 := by dsimp [jtop] at hv_lt; omega
      have hv_lt21 : v < 21 := by dsimp [jtop] at hv_lt; omega
      have ihu := hprops u hu_lt21
      have ihv := hprops v hv_lt21
      have htree_disj : Disjoint (tree gs u) (tree gs v) := by
        rw [Finset.disjoint_iff_ne]
        intro j1 hj1 j2 hj2 heq
        subst heq
        set I := tree gs u ∩ tree gs v
        have hIne : I.Nonempty := ⟨j1, Finset.mem_inter.mpr ⟨hj1, hj2⟩⟩
        obtain ⟨jmax, hjmax_mem, hjmax_max⟩ := Finset.exists_max_image I Fin.val hIne
        have hjmax_u : jmax ∈ tree gs u := (Finset.mem_inter.mp hjmax_mem).1
        have hjmax_v : jmax ∈ tree gs v := (Finset.mem_inter.mp hjmax_mem).2
        have hk1 : ∃ k1 : Fin gs.length, 11 + jmax.val ∈ (gs[k1.val]'k1.isLt).inputs ∧
            ((k1 = jtop ∧ 11 + jmax.val = u) ∨ k1 ∈ tree gs u) := by
          by_cases hju : 11 + jmax.val = u
          · exact ⟨jtop, by rw [hins_top, hju]; exact List.mem_cons_self, Or.inl ⟨rfl, hju⟩⟩
          · rcases ihu.2.2.2.1 jmax hjmax_u hju with ⟨k1, hk1_u, hk1_in⟩
            exact ⟨k1, hk1_in, Or.inr hk1_u⟩
        have hk2 : ∃ k2 : Fin gs.length, 11 + jmax.val ∈ (gs[k2.val]'k2.isLt).inputs ∧
            ((k2 = jtop ∧ 11 + jmax.val = v) ∨ k2 ∈ tree gs v) := by
          by_cases hjv : 11 + jmax.val = v
          · exact ⟨jtop, by rw [hins_top, hjv]; exact List.mem_cons_of_mem _ List.mem_cons_self,
              Or.inl ⟨rfl, hjv⟩⟩
          · rcases ihv.2.2.2.1 jmax hjmax_v hjv with ⟨k2, hk2_v, hk2_in⟩
            exact ⟨k2, hk2_in, Or.inr hk2_v⟩
        rcases hk1 with ⟨k1, hk1_in, hk1_or⟩
        rcases hk2 with ⟨k2, hk2_in, hk2_or⟩
        have heq_k : k1.val = k2.val :=
          nodup_flatMap_unique Gate.inputs gs hnd k1.isLt k2.isLt hk1_in hk2_in
        have heq_k' : k1 = k2 := Fin.ext heq_k
        subst heq_k'
        rcases hk1_or with ⟨rfl, hju⟩ | h1'
        · rcases hk2_or with ⟨_, hjv⟩ | h2'
          · omega
          · have := ihv.2.2.1 jtop h2'; dsimp [jtop] at this hv_lt; omega
        · rcases hk2_or with ⟨rfl, _⟩ | h2'
          · have := ihu.2.2.1 jtop h1'; dsimp [jtop] at this hv_lt; omega
          · have hk_I : k1 ∈ I := Finset.mem_inter.mpr ⟨h1', h2'⟩
            have hle := hjmax_max k1 hk_I
            have hlt := hrb k1.val k1.isLt (11 + jmax.val) hk1_in
            omega
      have hleaves_disj : Disjoint (leaves gs u) (leaves gs v) := by
        rw [Finset.disjoint_left]
        intro z hzu hzv
        have hk1 : ∃ k1 : Fin gs.length, z ∈ (gs[k1.val]'k1.isLt).inputs ∧
            ((k1 = jtop ∧ u = z) ∨ k1 ∈ tree gs u) := by
          rcases ihu.2.2.2.2.1 z hzu with heq | ⟨k1, hk1_u, hk1_in⟩
          · exact ⟨jtop, by rw [hins_top, ← heq]; exact List.mem_cons_self, Or.inl ⟨rfl, heq⟩⟩
          · exact ⟨k1, hk1_in, Or.inr hk1_u⟩
        have hk2 : ∃ k2 : Fin gs.length, z ∈ (gs[k2.val]'k2.isLt).inputs ∧
            ((k2 = jtop ∧ v = z) ∨ k2 ∈ tree gs v) := by
          rcases ihv.2.2.2.2.1 z hzv with heq | ⟨k2, hk2_v, hk2_in⟩
          · exact ⟨jtop, by rw [hins_top, ← heq]; exact List.mem_cons_of_mem _ List.mem_cons_self,
              Or.inl ⟨rfl, heq⟩⟩
          · exact ⟨k2, hk2_in, Or.inr hk2_v⟩
        rcases hk1 with ⟨k1, hk1_in, hk1_or⟩
        rcases hk2 with ⟨k2, hk2_in, hk2_or⟩
        have heq_k : k1 = k2 := Fin.ext
          (nodup_flatMap_unique Gate.inputs gs hnd k1.isLt k2.isLt hk1_in hk2_in)
        subst heq_k
        rcases hk1_or with ⟨rfl, huz⟩ | h1'
        · rcases hk2_or with ⟨_, hvz⟩ | h2'
          · omega
          · have := ihv.2.2.1 jtop h2'; dsimp [jtop] at this hv_lt; omega
        · rcases hk2_or with ⟨rfl, _⟩ | h2'
          · have := ihu.2.2.1 jtop h1'; dsimp [jtop] at this hv_lt; omega
          · exact Finset.disjoint_left.mp htree_disj h1' h2'
      have htop_eq : (∀ x, perm3 x = (F u x && F v x)) ∨ (∀ x, perm3 x = (F u x || F v x)) := by
        rcases hop_top with hop | hop
        · left
          intro x
          rw [← hF_out x]
          have h := hF_at jtop.val jtop.isLt x
          dsimp [jtop] at h
          rw [h, hins_top, hop]
          simp [GateOp.eval]
        · right
          intro x
          rw [← hF_out x]
          have h := hF_at jtop.val jtop.isLt x
          dsimp [jtop] at h
          rw [h, hins_top, hop]
          simp [GateOp.eval]
      have h2_mem : 2 ∈ leaves gs u ∨ 2 ∈ leaves gs v := by
        by_contra hno
        push Not at hno
        have hagree_u : ∀ z ∈ leaves gs u,
            (warm (high 2)).getD z false = (warm (low 2)).getD z false := fun z hz =>
          (agree_warm 2).2 z (fun he => hno.1 (by simpa [he] using hz))
        have hagree_v : ∀ z ∈ leaves gs v,
            (warm (high 2)).getD z false = (warm (low 2)).getD z false := fun z hz =>
          (agree_warm 2).2 z (fun he => hno.2 (by simpa [he] using hz))
        have hu_eq := ihu.2.2.2.2.2.2.1 _ _ hagree_u
        have hv_eq := ihv.2.2.2.2.2.2.1 _ _ hagree_v
        rcases htop_eq with h | h
        · exact separates 2 (by rw [h, h, hu_eq, hv_eq])
        · exact separates 2 (by rw [h, h, hu_eq, hv_eq])
      have hkill_pair : ∀ (w1 w2 : Nat), w1 < 21 → w2 < 21 →
          Disjoint (leaves gs w1) (leaves gs w2) →
          2 ∈ leaves gs w2 →
          ((∀ x, perm3 x = (F w1 x && F w2 x)) ∨ (∀ x, perm3 x = (F w1 x || F w2 x))) →
          False := by
        intro w1 w2 hw1 hw2 hdj h2w2 hteq
        have hp1 := hprops w1 hw1
        have hp2 := hprops w2 hw2
        have hmk_dep : ∀ (p q : Fin 9) (hp : p = 0 ∨ p = 4) (hq : q = 1 ∨ q = 5)
            (V : Finset (Fin 9)) (hV : ∀ i : Fin 9, i ∈ V ↔ i ≠ p ∧ i ≠ q),
            let A := V.filter (fun i => i.val ∈ leaves gs w1)
            (∀ S1 S2 : Finset (Fin 9), (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) →
              F w1 (rVec p q S1) = F w1 (rVec p q S2)) ∧
            (∀ S1 S2 : Finset (Fin 9), (∀ i ∈ V \ A, i ∈ S1 ↔ i ∈ S2) →
              F w2 (rVec p q S1) = F w2 (rVec p q S2)) := by
          intro p q hp hq V hV
          have h9_eq : ∀ S, (warm (rVec p q S)).getD 9 false = true := by
            intro S
            rw [warm_getD_9]
            rcases hp with rfl | rfl <;> simp [rVec]
          have h10_eq : ∀ S, (warm (rVec p q S)).getD 10 false = false := by
            intro S
            rw [warm_getD_10]
            have hpq : p ≠ q := by rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> decide
            rcases hq with rfl | rfl <;> simp [rVec, hpq.symm]
          constructor
          · intro S1 S2 hagree
            apply hp1.2.2.2.2.2.2.1
            intro z hz
            have hz11 : z < 11 := Finset.mem_range.mp (hp1.1 hz)
            by_cases hz9 : z < 9
            · let i : Fin 9 := ⟨z, hz9⟩
              change (warm (rVec p q S1)).getD i.val false = (warm (rVec p q S2)).getD i.val false
              rw [warm_getD_lt9, warm_getD_lt9]
              unfold rVec
              by_cases hip : i = p
              · simp [hip]
              · by_cases hiq : i = q
                · simp [hip, hiq]
                · simp only [hip, ↓reduceIte, hiq]
                  have hiA : i ∈ V.filter (fun i => i.val ∈ leaves gs w1) :=
                    Finset.mem_filter.mpr ⟨(hV i).mpr ⟨hip, hiq⟩, hz⟩
                  simp [hagree i hiA]
            · by_cases hz9eq : z = 9
              · subst hz9eq; rw [h9_eq, h9_eq]
              · have hz10 : z = 10 := by omega
                subst hz10; rw [h10_eq, h10_eq]
          · intro S1 S2 hagree
            apply hp2.2.2.2.2.2.2.1
            intro z hz
            have hz11 : z < 11 := Finset.mem_range.mp (hp2.1 hz)
            by_cases hz9 : z < 9
            · let i : Fin 9 := ⟨z, hz9⟩
              change (warm (rVec p q S1)).getD i.val false = (warm (rVec p q S2)).getD i.val false
              rw [warm_getD_lt9, warm_getD_lt9]
              unfold rVec
              by_cases hip : i = p
              · simp [hip]
              · by_cases hiq : i = q
                · simp [hip, hiq]
                · simp only [hip, ↓reduceIte, hiq]
                  have hiB : i ∈ V \ V.filter (fun i => i.val ∈ leaves gs w1) := by
                    refine Finset.mem_sdiff.mpr ⟨(hV i).mpr ⟨hip, hiq⟩, ?_⟩
                    intro hmem
                    exact Finset.disjoint_left.mp hdj (Finset.mem_filter.mp hmem).2 hz
                  simp [hagree i hiB]
            · by_cases hz9eq : z = 9
              · subst hz9eq; rw [h9_eq, h9_eq]
              · have hz10 : z = 10 := by omega
                subst hz10; rw [h10_eq, h10_eq]
        have hno_in_V : ∀ (p q : Fin 9) (V : Finset (Fin 9)),
            (p = 0 ∨ p = 4) → (q = 1 ∨ q = 5) →
            (∀ i : Fin 9, i ∈ V ↔ i ≠ p ∧ i ≠ q) →
            (2 : Fin 9) ∈ V →
            (∀ A : Finset (Fin 9), A ⊆ V → A.Nonempty → (V \ A).Nonempty →
              (∀ S1 S2, (∀ i ∈ A, i ∈ S1 ↔ i ∈ S2) → F w1 (rVec p q S1) = F w1 (rVec p q S2)) →
              (∀ S1 S2, (∀ i ∈ V \ A, i ∈ S1 ↔ i ∈ S2) → F w2 (rVec p q S1) = F w2 (rVec p q S2)) →
              ((∀ S, perm3 (rVec p q S) = (F w1 (rVec p q S) && F w2 (rVec p q S))) ∨
               (∀ S, perm3 (rVec p q S) = (F w1 (rVec p q S) || F w2 (rVec p q S)))) → False) →
            ∀ i ∈ V, i.val ∉ leaves gs w1 := by
          intro p q V hp hq hV h2V hnosplit i hi hiw1
          set A := V.filter (fun j => j.val ∈ leaves gs w1)
          have hAV : A ⊆ V := Finset.filter_subset _ _
          have hAne : A.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hiw1⟩⟩
          have hBne : (V \ A).Nonempty := ⟨2, Finset.mem_sdiff.mpr ⟨h2V, fun h =>
            Finset.disjoint_left.mp hdj (Finset.mem_filter.mp h).2 h2w2⟩⟩
          have hd := hmk_dep p q hp hq V hV
          have hteq' : (∀ S, perm3 (rVec p q S) = (F w1 (rVec p q S) && F w2 (rVec p q S))) ∨
              (∀ S, perm3 (rVec p q S) = (F w1 (rVec p q S) || F w2 (rVec p q S))) := by
            rcases hteq with h | h
            · left; intro S; exact h (rVec p q S)
            · right; intro S; exact h (rVec p q S)
          exact hnosplit A hAV hAne hBne hd.1 hd.2 hteq'
        have hno01 := hno_in_V 0 1 {2, 3, 4, 5, 6, 7, 8} (Or.inl rfl) (Or.inl rfl)
          (by intro i; fin_cases i <;> decide) (by decide)
          (fun A hAV hAne hBne hd1 hd2 hteq' =>
            no_split_01 A hAV hAne hBne (F w1) (F w2) hp1.2.2.2.2.2.1 hp2.2.2.2.2.2.1 hd1 hd2 hteq')
        have hno05 := hno_in_V 0 5 {1, 2, 3, 4, 6, 7, 8} (Or.inl rfl) (Or.inr rfl)
          (by intro i; fin_cases i <;> decide) (by decide)
          (fun A hAV hAne hBne hd1 hd2 hteq' =>
            no_split_05 A hAV hAne hBne (F w1) (F w2) hp1.2.2.2.2.2.1 hp2.2.2.2.2.2.1 hd1 hd2 hteq')
        have hno41 := hno_in_V 4 1 {0, 2, 3, 5, 6, 7, 8} (Or.inr rfl) (Or.inl rfl)
          (by intro i; fin_cases i <;> decide) (by decide)
          (fun A hAV hAne hBne hd1 hd2 hteq' =>
            no_split_41 A hAV hAne hBne (F w1) (F w2) hp1.2.2.2.2.2.1 hp2.2.2.2.2.2.1 hd1 hd2 hteq')
        have hno_any : ∀ i : Fin 9, i.val ∉ leaves gs w1 := by
          intro i
          fin_cases i
          · exact hno41 0 (by decide)
          · exact hno05 1 (by decide)
          · exact hno01 2 (by decide)
          · exact hno01 3 (by decide)
          · exact hno01 4 (by decide)
          · exact hno01 5 (by decide)
          · exact hno01 6 (by decide)
          · exact hno01 7 (by decide)
          · exact hno01 8 (by decide)
        have hsub910 : leaves gs w1 ⊆ {9, 10} := by
          intro z hz
          have hz11 : z < 11 := Finset.mem_range.mp (hp1.1 hz)
          by_cases hz9 : z < 9
          · exact (hno_any ⟨z, hz9⟩ hz).elim
          · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rcases hteq with hand | hor
        · let x : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 3 ∨ i = 7)
          have h9 : (warm x).getD 9 false = false := by rw [warm_getD_9]; decide
          have h10 : (warm x).getD 10 false = false := by rw [warm_getD_10]; decide
          have hfw1 : F w1 x = false := hp1.2.2.2.2.2.2.2 hsub910 false x h9 h10
          have hp : perm3 x = true := by decide
          rw [hand x, hfw1] at hp
          cases hp
        · let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5)
          have h9 : (warm x).getD 9 false = true := by rw [warm_getD_9]; decide
          have h10 : (warm x).getD 10 false = true := by rw [warm_getD_10]; decide
          have hfw1 : F w1 x = true := hp1.2.2.2.2.2.2.2 hsub910 true x h9 h10
          have hp : perm3 x = false := by decide
          rw [hor x, hfw1] at hp
          cases hp
      rcases h2_mem with h2u | h2v
      · exact hkill_pair v u hv_lt21 hu_lt21 hleaves_disj.symm h2u (by
          rcases htop_eq with h | h
          · left; intro x; rw [h x, Bool.and_comm]
          · right; intro x; rw [h x, Bool.or_comm])
      · exact hkill_pair u v hu_lt21 hv_lt21 hleaves_disj h2v htop_eq
