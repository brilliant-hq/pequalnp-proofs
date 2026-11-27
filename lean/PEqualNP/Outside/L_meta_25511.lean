import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25511

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = stp (W gs x) g := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega

theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih

theorem or_true_of (g : Gate) (w : List Bool) (c : ℕ) (hc : c ∈ g.inputs) (hv : w.getD c false = true) :
    GateOp.or.eval (g.inputs.map fun i => w.getD i false) = true := by
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨c, hc, hv⟩, rfl⟩

theorem and_false_of (g : Gate) (w : List Bool) (c : ℕ) (hc : c ∈ g.inputs) (hv : w.getD c false = false) :
    GateOp.and.eval (g.inputs.map fun i => w.getD i false) = false := by
  cases h : GateOp.and.eval (g.inputs.map fun i => w.getD i false)
  · rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at h
    have := h false ⟨c, hc, hv⟩
    simp at this

theorem op_symm_tf (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval [true, false] = op.eval [false, true] := by
  rcases h with rfl | rfl <;> rfl

theorem eval_eq (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]

theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]

theorem W_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]).inputs, i < x.length + j) :
    (W gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (W gs x).getD i false) := by
  have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
    rw [List.take_succ]; simp [List.getElem?_eq_getElem hj]
  rw [W_take gs x (j + 1) _ (by omega), h1, W_snoc, stp]
  have hl : (W (gs.take j) x).length = x.length + j := by
    rw [W_len, List.length_take]; omega
  have := getD_app_m (W (gs.take j) x) ((gs[j]).op.eval ((gs[j]).inputs.map fun i => (W (gs.take j) x).getD i false))
  rw [hl] at this
  rw [this]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (W_take gs x j i (hrb i hi)).symm

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    have : i ≠ n + v.val := by omega
    simp [List.getElem?_ofFn, h, this, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simpa using h)]
    have hu : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - n < m
    · simp [List.getElem?_ofFn, h2, hu, Fin.ext_iff]; omega
    · have : i ≠ n + v.val := by have := v.isLt; omega
      simp [List.getElem?_ofFn, h2, hu, this]

theorem rb_idx (C : Circuit) (N : ℕ) (hrb : ReadsBack N C) :
    ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < N + j := by
  intro j hj i hi
  exact hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)

def stepBack (C : Circuit) (N : ℕ) (j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if j ∈ S then
    S ∪ (((gateAt C j).inputs.filter (fun w => decide (N ≤ w ∧ w < N + j))).map
      (fun w => w - N)).toFinset
  else S

def reachBack (C : Circuit) (N : ℕ) : ℕ → Finset ℕ → Finset ℕ
  | 0, S => S
  | k + 1, S => reachBack C N k (stepBack C N k S)

theorem subset_stepBack (C : Circuit) (N j : ℕ) (S : Finset ℕ) :
    S ⊆ stepBack C N j S := by
  unfold stepBack
  split_ifs
  · exact Finset.subset_union_left
  · exact Finset.Subset.refl S

theorem subset_reachBack (C : Circuit) (N k : ℕ) (S : Finset ℕ) :
    S ⊆ reachBack C N k S := by
  induction k generalizing S with
  | zero => exact Finset.Subset.refl S
  | succ k ih =>
    exact Finset.Subset.trans (subset_stepBack C N k S) (ih (stepBack C N k S))

theorem mem_stepBack_ge (C : Circuit) (N j : ℕ) (S : Finset ℕ) (x : ℕ) (hx : j ≤ x) :
    x ∈ stepBack C N j S ↔ x ∈ S := by
  unfold stepBack
  split_ifs with hj
  · simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro (h | ⟨w, ⟨_, h1, h2⟩, rfl⟩)
      · exact h
      · omega
    · exact Or.inl
  · rfl

theorem mem_reachBack_ge (C : Circuit) (N k : ℕ) (S : Finset ℕ) (x : ℕ) (hx : k ≤ x) :
    x ∈ reachBack C N k S ↔ x ∈ S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    change x ∈ reachBack C N k (stepBack C N k S) ↔ x ∈ S
    rw [ih (stepBack C N k S) (by omega), mem_stepBack_ge C N k S x (by omega)]

theorem reachBack_lt (C : Circuit) (N k M : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < M) (hk : k ≤ M) :
    ∀ x ∈ reachBack C N k S, x < M := by
  induction k generalizing S with
  | zero => exact hS
  | succ k ih =>
    apply ih (stepBack C N k S) _ (by omega)
    intro x hx
    unfold stepBack at hx
    split_ifs at hx with h
    · simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hx
      rcases hx with hx | ⟨w, ⟨_, h1, h2⟩, rfl⟩
      · exact hS x hx
      · omega
    · exact hS x hx

theorem reachBack_closed (C : Circuit) (N k : ℕ) (S : Finset ℕ) :
    ∀ j ∈ reachBack C N k S, j < k →
      ∀ w ∈ (gateAt C j).inputs, N ≤ w → w < N + j → w - N ∈ reachBack C N k S := by
  induction k generalizing S with
  | zero => intro j _ h; omega
  | succ k ih =>
    intro j hj hjk w hw hN hlt
    change j ∈ reachBack C N k (stepBack C N k S) at hj
    change w - N ∈ reachBack C N k (stepBack C N k S)
    by_cases hlt' : j < k
    · exact ih (stepBack C N k S) j hj hlt' w hw hN hlt
    · have hjk_eq : j = k := by omega
      subst hjk_eq
      have h1 : j ∈ stepBack C N j S :=
        (mem_reachBack_ge C N j (stepBack C N j S) j (le_refl j)).mp hj
      have h2 : j ∈ S := (mem_stepBack_ge C N j S j (le_refl j)).mp h1
      have h3 : w - N ∈ stepBack C N j S := by
        unfold stepBack
        simp only [h2, ↓reduceIte, Finset.mem_union, List.mem_toFinset, List.mem_map,
          List.mem_filter, decide_eq_true_eq]
        exact Or.inr ⟨w, ⟨hw, hN, hlt⟩, rfl⟩
      exact subset_reachBack C N j (stepBack C N j S) h3

theorem reachBack_parent (C : Circuit) (N k out : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x = out ∨ ∃ p ∈ S, N + x ∈ (gateAt C p).inputs) :
    ∀ x ∈ reachBack C N k S, x = out ∨ ∃ p ∈ reachBack C N k S, N + x ∈ (gateAt C p).inputs := by
  induction k generalizing S with
  | zero => exact hS
  | succ k ih =>
    apply ih (stepBack C N k S)
    intro x hx
    unfold stepBack at hx
    split_ifs at hx with hk
    · simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hx
      rcases hx with hx | ⟨w, ⟨hw, hN, hlt⟩, rfl⟩
      · rcases hS x hx with rfl | ⟨p, hp, hwp⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨p, subset_stepBack C N k S hp, hwp⟩
      · refine Or.inr ⟨k, subset_stepBack C N k S hk, ?_⟩
        have e : N + (w - N) = w := by omega
        rw [e]; exact hw
    · rcases hS x hx with rfl | ⟨p, hp, hwp⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨p, subset_stepBack C N k S hp, hwp⟩

theorem core2_L (N : ℕ) (X Y : List Bool) (hX : X.length = N) (hY : Y.length = N) (bad : ℕ → Prop)
    (hin : ∀ i, ¬ bad i → X.getD i false = Y.getD i false) (C : Circuit) (L : Finset ℕ)
    (hLsub : ∀ j ∈ L, j < C.gates.length)
    (hLcl : ∀ j ∈ L, ∀ w ∈ (gateAt C j).inputs, N ≤ w → w - N ∈ L)
    (hrb : ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < N + j)
    (hg : ∀ j ∈ L, (∃ i ∈ (gateAt C j).inputs, bad i) →
      (W C.gates X).getD (N + j) false = (W C.gates Y).getD (N + j) false) :
    ∀ i, (i < N ∨ (N ≤ i ∧ i - N ∈ L)) → ¬ bad i →
      (W C.gates X).getD i false = (W C.gates Y).getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hdom hi
    by_cases h1 : i < N
    · rw [W_lt _ _ _ (by omega), W_lt _ _ _ (by omega)]; exact hin i hi
    · rcases hdom with hlt | ⟨hge, hmem⟩
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
        have hjL : j ∈ L := by simpa [Nat.add_sub_cancel_left] using hmem
        have hj : j < C.gates.length := hLsub j hjL
        by_cases hb : ∃ k ∈ (gateAt C j).inputs, bad k
        · exact hg j hjL hb
        · simp only [not_exists, not_and] at hb
          have vX := W_val C.gates X j hj (by rw [hX]; exact hrb j hj)
          have vY := W_val C.gates Y j hj (by rw [hY]; exact hrb j hj)
          rw [hX] at vX
          rw [hY] at vY
          rw [vX, vY]
          congr 1
          apply List.map_congr_left
          intro k hk
          have hk' : k ∈ (gateAt C j).inputs := by rwa [gateAt_eq C j hj]
          have hkdom : k < N ∨ (N ≤ k ∧ k - N ∈ L) := by
            by_cases hkN : k < N
            · exact Or.inl hkN
            · exact Or.inr ⟨by omega, hLcl j hjL k hk' (by omega)⟩
          exact ih k (hrb j hj k hk) hkdom (hb k hk')

theorem count_le_readsIn (C : Circuit) (L : Finset ℕ) (w j : ℕ) (hj : j ∈ L) :
    (gateAt C j).inputs.count w ≤ readsIn C L w := by
  simpa [readsIn] using
    Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count w) (fun _ _ => Nat.zero_le _) hj

theorem uniq_idx_L (C : Circuit) (L : Finset ℕ) (w : ℕ)
    (h1 : readsIn C L w = 1)
    (j0 : ℕ) (hj0 : j0 ∈ L) (hw0 : w ∈ (gateAt C j0).inputs)
    (j : ℕ) (hj : j ∈ L) (hw : w ∈ (gateAt C j).inputs) : j = j0 := by
  by_contra hjj
  have hsub : ({j, j0} : Finset ℕ) ⊆ L := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset
    (f := fun t => (gateAt C t).inputs.count w) hsub
  rw [Finset.sum_pair hjj] at hle
  have c1 : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
  have c2 : 0 < (gateAt C j0).inputs.count w := List.count_pos_iff.mpr hw0
  unfold readsIn at h1
  omega

theorem exists_mem_of_readsIn_pos (C : Circuit) (L : Finset ℕ) (w : ℕ)
    (hpos : 0 < readsIn C L w) : ∃ j ∈ L, w ∈ (gateAt C j).inputs := by
  by_contra hall
  push_neg at hall
  have hzero : readsIn C L w = 0 := by
    unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    exact List.count_eq_zero.mpr (hall j hj)
  omega

theorem list_len_eq_sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ x ∈ l, x ∈ S) :
    l.length = ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ∈ S := h a (by simp)
    have ht : t.length = ∑ w ∈ S, t.count w := ih (fun x hx => h x (by simp [hx]))
    have hstep : ∀ w, (a :: t).count w = t.count w + (if w = a then 1 else 0) := by
      intro w
      rw [List.count_cons]
      by_cases hwa : w = a
      · subst hwa; simp
      · have hne : (a == w) = false := beq_eq_false_iff_ne.mpr (Ne.symm hwa)
        simp [hwa, hne]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib]
    have h1 : (∑ w ∈ S, if w = a then 1 else 0) = 1 := by simp [ha]
    rw [h1, ← ht]
    simp

theorem list_len2_mem (l : List ℕ) (hl : l.length = 2) (w : ℕ) (hw : w ∈ l) :
    ∃ w', l = [w, w'] ∨ l = [w', w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨b, Or.inl rfl⟩
    · exact ⟨a, Or.inr rfl⟩
  · simp at hl

theorem list_len1_uniq (l : List ℕ) (hl : l.length = 1) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l) :
    a = b := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    omega
  · simp at hl

theorem range_filter_eq_list_filter (gs : List Gate) (p : Gate → Bool) :
    ((Finset.range gs.length).filter
      (fun j => p (gs.getD j ⟨GateOp.or, []⟩) = true)).card = (gs.filter p).length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, Finset.range_add_one,
      Finset.filter_insert, List.filter_append, List.length_append]
    have hget_last : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
      simp [List.getD_eq_getElem?_getD]
    have hcongr : (Finset.range gs.length).filter
        (fun j => p ((gs ++ [g]).getD j ⟨GateOp.or, []⟩) = true) =
        (Finset.range gs.length).filter
          (fun j => p (gs.getD j ⟨GateOp.or, []⟩) = true) := by
      apply Finset.filter_congr
      intro j hj
      have hjl : j < gs.length := Finset.mem_range.mp hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]
    rw [hget_last, hcongr]
    have hnotmem : gs.length ∉ (Finset.range gs.length).filter
        (fun j => p (gs.getD j ⟨GateOp.or, []⟩) = true) := by
      simp
    cases hp : p g
    · rw [ite_eq_right (by simp [hp]), ih]
      simp [hp]
    · rw [ite_eq_left (by simp [hp]), Finset.card_insert_of_notMem hnotmem, ih]
      simp [hp]

theorem sq (n m a gap : ℕ) (G : Fin n → Fin n → Bool) (rowPair : (Fin m × Bool) ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n))
    (hrow : ∀ i, (Finset.univ.filter
      (fun col : Fin n => G (rowPair (i, false)) col ≠ G (rowPair (i, true)) col)).card ≤ a)
    (hcol : ∀ b c, b ≠ c → a + gap ≤ (Finset.univ.filter (fun row : Fin n => G row b ≠ G row c)).card)
    (hsym : ∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) :
    gap * m ≤ gap * (n - kept.card) + ∑ u ∈ Finset.univ \ kept,
      min (Finset.univ.filter (fun onCol : Fin n => G u onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G u offCol = false)).card := by
  classical
  have hD : (Finset.univ \ kept).card = n - kept.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ kept), Finset.card_univ, Fintype.card_fin]
  let S : Finset (Fin m) := Finset.univ.filter
    (fun i => rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept)
  have hlost : (Finset.univ \ S).card ≤ (Finset.univ \ kept).card := by
    apply Finset.card_le_card_of_injOn
      (fun i => if rowPair (i, false) ∈ kept then rowPair (i, true) else rowPair (i, false))
    · intro i hi
      simp only [S, Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, not_and] at hi ⊢
      split_ifs with h
      · exact hi h
      · exact h
    · intro i _ j _ hij
      dsimp only at hij
      split_ifs at hij <;> simpa using rowPair.injective hij
  have hm : m ≤ S.card + (Finset.univ \ kept).card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hsurv : ∀ i ∈ S, gap ≤ ((Finset.univ \ kept).filter
      (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
    intro i hi
    obtain ⟨hp, hq⟩ : rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept := by
      simpa [S] using hi
    have hne : π (rowPair (i, false)) ≠ π (rowPair (i, true)) := by
      intro h
      have := rowPair.injective (π.injective h)
      simp at this
    have h1 := hcol _ _ hne
    have h2 : (Finset.univ.filter
        (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card
        = (kept.filter
            (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card
          + ((Finset.univ \ kept).filter
            (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
      rw [← Finset.card_union_of_disjoint, ← Finset.filter_union,
        Finset.union_sdiff_of_subset (Finset.subset_univ kept)]
      exact Finset.disjoint_filter_filter Finset.disjoint_sdiff
    have h3 : (kept.filter
        (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤ a := by
      refine le_trans ?_ (hrow i)
      apply Finset.card_le_card_of_injOn (fun w => π w)
      · intro w hw
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw ⊢
        rw [← hsym w hw.1 _ hp, ← hsym w hw.1 _ hq]
        exact hw.2
      · exact π.injective.injOn
    omega
  have hsum : gap * S.card ≤ ∑ w ∈ Finset.univ \ kept, (S.filter
      (fun i => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
    calc gap * S.card = ∑ _i ∈ S, gap := by simp [mul_comm]
      _ ≤ ∑ i ∈ S, ((Finset.univ \ kept).filter
          (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card :=
        Finset.sum_le_sum hsurv
      _ = _ := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
  have hmin : ∀ w : Fin n, (S.filter
      (fun i => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤
      min (Finset.univ.filter (fun onCol : Fin n => G w onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G w offCol = false)).card := by
    intro w
    apply le_min
    · apply Finset.card_le_card_of_injOn
        (fun i => if G w (π (rowPair (i, false))) = true then π (rowPair (i, false))
          else π (rowPair (i, true)))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
        split_ifs with h
        · exact h
        · have h' := hi.2
          revert h h'
          cases G w (π (rowPair (i, false))) <;> cases G w (π (rowPair (i, true))) <;> simp
      · intro i _ j _ hij
        dsimp only at hij
        split_ifs at hij <;> simpa using rowPair.injective (π.injective hij)
    · apply Finset.card_le_card_of_injOn
        (fun i => if G w (π (rowPair (i, false))) = false then π (rowPair (i, false))
          else π (rowPair (i, true)))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
        split_ifs with h
        · exact h
        · have h' := hi.2
          revert h h'
          cases G w (π (rowPair (i, false))) <;> cases G w (π (rowPair (i, true))) <;> simp
      · intro i _ j _ hij
        dsimp only at hij
        split_ifs at hij <;> simpa using rowPair.injective (π.injective hij)
  rw [← hD]
  calc gap * m ≤ gap * (S.card + (Finset.univ \ kept).card) := Nat.mul_le_mul_left _ hm
    _ = gap * (Finset.univ \ kept).card + gap * S.card := by ring
    _ ≤ _ := Nat.add_le_add_left (hsum.trans (Finset.sum_le_sum fun w _ => hmin w)) _

def P (m u v : ℕ) : Prop :=
  u / 2 = v / 2 ∨ (v % 2 = 0 ∧ (u / 2 = v / 2 + 1 ∨ u / 2 + m = v / 2 + 1)) ∨
    (v % 2 = 1 ∧ (u / 2 = v / 2 + 2 + u % 2 ∨ u / 2 + m = v / 2 + 2 + u % 2))

def Gm (m u v : ℕ) : Bool :=
  decide (u / 2 = v / 2 ∨ u / 2 = (v / 2 + if v % 2 = 0 then 1 else 2 + u % 2) % m)

theorem Gm_iff (m u v : ℕ) (hm : 5 ≤ m) (hu : u < 2 * m) (hv : v < 2 * m) :
    Gm m u v = true ↔ P m u v := by
  unfold Gm P
  rw [decide_eq_true_iff]
  by_cases hp : v % 2 = 0
  · rw [ite_eq_left hp]
    by_cases hlt : v / 2 + 1 < m
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have e : (v / 2 + 1) % m = v / 2 + 1 - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e]; omega
  · rw [ite_eq_right hp]
    by_cases hlt : v / 2 + (2 + u % 2) < m
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have e : (v / 2 + (2 + u % 2)) % m = v / 2 + (2 + u % 2) - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e]; omega

theorem f1 (m i v v' : ℕ) (hm : 5 ≤ m) (hi : i < m) (hv : v < 2 * m) (hv' : v' < 2 * m)
    (h1 : ¬ (P m (2 * i) v ↔ P m (2 * i + 1) v)) (h2 : ¬ (P m (2 * i) v' ↔ P m (2 * i + 1) v'))
    (h3 : P m (2 * i) v ↔ P m (2 * i) v') : v = v' := by
  by_cases a1 : P m (2 * i) v <;> by_cases a2 : P m (2 * i + 1) v <;>
    by_cases b1 : P m (2 * i) v' <;> by_cases b2 : P m (2 * i + 1) v' <;>
    first
    | (exfalso; exact h1 ⟨fun _ => a2, fun _ => a1⟩)
    | (exfalso; exact h1 ⟨fun h => absurd h a1, fun h => absurd h a2⟩)
    | (exfalso; exact h2 ⟨fun _ => b2, fun _ => b1⟩)
    | (exfalso; exact h2 ⟨fun h => absurd h b1, fun h => absurd h b2⟩)
    | (exfalso; exact b1 (h3.1 a1))
    | (exfalso; exact a1 (h3.2 b1))
    | (unfold P at a1 a2 b1 b2; omega)

def rw4 (m v e t : ℕ) : ℕ :=
  2 * (if e = 0 then v / 2 else
    if v / 2 + (if v % 2 = 0 then 1 else 2 + t) < m then v / 2 + (if v % 2 = 0 then 1 else 2 + t)
    else v / 2 + (if v % 2 = 0 then 1 else 2 + t) - m) + t

theorem rw4_lt (m v e t : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (ht : t < 2) : rw4 m v e t < 2 * m := by
  unfold rw4; split_ifs <;> omega

theorem rw4_P (m v e t : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (ht : t < 2) : P m (rw4 m v e t) v := by
  unfold rw4 P; split_ifs <;> omega

theorem rw4_inj (m v e t e' t' : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (he : e < 2) (ht : t < 2)
    (he' : e' < 2) (ht' : t' < 2) (h : rw4 m v e t = rw4 m v e' t') : e = e' ∧ t = t' := by
  unfold rw4 at h; split_ifs at h <;> omega

theorem f3 (m r r' c c' : ℕ) (hm : 5 ≤ m) (hr : r < 2 * m) (hr' : r' < 2 * m) (hc : c < 2 * m)
    (hc' : c' < 2 * m) (hne : c ≠ c') (h1 : P m r c) (h2 : P m r c') (h3 : P m r' c) (h4 : P m r' c')
    (hf1 : c % 2 = 1 ∧ c' % 2 = 1 → (r / 2 = c / 2 ↔ r' / 2 = c / 2))
    (hf2 : ¬ (c % 2 = 1 ∧ c' % 2 = 1) → (r % 2 = 0 ↔ r' % 2 = 0)) : r = r' := by
  unfold P at *; omega

theorem f4 (m u v v' : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (hv' : v' < 2 * m)
    (h1 : P m u v) (h2 : P m u v') (h3 : v % 2 = 0 ↔ v' % 2 = 0) (h4 : u / 2 = v / 2 ↔ u / 2 = v' / 2) :
    v = v' := by
  unfold P at *; omega

theorem f5 (m u : ℕ) (hm : 5 ≤ m) (hu : u < 2 * m) : ∃ c, c < 2 * m ∧ ¬ P m u c :=
  ⟨2 * (if u / 2 + 1 < m then u / 2 + 1 else u / 2 + 1 - m), by split_ifs <;> omega,
    by unfold P; split_ifs <;> omega⟩

theorem f6 (m c : ℕ) (hm : 5 ≤ m) (hc : c < 2 * m) : ∃ u, u < 2 * m ∧ ¬ P m u c :=
  ⟨2 * (if c / 2 + 4 < m then c / 2 + 4 else c / 2 + 4 - m), by split_ifs <;> omega,
    by unfold P; split_ifs <;> omega⟩

theorem f_row_ne (m u1 u2 : ℕ) (hm : 5 ≤ m) (h1 : u1 < 2 * m) (h2 : u2 < 2 * m) (hne : u1 ≠ u2) :
    ∃ v < 2 * m, ¬ (P m u1 v ↔ P m u2 v) := by
  by_cases hdiv : u1 / 2 = u2 / 2
  · refine ⟨2 * (if 2 ≤ u1 / 2 then u1 / 2 - 2 else u1 / 2 + m - 2) + 1,
      by split_ifs <;> omega, ?_⟩
    intro hiff
    by_cases hp : u1 % 2 = 0
    · have hP1 : P m u1 (2 * (if 2 ≤ u1 / 2 then u1 / 2 - 2 else u1 / 2 + m - 2) + 1) := by
        unfold P; split_ifs <;> omega
      have hP2 := hiff.1 hP1
      unfold P at hP2; split_ifs at hP2 <;> omega
    · have hP2 : P m u2 (2 * (if 2 ≤ u1 / 2 then u1 / 2 - 2 else u1 / 2 + m - 2) + 1) := by
        unfold P; split_ifs <;> omega
      have hP1 := hiff.2 hP2
      unfold P at hP1; split_ifs at hP1 <;> omega
  · by_cases hP : P m u2 (2 * (u1 / 2))
    · refine ⟨2 * (if 1 ≤ u1 / 2 then u1 / 2 - 1 else m - 1), by split_ifs <;> omega, ?_⟩
      intro hiff
      have hP1 : P m u1 (2 * (if 1 ≤ u1 / 2 then u1 / 2 - 1 else m - 1)) := by
        unfold P; split_ifs <;> omega
      have hP2 := hiff.1 hP1
      unfold P at hP hP2; split_ifs at hP hP2 <;> omega
    · refine ⟨2 * (u1 / 2), by omega, ?_⟩
      intro hiff
      exact hP (hiff.1 (by unfold P; omega))

def GG (m : ℕ) : Fin (2 * m) → Fin (2 * m) → Bool := fun u v => Gm m u.val v.val

theorem GG_iff (m : ℕ) (hm : 5 ≤ m) (u v : Fin (2 * m)) : GG m u v = true ↔ P m u.val v.val :=
  Gm_iff m _ _ hm u.isLt v.isLt

theorem row_ne (m : ℕ) (hm : 5 ≤ m) (u1 u2 : Fin (2 * m)) (hne : u1 ≠ u2) :
    ∃ v : Fin (2 * m), GG m u1 v ≠ GG m u2 v := by
  obtain ⟨v, hv, hneP⟩ := f_row_ne m u1.val u2.val hm u1.isLt u2.isLt (fun h => hne (Fin.ext h))
  refine ⟨⟨v, hv⟩, ?_⟩
  intro heq
  apply hneP
  rw [← GG_iff m hm u1 ⟨v, hv⟩, ← GG_iff m hm u2 ⟨v, hv⟩, heq]

def rp (m : ℕ) : (Fin m × Bool) ↪ Fin (2 * m) :=
  ⟨fun x => ⟨2 * x.1.val + (if x.2 = true then 1 else 0), by
    have := x.1.isLt
    split_ifs <;> omega⟩, by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have h' : 2 * i.val + (if s = true then 1 else 0) = 2 * j.val + (if t = true then 1 else 0) :=
      congrArg Fin.val h
    have hi : i = j := Fin.ext (by split_ifs at h' <;> omega)
    subst hi
    have hst : s = t := by
      cases s <;> cases t <;> first | rfl | (exfalso; simp at h')
    rw [hst]⟩

theorem rp0 (m : ℕ) (i : Fin m) : (rp m (i, false)).val = 2 * i.val := by
  show 2 * i.val + (if (false : Bool) = true then 1 else 0) = 2 * i.val
  simp

theorem rp1 (m : ℕ) (i : Fin m) : (rp m (i, true)).val = 2 * i.val + 1 := by
  show 2 * i.val + (if (true : Bool) = true then 1 else 0) = 2 * i.val + 1
  simp

theorem rowdist (m : ℕ) (hm : 5 ≤ m) (i : Fin m) :
    (Finset.univ.filter
      (fun col : Fin (2 * m) => GG m (rp m (i, false)) col ≠ GG m (rp m (i, true)) col)).card ≤ 2 := by
  have hG0 : ∀ v : Fin (2 * m), GG m (rp m (i, false)) v = true ↔ P m (2 * i.val) v.val := by
    intro v
    have h := GG_iff m hm (rp m (i, false)) v
    rwa [rp0] at h
  have hG1 : ∀ v : Fin (2 * m), GG m (rp m (i, true)) v = true ↔ P m (2 * i.val + 1) v.val := by
    intro v
    have h := GG_iff m hm (rp m (i, true)) v
    rwa [rp1] at h
  calc _ ≤ (Finset.univ : Finset Bool).card := by
        apply Finset.card_le_card_of_injOn (fun v => GG m (rp m (i, false)) v)
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro v hv v' hv' h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
          apply Fin.ext
          apply f1 m i.val v.val v'.val hm i.isLt v.isLt v'.isLt
          · intro hiff
            exact hv (Bool.eq_iff_iff.2 ((hG0 v).trans (hiff.trans (hG1 v).symm)))
          · intro hiff
            exact hv' (Bool.eq_iff_iff.2 ((hG0 v').trans (hiff.trans (hG1 v').symm)))
          · rw [← hG0 v, ← hG0 v']
            dsimp only at h
            rw [h]
    _ = 2 := by simp

theorem col4 (m : ℕ) (hm : 5 ≤ m) (c : Fin (2 * m)) :
    4 ≤ (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true)).card := by
  calc 4 = (Finset.univ : Finset (Fin 2 × Fin 2)).card := by simp
    _ ≤ _ := by
        apply Finset.card_le_card_of_injOn
          (fun x : Fin 2 × Fin 2 => (⟨rw4 m c.val x.1.val x.2.val,
            rw4_lt m c.val x.1.val x.2.val hm c.isLt x.2.isLt⟩ : Fin (2 * m)))
        · intro x _
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (GG_iff m hm _ c).2 (rw4_P m c.val x.1.val x.2.val hm c.isLt x.2.isLt)
        · intro x _ y _ h
          have h' := rw4_inj m c.val x.1.val x.2.val y.1.val y.2.val hm c.isLt x.1.isLt x.2.isLt
            y.1.isLt y.2.isLt (congrArg Fin.val h)
          exact Prod.ext (Fin.ext h'.1) (Fin.ext h'.2)

theorem common2 (m : ℕ) (hm : 5 ≤ m) (b c : Fin (2 * m)) (hbc : b ≠ c) :
    (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ GG m r c = true)).card ≤ 2 := by
  calc _ ≤ (Finset.univ : Finset Bool).card := by
        apply Finset.card_le_card_of_injOn
          (fun r : Fin (2 * m) => if b.val % 2 = 1 ∧ c.val % 2 = 1 then decide (r.val / 2 = b.val / 2)
            else decide (r.val % 2 = 0))
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro r hr r' hr' h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr hr'
          dsimp only at h
          apply Fin.ext
          apply f3 m r.val r'.val b.val c.val hm r.isLt r'.isLt b.isLt c.isLt
            (fun e => hbc (Fin.ext e))
            ((GG_iff m hm r b).1 hr.1) ((GG_iff m hm r c).1 hr.2)
            ((GG_iff m hm r' b).1 hr'.1) ((GG_iff m hm r' c).1 hr'.2)
          · intro hp
            rw [ite_eq_left hp, ite_eq_left hp] at h
            exact decide_eq_decide.1 h
          · intro hp
            rw [ite_eq_right hp, ite_eq_right hp] at h
            exact decide_eq_decide.1 h
    _ = 2 := by simp

theorem row4 (m : ℕ) (hm : 5 ≤ m) (u : Fin (2 * m)) :
    (Finset.univ.filter (fun v : Fin (2 * m) => GG m u v = true)).card ≤ 4 := by
  calc _ ≤ (Finset.univ : Finset (Bool × Bool)).card := by
        apply Finset.card_le_card_of_injOn
          (fun v : Fin (2 * m) => (decide (v.val % 2 = 0), decide (u.val / 2 = v.val / 2)))
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro v hv v' hv' h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
          dsimp only at h
          have h1 := decide_eq_decide.1 (congrArg Prod.fst h)
          have h2 := decide_eq_decide.1 (congrArg Prod.snd h)
          exact Fin.ext (f4 m u.val v.val v'.val hm v.isLt v'.isLt
            ((GG_iff m hm u v).1 hv) ((GG_iff m hm u v').1 hv') h1 h2)
    _ = 4 := by simp

theorem coldist (m : ℕ) (hm : 5 ≤ m) (b c : Fin (2 * m)) (hbc : b ≠ c) :
    2 + 2 ≤ (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b ≠ GG m r c)).card := by
  have hb := col4 m hm b
  have hc := col4 m hm c
  have hbc2 := common2 m hm b c hbc
  have hcb2 := common2 m hm c b (Ne.symm hbc)
  have e1 : (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true)).card ≤
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ GG m r c = true)).card +
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ ¬ GG m r c = true)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    by_cases h : GG m r c = true
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr ⟨hr, h⟩
  have e2 : (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true)).card ≤
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ GG m r b = true)).card +
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ ¬ GG m r b = true)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    by_cases h : GG m r b = true
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr ⟨hr, h⟩
  have hdisj : Disjoint
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ ¬ GG m r c = true))
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ ¬ GG m r b = true)) := by
    rw [Finset.disjoint_filter]
    intro r _ h1 h2
    exact h2.2 h1.1
  have hsub : (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ ¬ GG m r c = true)) ∪
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ ¬ GG m r b = true)) ⊆
      Finset.univ.filter (fun r : Fin (2 * m) => GG m r b ≠ GG m r c) := by
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro h
      rw [h] at h1
      exact h2 h1
    · intro h
      rw [← h] at h1
      exact h2 h1
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h
  omega

def isKeptPair (m : ℕ) (C : Circuit) (L : Finset ℕ) (u v : Fin (2 * m)) : Prop :=
  readsIn C L u.val = 1 ∧
  readsIn C L (2 * m + v.val) = 1 ∧
  ∃ j ∈ L, (gateAt C j).op = GateOp.or ∧
    ((gateAt C j).inputs = [u.val, 2 * m + v.val] ∨
     (gateAt C j).inputs = [2 * m + v.val, u.val])

theorem keptPair_uniq_r (m : ℕ) (C : Circuit) (L : Finset ℕ) (u v1 v2 : Fin (2 * m))
    (h1 : isKeptPair m C L u v1) (h2 : isKeptPair m C L u v2) : v1 = v2 := by
  obtain ⟨ru, _, j1, hj1, _, hi1⟩ := h1
  obtain ⟨_, _, j2, hj2, _, hi2⟩ := h2
  have mu1 : u.val ∈ (gateAt C j1).inputs := by rcases hi1 with h | h <;> simp [h]
  have mu2 : u.val ∈ (gateAt C j2).inputs := by rcases hi2 with h | h <;> simp [h]
  have hjeq : j1 = j2 := uniq_idx_L C L u.val ru j2 hj2 mu2 j1 hj1 mu1
  subst hjeq
  have hu := u.isLt
  apply Fin.ext
  rcases hi1 with h1 | h1 <;> rcases hi2 with h2 | h2
  · rw [h1] at h2; injection h2 with _ htail; injection htail with hv; omega
  · rw [h1] at h2; injection h2 with hv; omega
  · rw [h1] at h2; injection h2 with hv; omega
  · rw [h1] at h2; injection h2 with hv; omega

theorem keptPair_uniq_l (m : ℕ) (C : Circuit) (L : Finset ℕ) (u1 u2 v : Fin (2 * m))
    (h1 : isKeptPair m C L u1 v) (h2 : isKeptPair m C L u2 v) : u1 = u2 := by
  obtain ⟨_, rv, j1, hj1, _, hi1⟩ := h1
  obtain ⟨_, _, j2, hj2, _, hi2⟩ := h2
  have mv1 : 2 * m + v.val ∈ (gateAt C j1).inputs := by rcases hi1 with h | h <;> simp [h]
  have mv2 : 2 * m + v.val ∈ (gateAt C j2).inputs := by rcases hi2 with h | h <;> simp [h]
  have hjeq : j1 = j2 := uniq_idx_L C L (2 * m + v.val) rv j2 hj2 mv2 j1 hj1 mv1
  subst hjeq
  have hu1 := u1.isLt
  have hu2 := u2.isLt
  apply Fin.ext
  rcases hi1 with h1 | h1 <;> rcases hi2 with h2 | h2
  · rw [h1] at h2; injection h2
  · rw [h1] at h2; injection h2 with hu; omega
  · rw [h1] at h2; injection h2 with hu; omega
  · rw [h1] at h2; injection h2 with _ htail; injection htail

theorem main_L (m : ℕ) (hm : 5 ≤ m) (C : Circuit) (L : Finset ℕ) (out_j : ℕ)
    (hLsub : ∀ j ∈ L, j < C.gates.length)
    (hLcl : ∀ j ∈ L, ∀ w ∈ (gateAt C j).inputs, 2 * m + 2 * m ≤ w → w - (2 * m + 2 * m) ∈ L)
    (hout_eq : C.output = 2 * m + 2 * m + out_j)
    (hout_mem : out_j ∈ L)
    (π : Equiv.Perm (Fin (2 * m)))
    (kept : Finset (Fin (2 * m)))
    (hkept : ∀ i ∈ kept, isKeptPair m C L i (π i))
    (hrb : ReadsBack (2 * m + 2 * m) C)
    (hrep : PEqualNP.Represents.Represents (GG m) C) :
    m ≤ 3 * (2 * m - kept.card) := by
  classical
  have hlen : ∀ a b : Fin (2 * m), (PEqualNP.Represents.oneEach a b).length = 2 * m + 2 * m := by
    intro a b
    simp [PEqualNP.Represents.oneEach]
  have hrb' := rb_idx C (2 * m + 2 * m) hrb
  have valT : ∀ (Z : List Bool) (_ : Z.length = 2 * m + 2 * m) (j : ℕ) (hj : j < C.gates.length)
      (_ : (C.gates[j]).op = GateOp.or) (w : ℕ) (_ : w ∈ (C.gates[j]).inputs)
      (_ : w < 2 * m + 2 * m) (_ : Z.getD w false = true),
      (W C.gates Z).getD (2 * m + 2 * m + j) false = true := by
    intro Z hZ j hj hor w hw hwN hZw
    have v := W_val C.gates Z j hj (by rw [hZ]; exact hrb' j hj)
    rw [hZ] at v
    rw [v, hor]
    exact or_true_of _ _ w hw (by rw [W_lt _ _ _ (by omega)]; exact hZw)
  have hsym : ∀ u ∈ kept, ∀ v ∈ kept, GG m u (π v) = GG m v (π u) := by
    intro u hu v hv
    by_cases huv : u = v
    · rw [huv]
    obtain ⟨ru, rcu, ju, hjuL, hgor, hginp⟩ := hkept u hu
    obtain ⟨rv, rcv, jv, hjvL, hgvor, hgvinp⟩ := hkept v hv
    have hju : ju < C.gates.length := hLsub ju hjuL
    have hjv : jv < C.gates.length := hLsub jv hjvL
    have hgor' : (C.gates[ju]).op = GateOp.or := by rwa [← gateAt_eq C ju hju]
    have hgvor' : (C.gates[jv]).op = GateOp.or := by rwa [← gateAt_eq C jv hjv]
    have hu2 := u.isLt
    have hv2 := v.isLt
    have hpu2 := (π u).isLt
    have hpv2 := (π v).isLt
    have hXl := hlen u (π v)
    have hYl := hlen v (π u)
    have hX : ∀ i, (PEqualNP.Represents.oneEach u (π v)).getD i false =
        (decide (i = u.val) || decide (i = 2 * m + (π v).val)) := oneEach_getD u (π v)
    have hY : ∀ i, (PEqualNP.Represents.oneEach v (π u)).getD i false =
        (decide (i = v.val) || decide (i = 2 * m + (π u).val)) := oneEach_getD v (π u)
    have hin : ∀ i, ¬ (i = u.val ∨ i = v.val ∨ i = 2 * m + (π u).val ∨ i = 2 * m + (π v).val) →
        (PEqualNP.Represents.oneEach u (π v)).getD i false =
          (PEqualNP.Represents.oneEach v (π u)).getD i false := by
      intro i hi
      simp only [not_or] at hi
      rw [hX, hY]
      simp [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
    have mu1 : u.val ∈ (gateAt C ju).inputs := by rcases hginp with h | h <;> rw [h] <;> simp
    have mu2 : 2 * m + (π u).val ∈ (gateAt C ju).inputs := by rcases hginp with h | h <;> rw [h] <;> simp
    have mv1 : v.val ∈ (gateAt C jv).inputs := by rcases hgvinp with h | h <;> rw [h] <;> simp
    have mv2 : 2 * m + (π v).val ∈ (gateAt C jv).inputs := by rcases hgvinp with h | h <;> rw [h] <;> simp
    have mu1' : u.val ∈ (C.gates[ju]).inputs := by rwa [← gateAt_eq C ju hju]
    have mu2' : 2 * m + (π u).val ∈ (C.gates[ju]).inputs := by rwa [← gateAt_eq C ju hju]
    have mv1' : v.val ∈ (C.gates[jv]).inputs := by rwa [← gateAt_eq C jv hjv]
    have mv2' : 2 * m + (π v).val ∈ (C.gates[jv]).inputs := by rwa [← gateAt_eq C jv hjv]
    have hXu : (PEqualNP.Represents.oneEach u (π v)).getD u.val false = true := by rw [hX]; simp
    have hXv : (PEqualNP.Represents.oneEach u (π v)).getD (2 * m + (π v).val) false = true := by
      rw [hX]; simp
    have hYv : (PEqualNP.Represents.oneEach v (π u)).getD v.val false = true := by rw [hY]; simp
    have hYu : (PEqualNP.Represents.oneEach v (π u)).getD (2 * m + (π u).val) false = true := by
      rw [hY]; simp
    have gU : (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD (2 * m + 2 * m + ju) false =
        (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD (2 * m + 2 * m + ju) false := by
      rw [valT _ hXl ju hju hgor' u.val mu1' (by omega) hXu,
        valT _ hYl ju hju hgor' (2 * m + (π u).val) mu2' (by omega) hYu]
    have gV : (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD (2 * m + 2 * m + jv) false =
        (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD (2 * m + 2 * m + jv) false := by
      rw [valT _ hXl jv hjv hgvor' (2 * m + (π v).val) mv2' (by omega) hXv,
        valT _ hYl jv hjv hgvor' v.val mv1' (by omega) hYv]
    have hg : ∀ j ∈ L,
        (∃ i ∈ (gateAt C j).inputs,
          (i = u.val ∨ i = v.val ∨ i = 2 * m + (π u).val ∨ i = 2 * m + (π v).val)) →
        (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD (2 * m + 2 * m + j) false =
          (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD (2 * m + 2 * m + j) false := by
      intro j hjL ⟨i, hi, hb⟩
      rcases hb with h | h | h | h
      · rw [h] at hi
        rw [uniq_idx_L C L _ ru ju hjuL mu1 j hjL hi]; exact gU
      · rw [h] at hi
        rw [uniq_idx_L C L _ rv jv hjvL mv1 j hjL hi]; exact gV
      · rw [h] at hi
        rw [uniq_idx_L C L _ rcu ju hjuL mu2 j hjL hi]; exact gU
      · rw [h] at hi
        rw [uniq_idx_L C L _ rcv jv hjvL mv2 j hjL hi]; exact gV
    have core := core2_L (2 * m + 2 * m) _ _ hXl hYl
      (fun i => i = u.val ∨ i = v.val ∨ i = 2 * m + (π u).val ∨ i = 2 * m + (π v).val)
      hin C L hLsub hLcl hrb' hg
    have eX : GG m u (π v) =
        (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD C.output false := by
      rw [← hrep u (π v)]; rfl
    have eY : GG m v (π u) =
        (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD C.output false := by
      rw [← hrep v (π u)]; rfl
    rw [eX, eY]
    apply core C.output
    · exact Or.inr ⟨by omega, by rw [hout_eq, Nat.add_sub_cancel_left]; exact hout_mem⟩
    · omega
  have hs := sq (2 * m) m 2 2 (GG m) (rp m) π kept (rowdist m hm) (coldist m hm) hsym
  have hsum : ∑ u ∈ Finset.univ \ kept,
      min (Finset.univ.filter (fun onCol : Fin (2 * m) => GG m u onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin (2 * m) => GG m u offCol = false)).card ≤
      4 * (2 * m - kept.card) := by
    calc _ ≤ ∑ _u ∈ Finset.univ \ kept, 4 :=
          Finset.sum_le_sum (fun u _ => (min_le_left _ _).trans (row4 m hm u))
      _ = 4 * (2 * m - kept.card) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_sdiff_of_subset (Finset.subset_univ kept),
            Finset.card_univ, Fintype.card_fin, mul_comm]
  omega

def isPrivCrossAnd (m : ℕ) (C : Circuit) (L : Finset ℕ) (j : ℕ) : Prop :=
  j ∈ L ∧ (gateAt C j).op = GateOp.and ∧
  ∃ u v : Fin (2 * m),
    readsIn C L u.val = 1 ∧ readsIn C L (2 * m + v.val) = 1 ∧
    ((gateAt C j).inputs = [u.val, 2 * m + v.val] ∨
     (gateAt C j).inputs = [2 * m + v.val, u.val])

theorem full_proof (m : ℕ) (hm : 5 ≤ m) (C : Circuit)
    (hfan : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hrb : ReadsBack (2 * m + 2 * m) C)
    (hrep : PEqualNP.Represents.Represents (GG m) C) :
    38 * m ≤ 9 * C.size + 3 * (C.gates.filter (fun gate =>
      gate.inputs.length == 2 &&
      (gate.inputs.filter (fun w => w < 2 * m + 2 * m)).length == 1)).length + 39 := by
  classical
  let N := 2 * m + 2 * m
  have hlen : ∀ a b : Fin (2 * m), (PEqualNP.Represents.oneEach a b).length = N := by
    intro a b; simp [N, PEqualNP.Represents.oneEach]
  have hrb' := rb_idx C N hrb
  have hout_ge : N ≤ C.output := by
    by_contra hlt
    push_neg at hlt
    by_cases h1 : C.output < 2 * m
    · let w : Fin (2 * m) := ⟨C.output, h1⟩
      obtain ⟨c, hc, hnP⟩ := f5 m w.val hm w.isLt
      have hr := hrep w ⟨c, hc⟩
      have ev : C.eval (PEqualNP.Represents.oneEach w (⟨c, hc⟩ : Fin (2 * m))) = true := by
        rw [eval_eq, W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]; simp [w]
      rw [ev] at hr
      exact hnP ((GG_iff m hm w ⟨c, hc⟩).1 hr.symm)
    · let w : Fin (2 * m) := ⟨C.output - 2 * m, by omega⟩
      obtain ⟨r, hr0, hnP⟩ := f6 m w.val hm w.isLt
      have hr := hrep ⟨r, hr0⟩ w
      have ev : C.eval (PEqualNP.Represents.oneEach (⟨r, hr0⟩ : Fin (2 * m)) w) = true := by
        rw [eval_eq, W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]
        have heq : C.output = 2 * m + w.val := by dsimp [w]; omega
        simp [heq]
      rw [ev] at hr
      exact hnP ((GG_iff m hm ⟨r, hr0⟩ w).1 hr.symm)
  have hout_lt : C.output < N + C.gates.length := by
    by_contra hge
    push_neg at hge
    let z : Fin (2 * m) := ⟨0, by omega⟩
    have hr := hrep z z
    have ev : C.eval (PEqualNP.Represents.oneEach z z) = false := by
      rw [eval_eq, getD_big _ _ (by rw [W_len, hlen]; omega)]
    have hg : GG m z z = true := (GG_iff m hm z z).2 (Or.inl rfl)
    rw [ev, hg] at hr
    exact Bool.false_ne_true hr
  let out_j := C.output - N
  have hout_eq : C.output = N + out_j := by dsimp [out_j]; omega
  have hout_j_lt : out_j < C.gates.length := by dsimp [out_j]; omega
  let L : Finset ℕ := reachBack C N (out_j + 1) {out_j}
  have hout_mem : out_j ∈ L := subset_reachBack C N (out_j + 1) {out_j} (Finset.mem_singleton_self out_j)
  have hL_lt_out : ∀ j ∈ L, j < out_j + 1 :=
    reachBack_lt C N (out_j + 1) (out_j + 1) {out_j} (by intro x hx; simp at hx; omega) (le_refl _)
  have hLsub : ∀ j ∈ L, j < C.gates.length := fun j hj => by have := hL_lt_out j hj; omega
  have hLsub_range : L ⊆ Finset.range C.gates.length := fun j hj => Finset.mem_range.mpr (hLsub j hj)
  have hLcard_le : L.card ≤ C.size := by
    have := Finset.card_le_card hLsub_range
    simpa [Circuit.size] using this
  have hLcl : ∀ j ∈ L, ∀ w ∈ (gateAt C j).inputs, N ≤ w → w - N ∈ L := by
    intro j hj w hw hN
    have hlt : w < N + j := hrb j (hLsub j hj) w hw
    exact reachBack_closed C N (out_j + 1) {out_j} j hj (hL_lt_out j hj) w hw hN hlt
  have hLpar : ∀ x ∈ L, x = out_j ∨ ∃ p ∈ L, N + x ∈ (gateAt C p).inputs :=
    reachBack_parent C N (out_j + 1) out_j {out_j} (by intro x hx; simp at hx; exact Or.inl hx)
  let r := readsIn C L
  let kept : Finset (Fin (2 * m)) := Finset.univ.filter (fun u => ∃ v, isKeptPair m C L u v)
  let keptC : Finset (Fin (2 * m)) := Finset.univ.filter (fun v => ∃ u, isKeptPair m C L u v)
  have hkept_equiv : ∃ e1 : {u : Fin (2 * m) // u ∈ kept} ≃ {v : Fin (2 * m) // v ∈ keptC},
      ∀ u : {u : Fin (2 * m) // u ∈ kept}, isKeptPair m C L u.val (e1 u).val := by
    have hEx : ∀ u : {u : Fin (2 * m) // u ∈ kept}, ∃ v : Fin (2 * m), isKeptPair m C L u.val v := by
      intro ⟨u, hu⟩
      simp only [kept, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact hu
    let f : {u : Fin (2 * m) // u ∈ kept} → {v : Fin (2 * m) // v ∈ keptC} :=
      fun u => ⟨Classical.choose (hEx u), by
        simp only [keptC, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u.val, Classical.choose_spec (hEx u)⟩⟩
    have hf_spec : ∀ u, isKeptPair m C L u.val (f u).val := fun u => Classical.choose_spec (hEx u)
    have hf_bij : Function.Bijective f := by
      constructor
      · intro u1 u2 h
        have hv : (f u1).val = (f u2).val := congrArg Subtype.val h
        apply Subtype.ext
        exact keptPair_uniq_l m C L u1.val u2.val (f u1).val (hf_spec u1) (hv ▸ hf_spec u2)
      · intro ⟨v, hv⟩
        simp only [keptC, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨u, huv⟩ := hv
        have hu : u ∈ kept := by
          simp only [kept, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, huv⟩
        refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
        exact keptPair_uniq_r m C L u (f ⟨u, hu⟩).val v (hf_spec ⟨u, hu⟩) huv
    exact ⟨Equiv.ofBijective f hf_bij, fun u => hf_spec u⟩
  obtain ⟨e1, he1⟩ := hkept_equiv
  have hcard_kept : kept.card = keptC.card := by
    have h := Fintype.card_congr e1
    simpa [Fintype.card_coe] using h
  have hcomp_card : Fintype.card {u : Fin (2 * m) // u ∉ kept} =
      Fintype.card {v : Fin (2 * m) // v ∉ keptC} := by
    have h1 : Fintype.card {u : Fin (2 * m) // u ∉ kept} = (Finset.univ \ kept).card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact { toFun := fun ⟨u, hu⟩ => ⟨u, by simp [hu]⟩
              invFun := fun ⟨u, hu⟩ => ⟨u, by simp at hu; exact hu⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
    have h2 : Fintype.card {v : Fin (2 * m) // v ∉ keptC} = (Finset.univ \ keptC).card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact { toFun := fun ⟨v, hv⟩ => ⟨v, by simp [hv]⟩
              invFun := fun ⟨v, hv⟩ => ⟨v, by simp at hv; exact hv⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
    rw [h1, h2, Finset.card_sdiff_of_subset (Finset.subset_univ kept),
      Finset.card_sdiff_of_subset (Finset.subset_univ keptC), hcard_kept]
  obtain ⟨e2⟩ := Fintype.card_eq.mp hcomp_card
  let π : Equiv.Perm (Fin (2 * m)) :=
    { toFun := fun u => if h : u ∈ kept then (e1 ⟨u, h⟩).val else (e2 ⟨u, h⟩).val
      invFun := fun v => if h : v ∈ keptC then (e1.symm ⟨v, h⟩).val else (e2.symm ⟨v, h⟩).val
      left_inv := by
        intro u
        by_cases h : u ∈ kept
        · simp only [h, ↓reduceDIte]
          have hmem : (e1 ⟨u, h⟩).val ∈ keptC := (e1 ⟨u, h⟩).property
          simp only [hmem, ↓reduceDIte]
          have := e1.symm_apply_apply ⟨u, h⟩
          exact congrArg Subtype.val this
        · simp only [h, ↓reduceDIte]
          have hmem : (e2 ⟨u, h⟩).val ∉ keptC := (e2 ⟨u, h⟩).property
          simp only [hmem, ↓reduceDIte]
          have := e2.symm_apply_apply ⟨u, h⟩
          exact congrArg Subtype.val this
      right_inv := by
        intro v
        by_cases h : v ∈ keptC
        · simp only [h, ↓reduceDIte]
          have hmem : (e1.symm ⟨v, h⟩).val ∈ kept := (e1.symm ⟨v, h⟩).property
          simp only [hmem, ↓reduceDIte]
          have := e1.apply_symm_apply ⟨v, h⟩
          exact congrArg Subtype.val this
        · simp only [h, ↓reduceDIte]
          have hmem : (e2.symm ⟨v, h⟩).val ∉ kept := (e2.symm ⟨v, h⟩).property
          simp only [hmem, ↓reduceDIte]
          have := e2.apply_symm_apply ⟨v, h⟩
          exact congrArg Subtype.val this }
  have hπ_kept : ∀ u ∈ kept, isKeptPair m C L u (π u) := by
    intro u hu
    have hπu : π u = (e1 ⟨u, hu⟩).val := by simp [π, hu]
    rw [hπu]
    exact he1 ⟨u, hu⟩
  have hIneq1 : m ≤ 3 * (2 * m - kept.card) :=
    main_L m hm C L out_j hLsub hLcl hout_eq hout_mem π kept hπ_kept hrb hrep
  let S0 : Finset ℕ := (Finset.range N).filter (fun w => r w = 0)
  have hS0_row : ((Finset.range (2 * m)).filter (fun w => r w = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    by_contra hne
    simp only [Finset.mem_filter, Finset.mem_range] at hw1 hw2
    let u1 : Fin (2 * m) := ⟨w1, hw1.1⟩
    let u2 : Fin (2 * m) := ⟨w2, hw2.1⟩
    obtain ⟨v, hdiff⟩ := row_ne m hm u1 u2 (fun h => hne (congrArg Fin.val h))
    have hcore := core2_L N (PEqualNP.Represents.oneEach u1 v) (PEqualNP.Represents.oneEach u2 v)
      (hlen u1 v) (hlen u2 v) (fun i => i = w1 ∨ i = w2)
      (by
        intro i hi
        simp only [not_or] at hi
        rw [oneEach_getD, oneEach_getD]
        simp [u1, u2, hi.1, hi.2])
      C L hLsub hLcl hrb'
      (by
        intro j hj ⟨i, hi, hb⟩
        exfalso
        rcases hb with h | h
        · rw [h] at hi
          have c := count_le_readsIn C L w1 j hj
          have cp : 0 < (gateAt C j).inputs.count w1 := List.count_pos_iff.mpr hi
          have h0 : readsIn C L w1 = 0 := hw1.2
          omega
        · rw [h] at hi
          have c := count_le_readsIn C L w2 j hj
          have cp : 0 < (gateAt C j).inputs.count w2 := List.count_pos_iff.mpr hi
          have h0 : readsIn C L w2 = 0 := hw2.2
          omega)
      C.output
      (Or.inr ⟨hout_ge, by rw [hout_eq, Nat.add_sub_cancel_left]; exact hout_mem⟩)
      (by omega)
    have e1' : GG m u1 v = (W C.gates (PEqualNP.Represents.oneEach u1 v)).getD C.output false := by
      rw [← hrep u1 v]; rfl
    have e2' : GG m u2 v = (W C.gates (PEqualNP.Represents.oneEach u2 v)).getD C.output false := by
      rw [← hrep u2 v]; rfl
    exact hdiff (by rw [e1', e2', hcore])
  have hS0_col : ((Finset.Ico (2 * m) N).filter (fun w => r w = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    by_contra hne
    simp only [Finset.mem_filter, Finset.mem_Ico] at hw1 hw2
    let v1 : Fin (2 * m) := ⟨w1 - 2 * m, by omega⟩
    let v2 : Fin (2 * m) := ⟨w2 - 2 * m, by omega⟩
    have hvne : v1 ≠ v2 := fun h => hne (by have := congrArg Fin.val h; dsimp [v1, v2] at this; omega)
    have hcd := coldist m hm v1 v2 hvne
    have hempty : Finset.univ.filter (fun u : Fin (2 * m) => GG m u v1 ≠ GG m u v2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro u _
      push Not
      have hcore := core2_L N (PEqualNP.Represents.oneEach u v1) (PEqualNP.Represents.oneEach u v2)
        (hlen u v1) (hlen u v2) (fun i => i = w1 ∨ i = w2)
        (by
          intro i hi
          simp only [not_or] at hi
          rw [oneEach_getD, oneEach_getD]
          have e1' : 2 * m + v1.val = w1 := by dsimp [v1]; omega
          have e2' : 2 * m + v2.val = w2 := by dsimp [v2]; omega
          rw [e1', e2']
          simp [hi.1, hi.2])
        C L hLsub hLcl hrb'
        (by
          intro j hj ⟨i, hi, hb⟩
          exfalso
          rcases hb with h | h
          · rw [h] at hi
            have c := count_le_readsIn C L w1 j hj
            have cp : 0 < (gateAt C j).inputs.count w1 := List.count_pos_iff.mpr hi
            have h0 : readsIn C L w1 = 0 := hw1.2
            omega
          · rw [h] at hi
            have c := count_le_readsIn C L w2 j hj
            have cp : 0 < (gateAt C j).inputs.count w2 := List.count_pos_iff.mpr hi
            have h0 : readsIn C L w2 = 0 := hw2.2
            omega)
        C.output
        (Or.inr ⟨hout_ge, by rw [hout_eq, Nat.add_sub_cancel_left]; exact hout_mem⟩)
        (by omega)
      have e1' : GG m u v1 = (W C.gates (PEqualNP.Represents.oneEach u v1)).getD C.output false := by
        rw [← hrep u v1]; rfl
      have e2' : GG m u v2 = (W C.gates (PEqualNP.Represents.oneEach u v2)).getD C.output false := by
        rw [← hrep u v2]; rfl
      rw [e1', e2', hcore]
    rw [hempty] at hcd
    simp at hcd
  have hS0_le : S0.card ≤ 2 := by
    have hsub : S0 ⊆ ((Finset.range (2 * m)).filter (fun w => r w = 0)) ∪
        ((Finset.Ico (2 * m) N).filter (fun w => r w = 0)) := by
      intro w hw
      simp only [S0, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hw ⊢
      by_cases h : w < 2 * m
      · exact Or.inl ⟨h, hw.2⟩
      · exact Or.inr ⟨⟨by omega, hw.1⟩, hw.2⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  let E : ℕ := ∑ w ∈ Finset.range N, (r w - 1)
  let L_not : Finset ℕ := L.filter (fun j => (gateAt C j).op = GateOp.not)
  let T : ℕ := L_not.card
  have hRaw_eq : N + E = (∑ w ∈ Finset.range N, r w) + S0.card := by
    have hpt : ∀ w ∈ Finset.range N, 1 + (r w - 1) = r w + (if r w = 0 then 1 else 0) := by
      intro w _
      split_ifs with h <;> omega
    have hsum := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have h1 : (∑ _w ∈ Finset.range N, 1) = N := by simp
    have h2 : (∑ w ∈ Finset.range N, if r w = 0 then 1 else 0) = S0.card := by
      dsimp only [S0]; rw [Finset.card_filter]
    rw [h1, h2] at hsum
    exact hsum
  have hInputs_T : (∑ j ∈ L, (gateAt C j).inputs.length) + T = 2 * L.card := by
    have hpt : ∀ j ∈ L, (gateAt C j).inputs.length + (if (gateAt C j).op = GateOp.not then 1 else 0) = 2 := by
      intro j hj
      have hjl : j < C.gates.length := hLsub j hj
      have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt_eq C j hjl]
        exact List.getElem_mem hjl
      rcases hfan (gateAt C j) hmem with ⟨hop, hlen2⟩ | ⟨hop, hlen1⟩
      · have hne : (gateAt C j).op ≠ GateOp.not := by
          rcases hop with h | h <;> rw [h] <;> intro hc <;> cases hc
        simp [hne, hlen2]
      · simp [hop, hlen1]
    have hsum := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib] at hsum
    have h1 : (∑ j ∈ L, if (gateAt C j).op = GateOp.not then 1 else 0) = T := by
      dsimp only [T, L_not]; rw [Finset.card_filter]
    have h2 : (∑ _j ∈ L, 2) = 2 * L.card := by simp [mul_comm]
    rw [h1, h2] at hsum
    exact hsum
  have hInputs_split : (∑ j ∈ L, (gateAt C j).inputs.length) =
      (∑ w ∈ Finset.range N, r w) + (∑ k ∈ L, r (N + k)) := by
    let Wset : Finset ℕ := Finset.range N ∪ L.image (fun k => N + k)
    have hdisj : Disjoint (Finset.range N) (L.image (fun k => N + k)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_range] at hw1
      simp only [Finset.mem_image] at hw2
      obtain ⟨k, _, rfl⟩ := hw2
      omega
    have hlen_sum : ∀ j ∈ L, (gateAt C j).inputs.length =
        ∑ w ∈ Wset, (gateAt C j).inputs.count w := by
      intro j hj
      apply list_len_eq_sum_count
      intro w hw
      simp only [Wset, Finset.mem_union, Finset.mem_range, Finset.mem_image]
      by_cases hwN : w < N
      · exact Or.inl hwN
      · refine Or.inr ⟨w - N, hLcl j hj w hw (by omega), by omega⟩
    calc ∑ j ∈ L, (gateAt C j).inputs.length
        = ∑ j ∈ L, ∑ w ∈ Wset, (gateAt C j).inputs.count w := Finset.sum_congr rfl hlen_sum
      _ = ∑ w ∈ Wset, ∑ j ∈ L, (gateAt C j).inputs.count w := Finset.sum_comm
      _ = ∑ w ∈ Wset, r w := rfl
      _ = (∑ w ∈ Finset.range N, r w) + (∑ w ∈ L.image (fun k => N + k), r w) :=
            Finset.sum_union hdisj
      _ = (∑ w ∈ Finset.range N, r w) + (∑ k ∈ L, r (N + k)) := by
            congr 1
            rw [Finset.sum_image]
            intro a _ b _ h; dsimp only at h; omega
  have hGate_ge : L.card ≤ (∑ k ∈ L, r (N + k)) + 1 := by
    have hsub_le : ∑ k ∈ L.erase out_j, r (N + k) ≤ ∑ k ∈ L, r (N + k) :=
      Finset.sum_le_sum_of_subset (Finset.erase_subset out_j L)
    have hone : (L.erase out_j).card ≤ ∑ k ∈ L.erase out_j, r (N + k) := by
      calc (L.erase out_j).card = ∑ _k ∈ L.erase out_j, 1 := by simp
        _ ≤ ∑ k ∈ L.erase out_j, r (N + k) := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_erase] at hk
          rcases hLpar k hk.2 with h | ⟨p, hp, hwp⟩
          · exact absurd h hk.1
          · have cp : 0 < (gateAt C p).inputs.count (N + k) := List.count_pos_iff.mpr hwp
            have cl := count_le_readsIn C L (N + k) p hp
            change (gateAt C p).inputs.count (N + k) ≤ r (N + k) at cl
            omega
    have herase : (L.erase out_j).card + 1 = L.card := by
      rw [Finset.card_erase_of_mem hout_mem]
      have hpos : 0 < L.card := Finset.card_pos.mpr ⟨out_j, hout_mem⟩
      omega
    omega
  have hIneq2 : N + E + T ≤ C.size + 3 := by omega
  let isMixGate : Gate → Bool := fun gate =>
    gate.inputs.length == 2 && (gate.inputs.filter (fun w => w < N)).length == 1
  let L_mix : Finset ℕ := L.filter (fun j => isMixGate (gateAt C j) = true)
  let M : ℕ := L_mix.card
  have hM_le : M ≤ (C.gates.filter isMixGate).length := by
    calc M = L_mix.card := rfl
      _ ≤ ((Finset.range C.gates.length).filter (fun j => isMixGate (gateAt C j) = true)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [L_mix, Finset.mem_filter, Finset.mem_range] at hj ⊢
        exact ⟨hLsub j hj.1, hj.2⟩
      _ = (C.gates.filter isMixGate).length := range_filter_eq_list_filter C.gates isMixGate
  let ownedR : Finset ℕ := kept.image (fun u : Fin (2 * m) => u.val)
  let ownedC : Finset ℕ := keptC.image (fun v : Fin (2 * m) => 2 * m + v.val)
  let owned : Finset ℕ := ownedR ∪ ownedC
  have howned_sub : owned ⊆ Finset.range N := by
    intro w hw
    simp only [owned, ownedR, ownedC, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hw ⊢
    rcases hw with ⟨u, _, rfl⟩ | ⟨v, _, rfl⟩
    · have := u.isLt; omega
    · have := v.isLt; omega
  have howned_disj : Disjoint ownedR ownedC := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [ownedR, ownedC, Finset.mem_image] at hw1 hw2
    obtain ⟨u, _, rfl⟩ := hw1
    obtain ⟨v, _, hv⟩ := hw2
    have := u.isLt; omega
  have howned_card : owned.card = 2 * kept.card := by
    rw [Finset.card_union_of_disjoint howned_disj]
    have hR : ownedR.card = kept.card := by
      apply Finset.card_image_of_injective; intro a b h; exact Fin.ext h
    have hC : ownedC.card = keptC.card := by
      apply Finset.card_image_of_injective; intro a b h; dsimp only at h; exact Fin.ext (by omega)
    omega
  let S : Finset ℕ := Finset.range N \ owned
  have hS_card : S.card = 2 * (2 * m - kept.card) := by
    rw [Finset.card_sdiff_of_subset howned_sub, Finset.card_range, howned_card]
    have hk : kept.card ≤ 2 * m := by
      calc kept.card ≤ (Finset.univ : Finset (Fin (2 * m))).card := Finset.card_le_univ kept
        _ = 2 * m := by simp
    omega
  let S0' : Finset ℕ := S.filter (fun w => r w = 0)
  let S2_all : Finset ℕ := (Finset.range N).filter (fun w => 2 ≤ r w)
  let S2 : Finset ℕ := S.filter (fun w => 2 ≤ r w)
  let S1 : Finset ℕ := S.filter (fun w => r w = 1)
  have hS0'_le : S0'.card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) hS0_le
    intro w hw
    simp only [S0', S0, S, Finset.mem_filter, Finset.mem_sdiff] at hw ⊢
    exact ⟨hw.1.1, hw.2⟩
  have hS2_all_le : S2_all.card ≤ E := by
    have hsub : S2_all ⊆ Finset.range N := Finset.filter_subset _ _
    calc S2_all.card = ∑ _w ∈ S2_all, 1 := by simp
      _ ≤ ∑ w ∈ S2_all, (r w - 1) := by
        apply Finset.sum_le_sum
        intro w hw
        simp only [S2_all, Finset.mem_filter] at hw
        omega
      _ ≤ ∑ w ∈ Finset.range N, (r w - 1) := Finset.sum_le_sum_of_subset hsub
  have hS2_sum : ∑ w ∈ S2_all, r w ≤ S2_all.card + E := by
    have hsub : S2_all ⊆ Finset.range N := Finset.filter_subset _ _
    have hpt : ∀ w ∈ S2_all, r w = 1 + (r w - 1) := by
      intro w hw
      simp only [S2_all, Finset.mem_filter] at hw
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    have h1 : (∑ _w ∈ S2_all, 1) = S2_all.card := by simp
    rw [h1]
    exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset hsub) _
  have hS2_le : S2.card ≤ S2_all.card := by
    apply Finset.card_le_card
    intro w hw
    simp only [S2, S2_all, S, Finset.mem_filter, Finset.mem_sdiff] at hw ⊢
    exact ⟨hw.1.1, hw.2⟩
  let owner : ℕ → ℕ := fun w =>
    if h : ∃ j ∈ L, w ∈ (gateAt C j).inputs then Classical.choose h else 0
  have howner_spec : ∀ w ∈ S1, owner w ∈ L ∧ w ∈ (gateAt C (owner w)).inputs := by
    intro w hw
    simp only [S1, Finset.mem_filter] at hw
    have hex : ∃ j ∈ L, w ∈ (gateAt C j).inputs :=
      exists_mem_of_readsIn_pos C L w (by change 0 < r w; omega)
    dsimp only [owner]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  let S1_not : Finset ℕ := S1.filter (fun w => (gateAt C (owner w)).op = GateOp.not)
  let S1_mix : Finset ℕ := S1.filter (fun w => isMixGate (gateAt C (owner w)) = true)
  let S1_hit2 : Finset ℕ := S1.filter (fun w =>
    (gateAt C (owner w)).inputs.length = 2 ∧
    ∃ w' ∈ (gateAt C (owner w)).inputs, w' < N ∧ 2 ≤ r w')
  let S1_pair : Finset ℕ := S1.filter (fun w => isPrivCrossAnd m C L (owner w))
  have hS1_not_le : S1_not.card ≤ T := by
    apply Finset.card_le_card_of_injOn owner
    · intro w hw
      simp only [S1_not, L_not, Finset.mem_coe, Finset.mem_filter] at hw ⊢
      exact ⟨(howner_spec w hw.1).1, hw.2⟩
    · intro w1 hw1 w2 hw2 heq
      simp only [S1_not, Finset.mem_coe, Finset.mem_filter] at hw1 hw2
      have h1 := howner_spec w1 hw1.1
      have h2 := howner_spec w2 hw2.1
      rw [heq] at h1
      have hjl := hLsub (owner w2) h2.1
      have hmem : gateAt C (owner w2) ∈ C.gates := by
        rw [gateAt_eq C _ hjl]; exact List.getElem_mem hjl
      have hl1 : (gateAt C (owner w2)).inputs.length = 1 := by
        rcases hfan _ hmem with ⟨hop, _⟩ | ⟨_, hl⟩
        · exfalso; rcases hop with h | h <;> rw [hw2.2] at h <;> cases h
        · exact hl
      exact list_len1_uniq _ hl1 w1 w2 h1.2 h2.2
  have hS1_mix_le : S1_mix.card ≤ M := by
    apply Finset.card_le_card_of_injOn owner
    · intro w hw
      simp only [S1_mix, L_mix, Finset.mem_coe, Finset.mem_filter] at hw ⊢
      exact ⟨(howner_spec w hw.1).1, hw.2⟩
    · intro w1 hw1 w2 hw2 heq
      simp only [S1_mix, S1, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_range] at hw1 hw2
      have h1 := howner_spec w1 (by simp [S1, S, hw1.1.1.1, hw1.1.1.2, hw1.1.2])
      have h2 := howner_spec w2 (by simp [S1, S, hw2.1.1.1, hw2.1.1.2, hw2.1.2])
      rw [heq] at h1
      have hm2 := hw2.2
      simp only [isMixGate, Bool.and_eq_true, beq_iff_eq] at hm2
      have hf1 : w1 ∈ (gateAt C (owner w2)).inputs.filter (fun w => w < N) := by
        simp [h1.2, hw1.1.1.1]
      have hf2 : w2 ∈ (gateAt C (owner w2)).inputs.filter (fun w => w < N) := by
        simp [h2.2, hw2.1.1.1]
      exact list_len1_uniq _ hm2.2 w1 w2 hf1 hf2
  have hS1_hit2_inj : Set.InjOn owner (S1_hit2 : Set ℕ) := by
    intro w1 hw1 w2 hw2 heq
    simp only [S1_hit2, S1, Finset.mem_coe, Finset.mem_filter] at hw1 hw2
    by_contra hne
    have h1 := howner_spec w1 (by simp [S1, hw1.1.1, hw1.1.2])
    have h2 := howner_spec w2 (by simp [S1, hw2.1.1, hw2.1.2])
    rw [heq] at h1
    obtain ⟨w', hw'mem, _, hw'r⟩ := hw1.2.2
    rw [heq] at hw'mem
    have hlen2 : (gateAt C (owner w2)).inputs.length = 2 := hw2.2.1
    obtain ⟨z, hz⟩ := list_len2_mem _ hlen2 w1 h1.2
    rcases hz with hz | hz
    · have h2' := h2.2
      rw [hz] at h2' hw'mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2' hw'mem
      have hzw2 : w2 = z := by rcases h2' with h | h; exact absurd h.symm hne; exact h
      subst hzw2
      rcases hw'mem with rfl | rfl
      · omega
      · omega
    · have h2' := h2.2
      rw [hz] at h2' hw'mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2' hw'mem
      have hzw2 : w2 = z := by rcases h2' with h | h; exact h; exact absurd h.symm hne
      subst hzw2
      rcases hw'mem with rfl | rfl
      · omega
      · omega
  have hS1_hit2_le : S1_hit2.card ≤ S2_all.card + E := by
    have himg_sub : S1_hit2.image owner ⊆ L := by
      intro j hj
      simp only [Finset.mem_image] at hj
      obtain ⟨w, hw, rfl⟩ := hj
      simp only [S1_hit2, Finset.mem_filter] at hw
      exact (howner_spec w hw.1).1
    calc S1_hit2.card = (S1_hit2.image owner).card := (Finset.card_image_of_injOn hS1_hit2_inj).symm
      _ = ∑ _j ∈ S1_hit2.image owner, 1 := by simp
      _ ≤ ∑ j ∈ S1_hit2.image owner, ∑ x ∈ S2_all, (gateAt C j).inputs.count x := by
        apply Finset.sum_le_sum
        intro j hj
        simp only [Finset.mem_image] at hj
        obtain ⟨w, hw, rfl⟩ := hj
        simp only [S1_hit2, Finset.mem_filter] at hw
        obtain ⟨w', hw'mem, hw'lt, hw'r⟩ := hw.2.2
        have hw'S2 : w' ∈ S2_all := by
          simp only [S2_all, Finset.mem_filter, Finset.mem_range]
          exact ⟨hw'lt, hw'r⟩
        have hpos : 1 ≤ (gateAt C (owner w)).inputs.count w' :=
          List.count_pos_iff.mpr hw'mem
        exact le_trans hpos (Finset.single_le_sum
          (f := fun x => (gateAt C (owner w)).inputs.count x) (fun _ _ => Nat.zero_le _) hw'S2)
      _ ≤ ∑ j ∈ L, ∑ x ∈ S2_all, (gateAt C j).inputs.count x :=
        Finset.sum_le_sum_of_subset himg_sub
      _ = ∑ x ∈ S2_all, ∑ j ∈ L, (gateAt C j).inputs.count x := Finset.sum_comm
      _ = ∑ x ∈ S2_all, r x := rfl
      _ ≤ S2_all.card + E := hS2_sum
  have hPrivCross_uniq : ∀ j1 j2, isPrivCrossAnd m C L j1 → isPrivCrossAnd m C L j2 → j1 = j2 := by
    intro j1 j2 h1 h2
    by_contra hne
    obtain ⟨hj1L, hop1, u1, v1, _, rv1, hi1⟩ := h1
    obtain ⟨hj2L, hop2, u2, v2, _, rv2, hi2⟩ := h2
    have mv1 : 2 * m + v1.val ∈ (gateAt C j1).inputs := by rcases hi1 with h | h <;> simp [h]
    have mv2 : 2 * m + v2.val ∈ (gateAt C j2).inputs := by rcases hi2 with h | h <;> simp [h]
    have mu1 : u1.val ∈ (gateAt C j1).inputs := by rcases hi1 with h | h <;> simp [h]
    have mu2 : u2.val ∈ (gateAt C j2).inputs := by rcases hi2 with h | h <;> simp [h]
    have hvne : v1 ≠ v2 := by
      intro heq
      rw [heq] at mv1
      exact hne (uniq_idx_L C L (2 * m + v2.val) rv2 j2 hj2L mv2 j1 hj1L mv1)
    have hcd := coldist m hm v1 v2 hvne
    have hsub : Finset.univ.filter (fun u : Fin (2 * m) => GG m u v1 ≠ GG m u v2) ⊆ {u1, u2} := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hu ⊢
      by_contra hnot
      push Not at hnot
      have hj1 : j1 < C.gates.length := hLsub j1 hj1L
      have hj2 : j2 < C.gates.length := hLsub j2 hj2L
      have valF : ∀ (Z : List Bool) (_ : Z.length = N) (j : ℕ) (hj : j < C.gates.length)
          (_ : (gateAt C j).op = GateOp.and) (w : ℕ) (_ : w ∈ (gateAt C j).inputs)
          (_ : w < N) (_ : Z.getD w false = false),
          (W C.gates Z).getD (N + j) false = false := by
        intro Z hZ j hj hop w hw hwN hZw
        have v := W_val C.gates Z j hj (by rw [hZ]; exact hrb' j hj)
        rw [hZ] at v
        have hop' : (C.gates[j]).op = GateOp.and := by rwa [← gateAt_eq C j hj]
        have hw' : w ∈ (C.gates[j]).inputs := by rwa [← gateAt_eq C j hj]
        rw [v, hop']
        exact and_false_of _ _ w hw' (by rw [W_lt _ _ _ (by omega)]; exact hZw)
      have hX := hlen u v1
      have hY := hlen u v2
      have hXu1 : (PEqualNP.Represents.oneEach u v1).getD u1.val false = false := by
        rw [oneEach_getD]; have := u1.isLt; have : u1.val ≠ u.val := fun h => hnot.1 (Fin.ext h.symm)
        simp [this, show u1.val ≠ 2 * m + v1.val by omega]
      have hYu1 : (PEqualNP.Represents.oneEach u v2).getD u1.val false = false := by
        rw [oneEach_getD]; have := u1.isLt; have : u1.val ≠ u.val := fun h => hnot.1 (Fin.ext h.symm)
        simp [this, show u1.val ≠ 2 * m + v2.val by omega]
      have hXu2 : (PEqualNP.Represents.oneEach u v1).getD u2.val false = false := by
        rw [oneEach_getD]; have := u2.isLt; have : u2.val ≠ u.val := fun h => hnot.2 (Fin.ext h.symm)
        simp [this, show u2.val ≠ 2 * m + v1.val by omega]
      have hYu2 : (PEqualNP.Represents.oneEach u v2).getD u2.val false = false := by
        rw [oneEach_getD]; have := u2.isLt; have : u2.val ≠ u.val := fun h => hnot.2 (Fin.ext h.symm)
        simp [this, show u2.val ≠ 2 * m + v2.val by omega]
      have hcore := core2_L N (PEqualNP.Represents.oneEach u v1) (PEqualNP.Represents.oneEach u v2)
        hX hY (fun i => i = 2 * m + v1.val ∨ i = 2 * m + v2.val)
        (by
          intro i hi
          simp only [not_or] at hi
          rw [oneEach_getD, oneEach_getD]
          simp [hi.1, hi.2])
        C L hLsub hLcl hrb'
        (by
          intro k hk ⟨i, hi, hb⟩
          rcases hb with rfl | rfl
          · have hk1 : k = j1 := uniq_idx_L C L _ rv1 j1 hj1L mv1 k hk hi
            subst hk1
            have hu1lt : u1.val < N := by have := u1.isLt; omega
            rw [valF _ hX k hj1 hop1 u1.val mu1 hu1lt hXu1,
              valF _ hY k hj1 hop1 u1.val mu1 hu1lt hYu1]
          · have hk2 : k = j2 := uniq_idx_L C L _ rv2 j2 hj2L mv2 k hk hi
            subst hk2
            have hu2lt : u2.val < N := by have := u2.isLt; omega
            rw [valF _ hX k hj2 hop2 u2.val mu2 hu2lt hXu2,
              valF _ hY k hj2 hop2 u2.val mu2 hu2lt hYu2])
        C.output
        (Or.inr ⟨hout_ge, by rw [hout_eq, Nat.add_sub_cancel_left]; exact hout_mem⟩)
        (by have := v1.isLt; have := v2.isLt; omega)
      have e1' : GG m u v1 = (W C.gates (PEqualNP.Represents.oneEach u v1)).getD C.output false := by
        rw [← hrep u v1]; rfl
      have e2' : GG m u v2 = (W C.gates (PEqualNP.Represents.oneEach u v2)).getD C.output false := by
        rw [← hrep u v2]; rfl
      exact hu (by rw [e1', e2', hcore])
    have hle2 : ({u1, u2} : Finset (Fin (2 * m))).card ≤ 2 := Finset.card_le_two
    have := (Finset.card_le_card hsub).trans hle2
    omega
  have hS1_pair_le : S1_pair.card ≤ 2 := by
    by_cases hne : S1_pair.Nonempty
    · obtain ⟨w0, hw0⟩ := hne
      simp only [S1_pair, Finset.mem_filter] at hw0
      let j0 := owner w0
      have hsub : S1_pair ⊆ (gateAt C j0).inputs.toFinset := by
        intro w hw
        simp only [S1_pair, Finset.mem_filter] at hw
        have heq : owner w = j0 := hPrivCross_uniq (owner w) j0 hw.2 hw0.2
        have hm := (howner_spec w hw.1).2
        rw [heq] at hm
        exact List.mem_toFinset.mpr hm
      have hlen2 : (gateAt C j0).inputs.length = 2 := by
        obtain ⟨_, _, u, v, _, _, hi⟩ := hw0.2
        dsimp only [j0]
        rcases hi with h | h <;> rw [h] <;> rfl
      calc S1_pair.card ≤ (gateAt C j0).inputs.toFinset.card := Finset.card_le_card hsub
        _ ≤ (gateAt C j0).inputs.length := List.toFinset_card_le _
        _ = 2 := hlen2
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  have hS1_cover : S1 ⊆ S1_not ∪ S1_mix ∪ S1_hit2 ∪ S1_pair := by
    intro w hw
    simp only [Finset.mem_union]
    by_cases hnot : (gateAt C (owner w)).op = GateOp.not
    · exact Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hw, hnot⟩)))
    · have hown := howner_spec w hw
      have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
      have hrw : r w = 1 := (Finset.mem_filter.mp hw).2
      have hwN : w < N := Finset.mem_range.mp (Finset.mem_sdiff.mp hwS).1
      have hwnot : w ∉ owned := (Finset.mem_sdiff.mp hwS).2
      have hjl : owner w < C.gates.length := hLsub (owner w) hown.1
      have hmem : gateAt C (owner w) ∈ C.gates := by
        rw [gateAt_eq C _ hjl]; exact List.getElem_mem hjl
      have hbin : ((gateAt C (owner w)).op = GateOp.and ∨ (gateAt C (owner w)).op = GateOp.or) ∧
          (gateAt C (owner w)).inputs.length = 2 := by
        rcases hfan _ hmem with h | ⟨h, _⟩
        · exact h
        · exact absurd h hnot
      obtain ⟨w', hinp⟩ := list_len2_mem _ hbin.2 w hown.2
      have hw'mem : w' ∈ (gateAt C (owner w)).inputs := by rcases hinp with h | h <;> simp [h]
      by_cases hw'N : w' < N
      · by_cases hw'2 : 2 ≤ r w'
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hw, hbin.2, w', hw'mem, hw'N, hw'2⟩))
        · have hrw' : r w' = 1 := by
            have cp : 0 < (gateAt C (owner w)).inputs.count w' := List.count_pos_iff.mpr hw'mem
            have cl := count_le_readsIn C L w' (owner w) hown.1
            change (gateAt C (owner w)).inputs.count w' ≤ r w' at cl
            omega
          have hww' : w ≠ w' := by
            rintro rfl
            have hc2 : (gateAt C (owner w)).inputs.count w = 2 := by
              rcases hinp with h | h <;> simp [h]
            have cl := count_le_readsIn C L w (owner w) hown.1
            change (gateAt C (owner w)).inputs.count w ≤ r w at cl
            omega
          by_cases hbothR : w < 2 * m ∧ w' < 2 * m
          · exfalso
            let u1 : Fin (2 * m) := ⟨w, hbothR.1⟩
            let u2 : Fin (2 * m) := ⟨w', hbothR.2⟩
            obtain ⟨v, hdiff⟩ := row_ne m hm u1 u2 (fun h => hww' (congrArg Fin.val h))
            have hcore := core2_L N (PEqualNP.Represents.oneEach u1 v)
              (PEqualNP.Represents.oneEach u2 v) (hlen u1 v) (hlen u2 v)
              (fun i => i = w ∨ i = w')
              (by
                intro i hi
                simp only [not_or] at hi
                rw [oneEach_getD, oneEach_getD]
                simp [u1, u2, hi.1, hi.2])
              C L hLsub hLcl hrb'
              (by
                intro k hk ⟨i, hi, hb⟩
                have hkeq : k = owner w := by
                  rcases hb with h | h
                  · rw [h] at hi
                    exact uniq_idx_L C L w hrw (owner w) hown.1 hown.2 k hk hi
                  · rw [h] at hi
                    exact uniq_idx_L C L w' hrw' (owner w) hown.1 hw'mem k hk hi
                rw [hkeq]
                have vX := W_val C.gates (PEqualNP.Represents.oneEach u1 v) (owner w) hjl
                  (by rw [hlen]; exact hrb' (owner w) hjl)
                have vY := W_val C.gates (PEqualNP.Represents.oneEach u2 v) (owner w) hjl
                  (by rw [hlen]; exact hrb' (owner w) hjl)
                rw [hlen] at vX vY
                rw [vX, vY, ← gateAt_eq C (owner w) hjl]
                have hXw : (W C.gates (PEqualNP.Represents.oneEach u1 v)).getD w false = true := by
                  rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]; simp [u1]
                have hXw' : (W C.gates (PEqualNP.Represents.oneEach u1 v)).getD w' false = false := by
                  rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]
                  simp [u1, Ne.symm hww', show w' ≠ 2 * m + v.val by omega]
                have hYw : (W C.gates (PEqualNP.Represents.oneEach u2 v)).getD w false = false := by
                  rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]
                  simp [u2, hww', show w ≠ 2 * m + v.val by omega]
                have hYw' : (W C.gates (PEqualNP.Represents.oneEach u2 v)).getD w' false = true := by
                  rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]; simp [u2]
                rcases hinp with h | h
                · rw [h]; simp only [List.map_cons, List.map_nil, hXw, hXw', hYw, hYw']; exact op_symm_tf _ hbin.1
                · rw [h]; simp only [List.map_cons, List.map_nil, hXw, hXw', hYw, hYw']; exact (op_symm_tf _ hbin.1).symm)
              C.output
              (Or.inr ⟨hout_ge, by rw [hout_eq, Nat.add_sub_cancel_left]; exact hout_mem⟩)
              (by omega)
            have e1' : GG m u1 v = (W C.gates (PEqualNP.Represents.oneEach u1 v)).getD C.output false := by
              rw [← hrep u1 v]; rfl
            have e2' : GG m u2 v = (W C.gates (PEqualNP.Represents.oneEach u2 v)).getD C.output false := by
              rw [← hrep u2 v]; rfl
            exact hdiff (by rw [e1', e2', hcore])
          · by_cases hbothC : 2 * m ≤ w ∧ 2 * m ≤ w'
            · exfalso
              let v1 : Fin (2 * m) := ⟨w - 2 * m, by omega⟩
              let v2 : Fin (2 * m) := ⟨w' - 2 * m, by omega⟩
              have hvne : v1 ≠ v2 := fun h => hww' (by
                have := congrArg Fin.val h; dsimp [v1, v2] at this; omega)
              have hcd := coldist m hm v1 v2 hvne
              have hempty : Finset.univ.filter (fun u : Fin (2 * m) => GG m u v1 ≠ GG m u v2) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro u _
                push Not
                have ev1 : 2 * m + v1.val = w := by dsimp [v1]; omega
                have ev2 : 2 * m + v2.val = w' := by dsimp [v2]; omega
                have hcore := core2_L N (PEqualNP.Represents.oneEach u v1)
                  (PEqualNP.Represents.oneEach u v2) (hlen u v1) (hlen u v2)
                  (fun i => i = w ∨ i = w')
                  (by
                    intro i hi
                    simp only [not_or] at hi
                    rw [oneEach_getD, oneEach_getD, ev1, ev2]
                    simp [hi.1, hi.2])
                  C L hLsub hLcl hrb'
                  (by
                    intro k hk ⟨i, hi, hb⟩
                    have hkeq : k = owner w := by
                      rcases hb with h | h
                      · rw [h] at hi
                        exact uniq_idx_L C L w hrw (owner w) hown.1 hown.2 k hk hi
                      · rw [h] at hi
                        exact uniq_idx_L C L w' hrw' (owner w) hown.1 hw'mem k hk hi
                    rw [hkeq]
                    have vX := W_val C.gates (PEqualNP.Represents.oneEach u v1) (owner w) hjl
                      (by rw [hlen]; exact hrb' (owner w) hjl)
                    have vY := W_val C.gates (PEqualNP.Represents.oneEach u v2) (owner w) hjl
                      (by rw [hlen]; exact hrb' (owner w) hjl)
                    rw [hlen] at vX vY
                    rw [vX, vY, ← gateAt_eq C (owner w) hjl]
                    have hu2 := u.isLt
                    have hXw : (W C.gates (PEqualNP.Represents.oneEach u v1)).getD w false = true := by
                      rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD, ev1]; simp
                    have hXw' : (W C.gates (PEqualNP.Represents.oneEach u v1)).getD w' false = false := by
                      rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD, ev1]
                      simp [Ne.symm hww', show w' ≠ u.val by omega]
                    have hYw : (W C.gates (PEqualNP.Represents.oneEach u v2)).getD w false = false := by
                      rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD, ev2]
                      simp [hww', show w ≠ u.val by omega]
                    have hYw' : (W C.gates (PEqualNP.Represents.oneEach u v2)).getD w' false = true := by
                      rw [W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD, ev2]; simp
                    rcases hinp with h | h
                    · rw [h]; simp only [List.map_cons, List.map_nil, hXw, hXw', hYw, hYw']; exact op_symm_tf _ hbin.1
                    · rw [h]; simp only [List.map_cons, List.map_nil, hXw, hXw', hYw, hYw']; exact (op_symm_tf _ hbin.1).symm)
                  C.output
                  (Or.inr ⟨hout_ge, by rw [hout_eq, Nat.add_sub_cancel_left]; exact hout_mem⟩)
                  (by omega)
                have e1' : GG m u v1 = (W C.gates (PEqualNP.Represents.oneEach u v1)).getD C.output false := by
                  rw [← hrep u v1]; rfl
                have e2' : GG m u v2 = (W C.gates (PEqualNP.Represents.oneEach u v2)).getD C.output false := by
                  rw [← hrep u v2]; rfl
                rw [e1', e2', hcore]
              rw [hempty] at hcd
              simp at hcd
            · apply Or.inr
              apply Finset.mem_filter.mpr
              refine ⟨hw, ?_⟩
              by_cases hwR : w < 2 * m
              · have hw'C : 2 * m ≤ w' := by omega
                let u : Fin (2 * m) := ⟨w, hwR⟩
                let v : Fin (2 * m) := ⟨w' - 2 * m, by omega⟩
                have hv_eq : 2 * m + v.val = w' := by dsimp [v]; omega
                have hinputs : (gateAt C (owner w)).inputs = [u.val, 2 * m + v.val] ∨
                    (gateAt C (owner w)).inputs = [2 * m + v.val, u.val] := by
                  rw [hv_eq]; exact hinp
                rcases hbin.1 with hand | hor
                · exact ⟨hown.1, hand, u, v, hrw, by rw [hv_eq]; exact hrw', hinputs⟩
                · exfalso
                  have hkp : isKeptPair m C L u v :=
                    ⟨hrw, by rw [hv_eq]; exact hrw', owner w, hown.1, hor, hinputs⟩
                  have huK : u ∈ kept := Finset.mem_filter.mpr ⟨Finset.mem_univ u, v, hkp⟩
                  have hwO : w ∈ owned := Finset.mem_union_left ownedC
                    (Finset.mem_image.mpr ⟨u, huK, rfl⟩)
                  exact hwnot hwO
              · have hw'R : w' < 2 * m := by omega
                let u : Fin (2 * m) := ⟨w', hw'R⟩
                let v : Fin (2 * m) := ⟨w - 2 * m, by omega⟩
                have hv_eq : 2 * m + v.val = w := by dsimp [v]; omega
                have hinputs : (gateAt C (owner w)).inputs = [u.val, 2 * m + v.val] ∨
                    (gateAt C (owner w)).inputs = [2 * m + v.val, u.val] := by
                  rw [hv_eq]; rcases hinp with h | h; exact Or.inr h; exact Or.inl h
                rcases hbin.1 with hand | hor
                · exact ⟨hown.1, hand, u, v, hrw', by rw [hv_eq]; exact hrw, hinputs⟩
                · exfalso
                  have hkp : isKeptPair m C L u v :=
                    ⟨hrw', by rw [hv_eq]; exact hrw, owner w, hown.1, hor, hinputs⟩
                  have hvK : v ∈ keptC := Finset.mem_filter.mpr ⟨Finset.mem_univ v, u, hkp⟩
                  have hwO : w ∈ owned := Finset.mem_union_right ownedR
                    (Finset.mem_image.mpr ⟨v, hvK, hv_eq⟩)
                  exact hwnot hwO
      · apply Or.inl; apply Or.inl; apply Or.inr
        apply Finset.mem_filter.mpr
        refine ⟨hw, ?_⟩
        simp only [isMixGate, Bool.and_eq_true, beq_iff_eq]
        refine ⟨hbin.2, ?_⟩
        rcases hinp with h | h <;> rw [h] <;> simp [hwN, hw'N]
  have hS_cover : S ⊆ S0' ∪ S2 ∪ S1 := by
    intro w hw
    simp only [S0', S2, S1, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : r w = 0
    · exact Or.inl (Or.inl ⟨hw, h0⟩)
    · by_cases h1 : r w = 1
      · exact Or.inr ⟨hw, h1⟩
      · exact Or.inl (Or.inr ⟨hw, by omega⟩)
  have hS1_le : S1.card ≤ T + M + (S2_all.card + E) + 2 := by
    have h1 := (Finset.card_le_card hS1_cover).trans (Finset.card_union_le _ _)
    have h2 := Finset.card_union_le (S1_not ∪ S1_mix) S1_hit2
    have h3 := Finset.card_union_le S1_not S1_mix
    omega
  have hS_le : S.card ≤ S0'.card + S2.card + S1.card := by
    have h1 := (Finset.card_le_card hS_cover).trans (Finset.card_union_le _ _)
    have h2 := Finset.card_union_le S0' S2
    omega
  have hIneq3 : 2 * (2 * m - kept.card) ≤ 4 + 3 * E + T + M := by omega
  change M ≤ (C.gates.filter (fun gate =>
    gate.inputs.length == 2 &&
    (gate.inputs.filter (fun w => w < 2 * m + 2 * m)).length == 1)).length at hM_le
  omega

end PEqualNP.Outside.L_meta_25511

theorem PEqualNP.Outside.L_meta_25511 : (∀ (m : ℕ), 5 ≤ m →
  let n := 2 * m
  let G := fun (u v : Fin n) =>
    let i := u.val / 2
    let j := v.val / 2
    let offset := if v.val % 2 = 0 then 1 else 2 + u.val % 2
    decide (i = j ∨ i = (j + offset) % m)
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    let mixed := (C.gates.filter (fun gate =>
      gate.inputs.length == 2 &&
      (gate.inputs.filter (fun w => w < n + n)).length == 1)).length
    (∀ g ∈ C.gates,
      ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) C →
    PEqualNP.Represents.Represents G C →
    38 * m ≤ 9 * C.size + 3 * mixed + 39) := by
  intro m hm
  dsimp only
  intro C hfan hrb hrep
  exact PEqualNP.Outside.L_meta_25511.full_proof m hm C hfan hrb hrep
