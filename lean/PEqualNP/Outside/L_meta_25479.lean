import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25479_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

private def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma getD_append_left {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

private lemma getD_append_right {α : Type} (l r : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := by
  simp [List.getD, List.getElem?_append_right h]

private lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [getD_append_left _ _ _ _ (by simp [hi])]
  simp [List.getD, hi, Fin.ext_iff]

private lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) (hj : j < m) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  rw [getD_append_right _ _ _ _ (by simp)]
  simp [List.getD, hj, Fin.ext_iff]

private lemma oneEach_getD_ge {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) (hw : n + m ≤ w) :
    (oneEach u v).getD w false = false := by
  have hlen : (oneEach u v).length ≤ w := by rw [oneEach_length]; exact hw
  simp [List.getD, List.getElem?_eq_none hlen]

private lemma oneEach_getD_eq_of_not_mem {n m : ℕ} (u u' : Fin n) (b b' : Fin m) (w : ℕ)
    (hw : w ∉ [u.val, u'.val, n + b.val, n + b'.val]) :
    (oneEach u b').getD w false = (oneEach u' b).getD w false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  rcases hw with ⟨h1, h2, h3, h4⟩
  by_cases hn : w < n
  · rw [oneEach_getD_left u b' w hn, oneEach_getD_left u' b w hn]
    simp [h1, h2]
  · by_cases hnm : w < n + m
    · have hj : w - n < m := by omega
      have hw' : n + (w - n) = w := by omega
      rw [← hw', oneEach_getD_right u b' (w - n) hj, oneEach_getD_right u' b (w - n) hj]
      have h3' : w - n ≠ b.val := by omega
      have h4' : w - n ≠ b'.val := by omega
      simp [h3', h4']
    · rw [oneEach_getD_ge u b' w (by omega), oneEach_getD_ge u' b w (by omega)]

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD, hj]

private lemma not_mem_of_readsIn_eq_one (C : Circuit) (w j0 j : ℕ)
    (hj0 : j0 < C.gates.length) (hj : j < C.gates.length) (hne : j ≠ j0)
    (h1 : readsIn C (Finset.range C.size) w = 1)
    (hpos : 1 ≤ (gateAt C j0).inputs.count w) :
    w ∉ (gateAt C j).inputs := by
  have hmem0 : j0 ∈ Finset.range C.size := Finset.mem_range.mpr hj0
  have hmem : j ∈ Finset.range C.size := Finset.mem_range.mpr hj
  have hsplit : (gateAt C j0).inputs.count w + (gateAt C j).inputs.count w ≤
      readsIn C (Finset.range C.size) w := by
    unfold readsIn
    have hsub : ({j0, j} : Finset ℕ) ⊆ Finset.range C.size := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    calc (gateAt C j0).inputs.count w + (gateAt C j).inputs.count w
        = ∑ a ∈ ({j0, j} : Finset ℕ), (gateAt C a).inputs.count w := by
          rw [Finset.sum_pair (Ne.symm hne)]
      _ ≤ ∑ a ∈ Finset.range C.size, (gateAt C a).inputs.count w :=
          Finset.sum_le_sum_of_subset hsub
  have hzero : (gateAt C j).inputs.count w = 0 := by omega
  exact List.count_eq_zero.mp hzero

private lemma foldl_wireStep_length (gs : List Gate) (x : List Bool) :
    (gs.foldl wireStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, wireStep, List.length_append,
      List.length_nil]
    omega

private lemma foldl_wireStep_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wireStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (wireStep x g).length := by
      simp [wireStep]; omega
    rw [ih (wireStep x g) hi']
    exact getD_append_left x _ i false hi

end PEqualNP.Outside.L_meta_25479_aux

theorem PEqualNP.Outside.L_meta_25479 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
  (C : PEqualNP.CircuitLowerBounds.Circuit)
  (u u' : Fin n) (b b' : Fin m),
  let x := u.val
  let x' := u'.val
  let y := n + b.val
  let y' := n + b'.val
  let paired := fun (r c : ℕ) =>
    ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (g.inputs = [r, c] ∨ g.inputs = [c, r])
  u ≠ u' → b ≠ b' →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  paired x y → paired x' y' →
  (∀ w ∈ [x, x', y, y'],
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1) →
  C.output ∉ [x, x', y, y'] →
  G u b' = G u' b) := by
  intro n m G C u u' b b' x x' y y' paired hu hb _hRB hRep hxy hx'y' hreads hout
  open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover
    PEqualNP.Outside.L_meta_25479_aux in
  have hxx' : x ≠ x' := fun h => hu (Fin.ext h)
  have hyy' : y ≠ y' := fun h => hb (Fin.ext (by omega))
  have hxy_ne : x ≠ y := by omega
  have hxy'_ne : x ≠ y' := by omega
  have hx'y_ne : x' ≠ y := by omega
  have hx'y'_ne : x' ≠ y' := by omega
  rcases hxy with ⟨g1, hg1_mem, hg1_op, hg1_in⟩
  rcases hx'y' with ⟨g2, hg2_mem, hg2_op, hg2_in⟩
  rcases List.getElem_of_mem hg1_mem with ⟨j1, hj1, rfl⟩
  rcases List.getElem_of_mem hg2_mem with ⟨j2, hj2, rfl⟩
  have hgate1 : gateAt C j1 = C.gates[j1] := gateAt_eq_getElem C j1 hj1
  have hgate2 : gateAt C j2 = C.gates[j2] := gateAt_eq_getElem C j2 hj2
  have hrx : readsIn C (Finset.range C.size) x = 1 := hreads x (by simp)
  have hrx' : readsIn C (Finset.range C.size) x' = 1 := hreads x' (by simp)
  have hry : readsIn C (Finset.range C.size) y = 1 := hreads y (by simp)
  have hry' : readsIn C (Finset.range C.size) y' = 1 := hreads y' (by simp)
  have hc1x : 1 ≤ (gateAt C j1).inputs.count x := by
    rw [hgate1]; rcases hg1_in with h | h <;> simp [h]
  have hc1y : 1 ≤ (gateAt C j1).inputs.count y := by
    rw [hgate1]; rcases hg1_in with h | h <;> simp [h]
  have hc2x' : 1 ≤ (gateAt C j2).inputs.count x' := by
    rw [hgate2]; rcases hg2_in with h | h <;> simp [h]
  have hc2y' : 1 ≤ (gateAt C j2).inputs.count y' := by
    rw [hgate2]; rcases hg2_in with h | h <;> simp [h]
  let inp1 : List Bool := oneEach u b'
  let inp2 : List Bool := oneEach u' b
  have hlen1 : inp1.length = n + m := oneEach_length u b'
  have hlen2 : inp2.length = n + m := oneEach_length u' b
  have hinv : ∀ k ≤ C.gates.length,
      ∀ w, w ∉ [x, x', y, y'] →
        ((C.gates.take k).foldl wireStep inp1).getD w false =
        ((C.gates.take k).foldl wireStep inp2).getD w false := by
    intro k hk
    induction k with
    | zero =>
      intro w hw
      simpa [inp1, inp2] using oneEach_getD_eq_of_not_mem u u' b b' w hw
    | succ k ih =>
      have hklt : k < C.gates.length := by omega
      have ih' := ih (by omega)
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
        List.take_succ_eq_append_getElem hklt
      have hbit :
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
            ((C.gates.take k).foldl wireStep inp1).getD i false) =
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
            ((C.gates.take k).foldl wireStep inp2).getD i false) := by
        by_cases hkj1 : k = j1
        · subst hkj1
          have hx1 : ((C.gates.take k).foldl wireStep inp1).getD x false = true := by
            rw [foldl_wireStep_getD_lt _ _ _ (by rw [hlen1]; omega)]
            simpa [inp1, x] using oneEach_getD_left u b' u.val u.isLt
          have hy2 : ((C.gates.take k).foldl wireStep inp2).getD y false = true := by
            rw [foldl_wireStep_getD_lt _ _ _ (by rw [hlen2]; omega)]
            simpa [inp2, y] using oneEach_getD_right u' b b.val b.isLt
          rw [hg1_op]
          rcases hg1_in with h | h <;>
            simp only [h, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hx1, hy2, Bool.true_or, Bool.or_true]
        · by_cases hkj2 : k = j2
          · subst hkj2
            have hy'1 : ((C.gates.take k).foldl wireStep inp1).getD y' false = true := by
              rw [foldl_wireStep_getD_lt _ _ _ (by rw [hlen1]; omega)]
              simpa [inp1, y'] using oneEach_getD_right u b' b'.val b'.isLt
            have hx'2 : ((C.gates.take k).foldl wireStep inp2).getD x' false = true := by
              rw [foldl_wireStep_getD_lt _ _ _ (by rw [hlen2]; omega)]
              simpa [inp2, x'] using oneEach_getD_left u' b u'.val u'.isLt
            rw [hg2_op]
            rcases hg2_in with h | h <;>
              simp only [h, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, hy'1, hx'2, Bool.true_or, Bool.or_true]
          · congr 1
            apply List.map_congr_left
            intro i hi
            have hi' : i ∈ (gateAt C k).inputs := by
              rwa [gateAt_eq_getElem C k hklt]
            have hnx : i ≠ x := fun h => by
              rw [h] at hi'; exact not_mem_of_readsIn_eq_one C x j1 k hj1 hklt hkj1 hrx hc1x hi'
            have hny : i ≠ y := fun h => by
              rw [h] at hi'; exact not_mem_of_readsIn_eq_one C y j1 k hj1 hklt hkj1 hry hc1y hi'
            have hnx' : i ≠ x' := fun h => by
              rw [h] at hi'; exact not_mem_of_readsIn_eq_one C x' j2 k hj2 hklt hkj2 hrx' hc2x' hi'
            have hny' : i ≠ y' := fun h => by
              rw [h] at hi'; exact not_mem_of_readsIn_eq_one C y' j2 k hj2 hklt hkj2 hry' hc2y' hi'
            exact ih' i (by simp [hnx, hnx', hny, hny'])
      intro w hw
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [wireStep]
      have hL1 : ((C.gates.take k).foldl wireStep inp1).length = n + m + k := by
        rw [foldl_wireStep_length, hlen1, List.length_take, Nat.min_eq_left (by omega)]
      have hL2 : ((C.gates.take k).foldl wireStep inp2).length = n + m + k := by
        rw [foldl_wireStep_length, hlen2, List.length_take, Nat.min_eq_left (by omega)]
      by_cases hlt : w < n + m + k
      · rw [getD_append_left _ _ _ _ (by omega), getD_append_left _ _ _ _ (by omega)]
        exact ih' w hw
      · rw [getD_append_right _ _ _ _ (by omega), getD_append_right _ _ _ _ (by omega), hL1, hL2, hbit]
  have hfinal := hinv C.gates.length le_rfl C.output hout
  rw [List.take_length] at hfinal
  have h1 : C.eval inp1 = G u b' := hRep u b'
  have h2 : C.eval inp2 = G u' b := hRep u' b
  rw [← h1, ← h2]
  exact hfinal
