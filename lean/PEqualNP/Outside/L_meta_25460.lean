import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25460_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem back_snoc {N : ℕ} {gs : List Gate} {g : Gate}
    (h : ReadsBack N ⟨gs,0⟩) (hg : ∀ i ∈ g.inputs, i < N + gs.length) :
    ReadsBack N ⟨gs ++ [g],0⟩ := by
  intro j hj i hi
  change j < (gs ++ [g]).length at hj
  change i ∈ ((gs ++ [g]).getD j ⟨.or,[]⟩).inputs at hi
  by_cases hlt : j < gs.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h j hlt i hi
  · have he : j = gs.length := by simp only [List.length_append,List.length_singleton] at hj; omega
    subst j
    have e : (gs ++ [g]).getD gs.length ⟨.or,[]⟩ = g := by simp
    rw [e] at hi
    exact hg i hi

private def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wstep_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl wstep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

private lemma foldl_wstep_getD_lt (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl wstep acc).getD j false = acc.getD j false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep acc g) (by simp [wstep]; omega)]
    rw [wstep, List.getD_append _ _ _ _ hj]

private lemma or_eval_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

private lemma build_slice_left (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) (hRb0 : ReadsBack N ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ ReadsBack N ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ pw : ℕ → ℕ,
          (∀ k ≤ m, pw k < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ k ≤ m,
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (pw k) false =
              decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, by simpa using hRb0, rfl, fun _ => off, fun _ _ => by dsimp only; omega, ?_⟩
    intro inp hlen k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD off false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨0, by omega⟩, le_rfl, by simpa using h⟩
    · rintro ⟨j, hj, hxj⟩
      have hj0 : j.val = 0 := by omega
      rw [hj0, Nat.add_zero] at hxj
      exact hxj
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hRb, hlen, pw, hpbd, hpev⟩ := ih (by omega)
    let newG : Gate := ⟨.or, [pw m, off + (m + 1)]⟩
    let gs' : List Gate := gs ++ [newG]
    let pw' : ℕ → ℕ := fun k => if k = m + 1 then N + gs0.length + m else pw k
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, ?_, by simp [gs', hlen], pw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · change ReadsBack N ⟨gs0 ++ gs', 0⟩
      rw [hassoc]
      apply back_snoc hRb
      intro i hi
      simp only [newG, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have h := hpbd m le_rfl
        simpa [List.length_append,hlen,Nat.add_assoc] using h
      · simp only [List.length_append,hlen]
        omega
    · intro k hk
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · simp only [hkeq, ite_true]; omega
      · simp only [hkeq, ite_false]
        have := hpbd k (by omega)
        omega
    · intro inp hlen_inp k hk
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (pw m) false || w.getD (off + (m + 1)) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [pw']
      by_cases hkeq : k = m + 1
      · subst hkeq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hpev inp hlen_inp m le_rfl
        have h2 : w.getD (off + (m + 1)) false = inp.getD (off + (m + 1)) false := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD (off + (m + 1)) false = _
          rw [foldl_wstep_getD_lt _ _ _ (by omega)]
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hxj⟩ | hxm)
          · exact ⟨j, by omega, hxj⟩
          · exact ⟨⟨m + 1, by omega⟩, le_rfl, hxm⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : j.val ≤ m
          · exact Or.inl ⟨j, hjm, hxj⟩
          · have hjeq : j.val = m + 1 := by omega
            rw [hjeq] at hxj
            exact Or.inr hxj
      · simp only [hkeq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hpbd k (by omega))]
        exact hpev inp hlen_inp k (by omega)

private lemma build_slice_right (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) (hRb0 : ReadsBack N ⟨gs0, 0⟩) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ ReadsBack N ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ sw : ℕ → ℕ,
          (∀ r ≤ m, sw r < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ r ≤ m,
            ((Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (sw r) false =
              decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ inp.getD (off + j.val) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], by simpa using hM0, by simpa using hRb0, rfl, fun _ => off + (n - 1), fun _ _ => by dsimp only; omega, ?_⟩
    intro inp hlen r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD (off + (n - 1)) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨⟨n - 1, by omega⟩, by dsimp only; omega, h⟩
    · rintro ⟨j, hj, hxj⟩
      have hjeq : j.val = n - 1 := by omega
      rwa [← hjeq]
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hRb, hlen, sw, hsbd, hsev⟩ := ih (by omega)
    let idx : ℕ := n - 1 - (m + 1)
    let newG : Gate := ⟨.or, [off + idx, sw m]⟩
    let gs' : List Gate := gs ++ [newG]
    let sw' : ℕ → ℕ := fun r => if r = m + 1 then N + gs0.length + m else sw r
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, ?_, by simp [gs', hlen], sw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · change ReadsBack N ⟨gs0 ++ gs', 0⟩
      rw [hassoc]
      apply back_snoc hRb
      intro i hi
      simp only [newG, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simp only [List.length_append,hlen,idx]
        omega
      · have h := hsbd m le_rfl
        simpa [List.length_append,hlen,Nat.add_assoc] using h
    · intro r hr
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · simp only [hreq, ite_true]; omega
      · simp only [hreq, ite_false]
        have := hsbd r (by omega)
        omega
    · intro inp hlen_inp r hr
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (off + idx) false || w.getD (sw m) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [sw']
      by_cases hreq : r = m + 1
      · subst hreq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have h1 := hsev inp hlen_inp m le_rfl
        have h2 : w.getD (off + idx) false = inp.getD (off + idx) false := by
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD (off + idx) false = _
          rw [foldl_wstep_getD_lt _ _ _ (by omega)]
        rw [h1, h2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (hxidx | ⟨j, hj, hxj⟩)
          · exact ⟨⟨idx, by omega⟩, by dsimp only [idx]; omega, hxidx⟩
          · exact ⟨j, by omega, hxj⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : n - 1 - m ≤ j.val
          · exact Or.inr ⟨j, hjm, hxj⟩
          · have hjeq : j.val = idx := by dsimp only [idx]; omega
            rw [hjeq] at hxj
            exact Or.inl hxj
      · simp only [hreq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hsbd r (by omega))]
        exact hsev inp hlen_inp r (by omega)

private lemma build_slice_mid (N off n : ℕ) (hn : 3 ≤ n) (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) (hRb0 : ReadsBack N ⟨gs0, 0⟩)
    (pw sw : ℕ → ℕ)
    (hpbd : ∀ k ≤ n - 2, pw k < N + gs0.length)
    (hsbd : ∀ r ≤ n - 2, sw r < N + gs0.length)
    (hpev : ∀ (inp : List Bool), inp.length = N → ∀ k ≤ n - 2,
      (Circuit.wires ⟨gs0, 0⟩ inp).getD (pw k) false =
        decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true))
    (hsev : ∀ (inp : List Bool), inp.length = N → ∀ r ≤ n - 2,
      (Circuit.wires ⟨gs0, 0⟩ inp).getD (sw r) false =
        decide (∃ j : Fin n, n - 1 - r ≤ j.val ∧ inp.getD (off + j.val) false = true)) :
    ∀ m, m ≤ n - 2 →
      ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ ReadsBack N ⟨gs0 ++ gs, 0⟩ ∧ gs.length = m ∧
        ∃ mw : ℕ → ℕ,
          (∀ i, 1 ≤ i → i ≤ m → mw i < N + gs0.length + m) ∧
          (∀ (inp : List Bool), inp.length = N → ∀ i, 1 ≤ i → i ≤ m →
            (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (mw i) false =
              decide (∃ j : Fin n, j.val ≠ i ∧ inp.getD (off + j.val) false = true)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨[], by simpa using hM0, by simpa using hRb0, rfl, fun _ => 0, fun _ h1 h2 => by omega, fun _ _ _ h1 h2 => by omega⟩
  | succ m ih =>
    intro hm1
    obtain ⟨gs, hM, hRb, hlen, mw, hmbd, hmev⟩ := ih (by omega)
    let i0 : ℕ := m + 1
    let newG : Gate := ⟨.or, [pw (i0 - 1), sw (n - 2 - i0)]⟩
    let gs' : List Gate := gs ++ [newG]
    let mw' : ℕ → ℕ := fun i => if i = i0 then N + gs0.length + m else mw i
    have hassoc : gs0 ++ gs' = (gs0 ++ gs) ++ [newG] := (List.append_assoc gs0 gs [newG]).symm
    refine ⟨gs', ?_, ?_, by simp [gs', hlen], mw', ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gs' at hg
      rw [hassoc, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨Or.inr rfl, by simp [newG]⟩
    · change ReadsBack N ⟨gs0 ++ gs', 0⟩
      rw [hassoc]
      apply back_snoc hRb
      intro i hi
      simp only [newG, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have h := hpbd (i0-1) (by dsimp [i0]; omega)
        simp only [List.length_append,hlen]
        omega
      · have h := hsbd (n-2-i0) (by omega)
        simp only [List.length_append,hlen]
        omega
    · intro i hi1 hi2
      dsimp only [mw']
      by_cases hieq : i = i0
      · simp only [hieq, ite_true]; omega
      · simp only [hieq, ite_false]
        have := hmbd i hi1 (by omega)
        omega
    · intro inp hlen_inp i hi1 hi2
      set w := Circuit.wires ⟨gs0 ++ gs, 0⟩ inp
      have hwlen : w.length = N + gs0.length + m := by
        simp only [w, Circuit.wires]
        change ((gs0 ++ gs).foldl wstep inp).length = N + gs0.length + m
        rw [foldl_wstep_len, hlen_inp, List.length_append, hlen]
        omega
      have hw' : Circuit.wires ⟨gs0 ++ gs', 0⟩ inp =
          w ++ [w.getD (pw (i0 - 1)) false || w.getD (sw (n - 2 - i0)) false] := by
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change (((gs0 ++ gs) ++ [newG]).foldl wstep inp) = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [wstep, newG, List.map_cons, List.map_nil, or_eval_two, w, Circuit.wires]
        rfl
      dsimp only [mw']
      by_cases hieq : i = i0
      · subst hieq
        simp only [ite_true]
        rw [hw', ← hwlen, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        have hkeep : ∀ u < N + gs0.length, w.getD u false = (Circuit.wires ⟨gs0, 0⟩ inp).getD u false := by
          intro u hu
          simp only [w, Circuit.wires]
          change ((gs0 ++ gs).foldl wstep inp).getD u false = _
          rw [List.foldl_append]
          rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp]; exact hu)]
          rfl
        rw [hkeep _ (hpbd (i0 - 1) (by omega)), hkeep _ (hsbd (n - 2 - i0) (by omega))]
        rw [hpev inp hlen_inp (i0 - 1) (by omega), hsev inp hlen_inp (n - 2 - i0) (by omega)]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, hxj⟩ | ⟨j, hj, hxj⟩)
          · exact ⟨j, by omega, hxj⟩
          · exact ⟨j, by omega, hxj⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hlt : j.val < i0
          · exact Or.inl ⟨j, by omega, hxj⟩
          · exact Or.inr ⟨j, by omega, hxj⟩
      · simp only [hieq, ite_false]
        rw [hw', List.getD_append _ _ _ _ (by rw [hwlen]; exact hmbd i hi1 (by omega))]
        exact hmev inp hlen_inp i hi1 (by omega)

private lemma build_slice_loo (N off n : ℕ) (hn : 2 ≤ n) (hbound : off + n ≤ N)
    (gs0 : List Gate) (hM0 : Monotone2 ⟨gs0, 0⟩) (hRb0 : ReadsBack N ⟨gs0, 0⟩) :
    ∃ gs : List Gate, Monotone2 ⟨gs0 ++ gs, 0⟩ ∧ ReadsBack N ⟨gs0 ++ gs, 0⟩ ∧ gs.length ≤ 3 * n - 6 ∧
      ∃ r : Fin n → ℕ,
        (∀ i, r i < N + gs0.length + gs.length) ∧
        (∀ (inp : List Bool), inp.length = N → ∀ i : Fin n,
          (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD (r i) false =
            decide (∃ j : Fin n, j ≠ i ∧ inp.getD (off + j.val) false = true)) := by
  by_cases hn2 : n = 2
  · subst hn2
    refine ⟨[], by simpa using hM0, by simpa using hRb0, by simp, fun i => off + (1 - i.val),
      fun i => by dsimp only; omega, ?_⟩
    intro inp hlen i
    simp only [List.append_nil, Circuit.wires]
    change (gs0.foldl wstep inp).getD (off + (1 - i.val)) false = _
    rw [foldl_wstep_getD_lt _ _ _ (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨⟨1 - i.val, by omega⟩, ?_, h⟩
      intro heq
      have := congrArg Fin.val heq
      dsimp only at this
      omega
    · rintro ⟨j, hne, hxj⟩
      have hjeq : j.val = 1 - i.val := by
        have hne' : j.val ≠ i.val := fun h => hne (Fin.ext h)
        omega
      rwa [← hjeq]
  · have hn3 : 3 ≤ n := by omega
    obtain ⟨gs1, hM1, hRb1, hlen1, pw, hpbd1, hpev1⟩ := build_slice_left N off n (by omega) hbound gs0 hM0 hRb0 (n - 2) le_rfl
    obtain ⟨gs2, hM2, hRb2, hlen2, sw, hsbd2, hsev2⟩ := build_slice_right N off n (by omega) hbound (gs0 ++ gs1) hM1 hRb1 (n - 2) le_rfl
    have hlen012 : ((gs0 ++ gs1) ++ gs2).length = gs0.length + 2 * (n - 2) := by
      simp only [List.length_append, hlen1, hlen2]; omega
    have hpbd12 : ∀ k ≤ n - 2, pw k < N + ((gs0 ++ gs1) ++ gs2).length := by
      intro k hk; have := hpbd1 k hk; omega
    have hsbd12 : ∀ r ≤ n - 2, sw r < N + ((gs0 ++ gs1) ++ gs2).length := by
      intro r hr; have := hsbd2 r hr; simp only [List.length_append, hlen1] at this; omega
    have hpev12 : ∀ (inp : List Bool), inp.length = N → ∀ k ≤ n - 2,
        (Circuit.wires ⟨(gs0 ++ gs1) ++ gs2, 0⟩ inp).getD (pw k) false =
          decide (∃ j : Fin n, j.val ≤ k ∧ inp.getD (off + j.val) false = true) := by
      intro inp hlen_inp k hk
      unfold Circuit.wires
      change (((gs0 ++ gs1) ++ gs2).foldl wstep inp).getD (pw k) false = _
      rw [List.foldl_append]
      rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp, List.length_append, hlen1]; have := hpbd1 k hk; omega)]
      exact hpev1 inp hlen_inp k hk
    obtain ⟨gs3, hM3, hRb3, hlen3, mw, hmbd3, hmev3⟩ :=
      build_slice_mid N off n hn3 ((gs0 ++ gs1) ++ gs2) hM2 hRb2 pw sw hpbd12 hsbd12 hpev12 hsev2 (n - 2) le_rfl
    let gtot : List Gate := (gs1 ++ gs2) ++ gs3
    have hassoc : gs0 ++ gtot = ((gs0 ++ gs1) ++ gs2) ++ gs3 := by
      simp [gtot, List.append_assoc]
    let r : Fin n → ℕ := fun i =>
      if i.val = 0 then sw (n - 2)
      else if i.val = n - 1 then pw (n - 2)
      else mw i.val
    refine ⟨gtot, ?_, ?_, ?_, r, ?_, ?_⟩
    · intro g hg
      change g ∈ gs0 ++ gtot at hg
      rw [hassoc] at hg
      exact hM3 g hg
    · change ReadsBack N ⟨gs0 ++ gtot, 0⟩
      rwa [hassoc]
    · simp only [gtot, List.length_append, hlen1, hlen2, hlen3]; omega
    · intro i
      dsimp only [r]
      have htot : N + gs0.length + gtot.length = N + ((gs0 ++ gs1) ++ gs2).length + (n - 2) := by
        simp only [gtot, List.length_append, hlen1, hlen2, hlen3]; omega
      by_cases hi0 : i.val = 0
      · simp only [hi0, ite_true]; have := hsbd12 (n - 2) le_rfl; omega
      · simp only [hi0, ite_false]
        by_cases hin : i.val = n - 1
        · simp only [hin, ite_true]; have := hpbd12 (n - 2) le_rfl; omega
        · simp only [hin, ite_false]; have := hmbd3 i.val (by omega) (by omega); omega
    · intro inp hlen_inp i
      have hkeep : ∀ u < N + ((gs0 ++ gs1) ++ gs2).length,
          (Circuit.wires ⟨gs0 ++ gtot, 0⟩ inp).getD u false =
          (Circuit.wires ⟨(gs0 ++ gs1) ++ gs2, 0⟩ inp).getD u false := by
        intro u hu
        unfold Circuit.wires; dsimp only; rw [hassoc]
        change ((((gs0 ++ gs1) ++ gs2) ++ gs3).foldl wstep inp).getD u false = _
        rw [List.foldl_append]
        rw [foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len, hlen_inp]; exact hu)]
        rfl
      dsimp only [r]
      by_cases hi0 : i.val = 0
      · simp only [hi0, ite_true]
        rw [hkeep _ (hsbd12 (n - 2) le_rfl), hsev2 inp hlen_inp (n - 2) le_rfl]
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨j, hj, hxj⟩; exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
        · rintro ⟨j, hne, hxj⟩; have : j.val ≠ i.val := fun h => hne (Fin.ext h); exact ⟨j, by omega, hxj⟩
      · simp only [hi0, ite_false]
        by_cases hin : i.val = n - 1
        · simp only [hin, ite_true]
          rw [hkeep _ (hpbd12 (n - 2) le_rfl), hpev12 inp hlen_inp (n - 2) le_rfl]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨j, hj, hxj⟩; exact ⟨j, fun h => by have := congrArg Fin.val h; omega, hxj⟩
          · rintro ⟨j, hne, hxj⟩; have : j.val ≠ i.val := fun h => hne (Fin.ext h); exact ⟨j, by omega, hxj⟩
        · simp only [hin, ite_false]
          have heq : (Circuit.wires ⟨gs0 ++ gtot, 0⟩ inp) = Circuit.wires ⟨((gs0 ++ gs1) ++ gs2) ++ gs3, 0⟩ inp := by
            unfold Circuit.wires; dsimp only; rw [hassoc]
          rw [heq, hmev3 inp hlen_inp i.val (by omega) (by omega)]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
          constructor
          · rintro ⟨j, hne, hxj⟩; exact ⟨j, fun h => hne (congrArg Fin.val h), hxj⟩
          · rintro ⟨j, hne, hxj⟩; exact ⟨j, fun h => hne (Fin.ext h), hxj⟩


private lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, j.isLt]

private lemma wires_keep (gs0 gs : List Gate) (inp : List Bool) (idx : ℕ)
    (h : idx < inp.length + gs0.length) :
    (Circuit.wires ⟨gs0 ++ gs, 0⟩ inp).getD idx false = (Circuit.wires ⟨gs0, 0⟩ inp).getD idx false := by
  unfold Circuit.wires
  change ((gs0 ++ gs).foldl wstep inp).getD idx false = (gs0.foldl wstep inp).getD idx false
  rw [List.foldl_append, foldl_wstep_getD_lt _ _ _ (by rw [foldl_wstep_len]; exact h)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h₁ h₂
  · rw [List.getElem?_append_left h₁]
  · subst h₂; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp


theorem back_append {N : ℕ} {L R : List Gate}
    (hL : ReadsBack N ⟨L,0⟩) (hR : ReadsBack (N + L.length) ⟨R,0⟩) :
    ReadsBack N ⟨L ++ R,0⟩ := by
  intro j hj w hw
  change j < (L ++ R).length at hj
  change w ∈ ((L ++ R).getD j ⟨.or,[]⟩).inputs at hw
  by_cases h : j < L.length
  · rw [List.getD_append _ _ _ _ h] at hw
    exact hL j h w hw
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)] at hw
    have hl : j - L.length < R.length := by simp [List.length_append] at hj; omega
    have hr := hR (j - L.length) hl w hw
    omega

def flipOp : GateOp → GateOp
  | .and => .or
  | _ => .and

def dualGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨flipOp g.op,g.inputs.map f⟩

theorem flip_eval (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (xs : List Bool) : (flipOp op).eval (xs.map Bool.not) = !(op.eval xs) := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · induction xs with
    | nil => rfl
    | cons b xs ih =>
      change (xs.map Bool.not).any id = !(xs.all id) at ih
      change (!b || (xs.map Bool.not).any id) = !(b && xs.all id)
      rw [ih]
      cases b <;> rfl
  · induction xs with
    | nil => rfl
    | cons b xs ih =>
      change (xs.map Bool.not).all id = !(xs.any id) at ih
      change (!b && (xs.map Bool.not).all id) = !(b || xs.any id)
      rw [ih]
      cases b <;> rfl

theorem dual_fit (f : ℕ → ℕ) {g : Gate}
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (dualGate f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (dualGate f g).inputs.length ≤ 2 := by
  have hop := h.1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> simp [dualGate,hop,flipOp,h.2]

theorem mapped_bound (N B : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i < N, f i < B) (hg : ∀ i, N ≤ i → f i = B + (i-N))
    {nx ny i : ℕ} (hN : N ≤ nx) (hrel : ny + N = nx + B) (hi : i < nx) : f i < ny := by
  by_cases h : i < N
  · have h1 := hf i h
    omega
  · rw [hg i (by omega)]
    omega

theorem dual_back (N B : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i < N, f i < B) (hg : ∀ i, N ≤ i → f i = B + (i-N))
    (C : Circuit) (hC : ReadsBack N C) :
    ReadsBack B ⟨C.gates.map (dualGate f),0⟩ := by
  intro j hj w hw
  have hj' : j < C.gates.length := by simpa using hj
  change w ∈ ((C.gates.map (dualGate f)).getD j ⟨.or,[]⟩).inputs at hw
  rw [List.getD_eq_getElem _ _ hj] at hw
  simp only [List.getElem_map,dualGate] at hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  have hi' : i ∈ (gateAt C j).inputs := by
    rw [gateAt,List.getD_eq_getElem _ _ hj']
    exact hi
  exact mapped_bound N B f hf hg (nx := N+j) (ny := B+j) (by omega) (by omega)
    (hC j hj' i hi')

theorem dual_fold (f : ℕ → ℕ) (N B : ℕ)
    (hf : ∀ i < N, f i < B) (hg : ∀ i, N ≤ i → f i = B + (i - N)) :
    ∀ (gs : List Gate) (x y : List Bool),
      N ≤ x.length → y.length + N = x.length + B →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      ReadsBack x.length ⟨gs,0⟩ →
      (∀ i < x.length, y.getD (f i) false = !(x.getD i false)) →
      ∀ i < x.length + gs.length,
        ((gs.map (dualGate f)).foldl wstep y).getD (f i) false = !((gs.foldl wstep x).getD i false) := by
  intro gs
  induction gs with
  | nil =>
    intro x y _ _ _ _ h i hi
    exact h i (by simpa using hi)
  | cons g gs ih =>
    intro x y hx hlen hFit hback he i hi
    have hb (j : ℕ) (hj : j ∈ g.inputs) : j < x.length := by
      have e := hback 0 (by simp) j (by simpa [gateAt] using hj)
      simpa using e
    let v := g.op.eval (g.inputs.map fun j => x.getD j false)
    have ev : wstep y (dualGate f g) = y ++ [!v] := by
      change y ++ [(flipOp g.op).eval ((g.inputs.map f).map fun j => y.getD j false)] = _
      have hMap : (g.inputs.map f).map (fun j => y.getD j false) =
          (g.inputs.map (fun j => x.getD j false)).map Bool.not := by
        rw [List.map_map,List.map_map]
        exact List.map_congr_left fun j hj => he j (hb j hj)
      rw [hMap, flip_eval g.op (hFit g (by simp))]
    have ex : wstep x g = x ++ [v] := rfl
    have tail : ReadsBack (wstep x g).length ⟨gs,0⟩ := by
      intro j hj w hw
      have hd : w ∈ (gateAt (⟨g :: gs,0⟩ : Circuit) (j+1)).inputs := by
        simpa [gateAt,List.getD_cons_succ] using hw
      have hi := hback (j+1) (by simp; omega) w hd
      rw [ex]
      simp only [List.length_append,List.length_singleton]
      omega
    have hStep (j : ℕ) (hj : j < (wstep x g).length) :
        (wstep y (dualGate f g)).getD (f j) false = !((wstep x g).getD j false) := by
      rw [ex] at hj
      simp only [List.length_append,List.length_singleton] at hj
      rw [ev,ex]
      by_cases hd : j < x.length
      · have hy := mapped_bound N B f hf hg hx hlen hd
        rw [List.getD_append _ _ _ _ hy,List.getD_append _ _ _ _ hd]
        exact he j hd
      · have eq : j = x.length := by omega
        subst j
        have ep : f x.length = y.length := by rw [hg _ hx]; omega
        rw [ep]
        simp
    simp only [List.map_cons,List.foldl_cons]
    refine ih (wstep x g) (wstep y (dualGate f g)) ?_ ?_
      (fun a ha => hFit a (List.mem_cons_of_mem _ ha)) tail hStep i ?_
    · rw [ex]
      simp
      omega
    · rw [ex,ev]
      simp
      omega
    · rw [ex]
      simp only [List.length_append,List.length_singleton,List.length_cons] at hi ⊢
      omega

theorem only_one_excluded {n : ℕ} (P : Fin n → Bool) (u i : Fin n)
    (h : ∀ j, P j = decide (j = u)) :
    decide (∃ j : Fin n, j ≠ i ∧ P j = true) = !(P i) := by
  rw [h i]
  by_cases e : i = u
  · have he : ¬ ∃ j : Fin n, j ≠ i ∧ P j = true := by
      rintro ⟨j,hj,hp⟩
      rw [h,decide_eq_true_eq] at hp
      exact hj (hp.trans e.symm)
    rw [decide_eq_false_iff_not.mpr he]
    simp [e]
  · have he : ∃ j : Fin n, j ≠ i ∧ P j = true := ⟨u,Ne.symm e,by simp [h]⟩
    simp [e,he]

theorem complement {r c s : ℕ} (G : Fin r → Fin c → Bool) (C : Circuit)
    (hr : 2 ≤ r) (hc : 2 ≤ c) (hFit : Monotone2 C) (hBack : ReadsBack (r+c) C)
    (hSize : C.size ≤ s) (hRep : Represents G C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (r+c) D ∧
      D.size ≤ s + (3*r-6) + (3*c-6) + 1 ∧ Represents (fun u v => !(G u v)) D := by
  let N := r+c
  have emptyFit : Monotone2 ⟨[],0⟩ := by intro g hg; simp at hg
  have emptyBack : ReadsBack N ⟨[],0⟩ := by intro j hj; simp at hj
  obtain ⟨L,hLFit,hLBack,hLenL,row,hrowL,hrowV⟩ :=
    build_slice_loo N 0 r hr (by dsimp [N]; omega) [] emptyFit emptyBack
  simp only [List.nil_append,List.length_nil,Nat.add_zero] at hLFit hLBack hrowL hrowV
  obtain ⟨R,hPrepFit,hPrepBack,hLenR,col,hcolL,hcolV⟩ :=
    build_slice_loo N r c hc (by rfl) L hLFit hLBack
  let prep := L ++ R
  let B := N + prep.length
  let addr (i : ℕ) : ℕ :=
    if h : i < r then row ⟨i,h⟩ else if h' : i < N then col ⟨i-r,by dsimp [N] at h'; omega⟩
    else B + (i-N)
  have rowAddr (i : Fin r) : addr i.val = row i := by simp [addr,i.isLt]
  have colAddr (i : Fin c) : addr (r+i.val) = col i := by
    have hh : r + i.val < N := by have := i.isLt; dsimp [N]; omega
    simp only [addr,dite_eq_right (show ¬ r+i.val<r by omega),dite_eq_left hh]
    congr 1
    exact Fin.ext (Nat.add_sub_cancel_left _ _)
  have small (i : ℕ) (hi : i < N) : addr i < B := by
    by_cases il : i < r
    · rw [show addr i = row ⟨i,il⟩ from rowAddr ⟨i,il⟩]
      have h := hrowL ⟨i,il⟩
      dsimp [B,prep]
      simp only [List.length_append]
      omega
    · let iv : Fin c := ⟨i-r,by dsimp [N] at hi; omega⟩
      have eq : r+iv.val=i := by dsimp [iv]; omega
      rw [← eq,colAddr]
      have h := hcolL iv
      simpa [B,prep,List.length_append,Nat.add_assoc] using h
  have large (i : ℕ) (hi : N ≤ i) : addr i = B+(i-N) := by
    have hh : ¬ i < r := by dsimp [N] at hi; omega
    simp [addr,hh,Nat.not_lt_of_ge hi]
  let M := C.gates.map (dualGate addr)
  let trail : Gate := ⟨.and,[]⟩
  let D : Circuit := ⟨(prep ++ M) ++ [trail],
    if C.output < N + C.gates.length then addr C.output else B + C.gates.length⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ (prep ++ M) ++ [trail] at hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with (ha | hb) | rfl
    · exact hPrepFit g ha
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      exact dual_fit addr (hFit a ha)
    · simp [trail]
  · change ReadsBack N ⟨(prep ++ M) ++ [trail],0⟩
    apply back_snoc
    · apply back_append hPrepBack
      exact dual_back N B addr small large C hBack
    · intro i hi
      simp [trail] at hi
  · change C.gates.length ≤ s at hSize
    simp [D,Circuit.size,prep,M,List.length_append]
    omega
  · intro u v
    let x := oneEach u v
    let Y := prep.foldl wstep x
    have hx : x.length = N := oneEach_len u v
    have hY : Y.length = B := by rw [show Y = prep.foldl wstep x from rfl,foldl_wstep_len,hx]
    have evalL (i : Fin r) : Y.getD (row i) false = !(x.getD i.val false) := by
      change (Circuit.wires ⟨L++R,0⟩ x).getD (row i) false = _
      rw [wires_keep L R x _ (by rw [hx]; exact hrowL i),hrowV x hx i]
      simpa only [Nat.zero_add] using
        (only_one_excluded (fun j : Fin r => x.getD j.val false) u i (oneEach_getD_left u v))
    have evalR (i : Fin c) : Y.getD (col i) false = !(x.getD (r+i.val) false) := by
      change (Circuit.wires ⟨L++R,0⟩ x).getD (col i) false = _
      rw [hcolV x hx i]
      exact only_one_excluded (fun j : Fin c => x.getD (r+j.val) false) v i (oneEach_getD_right u v)
    have hInit (i : ℕ) (hi : i < x.length) : Y.getD (addr i) false = !(x.getD i false) := by
      by_cases h : i < r
      · rw [show addr i = row ⟨i,h⟩ from rowAddr ⟨i,h⟩]
        exact evalL ⟨i,h⟩
      · let j : Fin c := ⟨i-r,by dsimp [N] at hx; omega⟩
        have hEq : r+j.val = i := by dsimp [j]; omega
        rw [← hEq,colAddr]
        exact evalR j
    have hcBack : ReadsBack x.length ⟨C.gates,0⟩ := by rw [hx]; exact hBack
    have hDual := dual_fold addr N B small large C.gates x Y (by omega) (by omega)
      (fun g hg => (hFit g hg).1) hcBack hInit
    let Z := (prep ++ M).foldl wstep x
    have hZ : Z.length = B+C.gates.length := by
      rw [show Z = (prep ++ M).foldl wstep x from rfl,foldl_wstep_len,hx]
      simp [M,B,List.length_append,Nat.add_assoc]
    change (((prep ++ M) ++ [trail]).foldl wstep x).getD
        (if C.output < N+C.gates.length then addr C.output else B+C.gates.length) false = !(G u v)
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (Z++[true]).getD
      (if C.output < N+C.gates.length then addr C.output else B+C.gates.length) false = !(G u v)
    rw [← hRep u v]
    change _ = !((C.gates.foldl wstep x).getD C.output false)
    by_cases h : C.output < N+C.gates.length
    · have hAddr : addr C.output < Z.length := by
        rw [hZ]
        exact mapped_bound N B addr small large (nx := N+C.gates.length) (ny := B+C.gates.length)
          (by omega) (by omega) h
      rw [ite_eq_left h,List.getD_append _ _ _ _ hAddr]
      have e := hDual C.output (by omega)
      simpa only [Z,List.foldl_append] using e
    · rw [ite_eq_right h,← hZ]
      simp only [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero]
      rw [List.getD_eq_default _ _ (by rw [foldl_wstep_len,hx]; omega)]
      rfl

end PEqualNP.Outside.L_meta_25460_aux

open PEqualNP.Outside.L_meta_25460_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25460 : ∀ (r c s : ℕ) (G : Fin r → Fin c → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ r → 2 ≤ c → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) C → C.size ≤ s → PEqualNP.Represents.Represents G C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) D ∧ D.size ≤ s + (3 * r - 6) + (3 * c - 6) + 1 ∧ PEqualNP.Represents.Represents (fun u v => !(G u v)) D := by
  intro r c s G C hr hc hFit hBack hSize hRep
  exact complement G C hr hc hFit hBack hSize hRep
