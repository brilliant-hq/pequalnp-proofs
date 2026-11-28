import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9045_1
    (hUncov :
      ∀ (q v : ℕ) (S : Fin v → Finset (Fin v)),
        (1 : ℕ) ≤ q →
        v = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ (l : Fin v), (S l).card = q + (1 : ℕ)) →
        ∀ (Y : Finset (Fin v)),
          Y.card ≤ q →
          ∃ p : Fin v, ∀ l ∈ Y, p ∉ S l)
    (hSafeAndHalfLB :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (E : Finset (Fin x2 × Fin x2)),
        (200 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →
        (∀ (Y : Finset (Fin x2)), Y.card ≤ x1 → ∃ p : Fin x2, ∀ l ∈ Y, p ∉ x3 l) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * E.card →
        (∀ e ∈ E, e.1 ∈ x3 e.2 ∧
          ∃ s < x4.size,
            (PEqualNP.MetaComplexity.NestedCover.gateAt x4 s).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 X Y → (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD (x2 + x2 + s) Bool.false = Bool.false) ∧
            (x4.wires (PEqualNP.GenericRejection.incidenceInput {e.1} {e.2})).getD (x2 + x2 + s) Bool.false = Bool.true) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 x5 hx1 hx2 hLine hUniq hAO hx5lt houtHi hSafe5 hHalf
  let safe : ℕ → Prop := fun w =>
    ∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 X Y →
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD w Bool.false = Bool.false
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs ++ [g]).foldl step x = gs.foldl step x ++ [g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false)] := by
    intro gs g x
    simp [step, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (gs.foldl step x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [run_snoc]
      simp [ih]
      omega
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length →
      ((gs ++ hs).foldl step x).getD i false = (gs.foldl step x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc]
      have hlen : ((gs ++ hs).foldl step x).length = x.length + (gs ++ hs).length := run_length (gs ++ hs) x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen, List.length_append]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
    intro gs x i hi
    have := run_prefix [] gs x i (by simpa using hi)
    simpa using this
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl step x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (gs.foldl step x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (gs.foldl step x).length = x.length + gs.length := run_length gs x
      have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then ((gs ++ [g]).foldl step x).getD i false else false) =
          l.map fun i => if i < x.length + k then (gs.foldl step x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · exact run_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
        exact ih j h
      · have hjj : j = gs.length := by simp at hj; omega
        subst hjj
        have hg : (gs ++ [g])[gs.length] = g := by simp
        rw [hg, same _ le_rfl, run_snoc, ← hlen]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hlen_inc : ∀ (X Y : Finset (Fin x2)),
      (PEqualNP.GenericRejection.incidenceInput X Y).length = x2 + x2 := by
    intro X Y
    change (List.ofFn (fun p : Fin x2 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin x2 => decide (l ∈ Y))).length = x2 + x2
    simp
  have hno_input_safe : ∀ w < x2 + x2, ¬safe w := by
    intro w hw hsw
    by_cases hlt : w < x2
    · let p : Fin x2 := ⟨w, hlt⟩
      have hfalse : PEqualNP.GenericRejection.IsFalseInput x3 ({p} : Finset (Fin x2)) (∅ : Finset (Fin x2)) := by
        intro l hl
        simp at hl
      have hv0 := hsw ({p} : Finset (Fin x2)) (∅ : Finset (Fin x2)) (by simp) hfalse
      have hv1 : (x4.wires (PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin x2)) (∅ : Finset (Fin x2)))).getD w false = true := by
        change (x4.gates.foldl step (PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin x2)) (∅ : Finset (Fin x2)))).getD w false = true
        rw [run_input x4.gates _ w (by rw [hlen_inc]; omega)]
        change (List.ofFn (fun q : Fin x2 => decide (q ∈ ({p} : Finset (Fin x2)))) ++ List.ofFn (fun q : Fin x2 => decide (q ∈ (∅ : Finset (Fin x2))))).getD w false = true
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hlt])]
        simp [p, hlt]
      rw [hv1] at hv0
      cases hv0
    · let l : Fin x2 := ⟨w - x2, by omega⟩
      have hfalse : PEqualNP.GenericRejection.IsFalseInput x3 (∅ : Finset (Fin x2)) ({l} : Finset (Fin x2)) := by
        intro l' _
        exact Finset.disjoint_empty_right _
      have hv0 := hsw (∅ : Finset (Fin x2)) ({l} : Finset (Fin x2)) (by simp; omega) hfalse
      have hv1 : (x4.wires (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin x2)) ({l} : Finset (Fin x2)))).getD w false = true := by
        change (x4.gates.foldl step (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin x2)) ({l} : Finset (Fin x2)))).getD w false = true
        rw [run_input x4.gates _ w (by rw [hlen_inc]; omega)]
        change (List.ofFn (fun q : Fin x2 => decide (q ∈ (∅ : Finset (Fin x2)))) ++ List.ofFn (fun q : Fin x2 => decide (q ∈ ({l} : Finset (Fin x2))))).getD w false = true
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp [l, show w - x2 < x2 by omega]
      rw [hv1] at hv0
      cases hv0
  have hgate_eval : ∀ (X Y : Finset (Fin x2)) (j : ℕ) (hj : j < x4.size),
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD (x2 + x2 + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs.map fun i =>
          (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD i false) := by
    intro X Y j hj
    have hj' : j < x4.gates.length := hj
    have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = x4.gates[j] :=
      List.getD_eq_getElem _ _ hj'
    change (x4.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD (x2 + x2 + j) false = _
    have hrg := run_gate x4.gates (PEqualNP.GenericRejection.incidenceInput X Y) j hj'
    rw [hlen_inc X Y] at hrg
    rw [hrg, hge]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hib : i < x2 + x2 + j := hAO.2.1 j hj' i (hge.symm ▸ hi)
    simp only [hib, ite_true]
    rfl
  have hsafe_or : ∀ (j : ℕ) (hj : j < x4.size),
      (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      safe (x2 + x2 + j) →
      ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs, safe u := by
    intro j hj hor hs u hu X Y hY hF
    have hval := hs X Y hY hF
    rw [hgate_eval X Y j hj, hor] at hval
    change (((PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs.map fun i =>
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD i false).any id) = false at hval
    cases hvu : (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD u false
    · rfl
    · have hany : (((PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs.map fun i =>
          (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD i false).any id) = true := by
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.mpr ⟨u, hu, hvu⟩, rfl⟩
      rw [hany] at hval
      cases hval
  have hsafe_wire_and : ∀ (p l : Fin x2) (w : ℕ),
      w < x2 + x2 + x4.size →
      safe w →
      (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD w false = true →
      ∃ s < x4.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 s).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        safe (x2 + x2 + s) ∧
        (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD (x2 + x2 + s) false = true := by
    intro p l w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hsw hval
      by_cases hlt : w < x2 + x2
      · exact False.elim (hno_input_safe w hlt hsw)
      · let j : ℕ := w - (x2 + x2)
        have hj : j < x4.size := by omega
        have hwj : w = x2 + x2 + j := by omega
        rw [hwj] at hsw hval
        have hj' : j < x4.gates.length := hj
        have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = x4.gates[j] :=
          List.getD_eq_getElem _ _ hj'
        have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j ∈ x4.gates := by
          rw [hge]
          exact List.getElem_mem hj'
        rcases hAO.1 _ hmem with hand | hor
        · exact ⟨j, hj, hand, hsw, hval⟩
        · rw [hgate_eval {p} {l} j hj, hor] at hval
          change (((PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs.map fun i =>
            (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD i false).any id) = true at hval
          rw [List.any_eq_true] at hval
          rcases hval with ⟨b, hb, hbid⟩
          rcases List.mem_map.mp hb with ⟨u, hu, hvu⟩
          have hub : u < x2 + x2 + j := hAO.2.1 j hj' u hu
          have hsu : safe u := hsafe_or j hj hor hsw u hu
          have hvu' : (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD u false = true := by
            rw [hvu]
            exact hbid
          exact ih u (by omega) (by omega) hsu hvu'
  let E : Finset (Fin x2 × Fin x2) :=
    (Finset.univ.sigma fun l : Fin x2 =>
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 Bool.false = Bool.true}).image
      (fun z => (z.2, z.1))
  have hEcard : E.card = ∑ l : Fin x2, {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD x5 Bool.false = Bool.true}.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_sigma _ _
    · intro z1 z2 hz
      rcases z1 with ⟨l1, p1⟩
      rcases z2 with ⟨l2, p2⟩
      simp only [Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, rfl⟩
      rfl
  have hEhalf : x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * E.card := by
    rw [hEcard]
    exact hHalf
  have hEmem : ∀ e ∈ E, e.1 ∈ x3 e.2 ∧
      ∃ s < x4.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 s).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        safe (x2 + x2 + s) ∧
        (x4.wires (PEqualNP.GenericRejection.incidenceInput {e.1} {e.2})).getD (x2 + x2 + s) Bool.false = Bool.true := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨⟨l, p⟩, hlp, rfl⟩
    rw [Finset.mem_sigma] at hlp
    rcases Finset.mem_filter.mp hlp.2 with ⟨hp, hval⟩
    exact ⟨hp, hsafe_wire_and p l x5 (by omega) hSafe5 hval⟩
  exact hSafeAndHalfLB x1 x2 x3 x4 E hx1 hx2 hLine hUniq (hUncov x1 x2 x3 (by omega) hx2 hLine) hAO hEhalf hEmem
