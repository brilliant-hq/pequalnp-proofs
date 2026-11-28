import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8947_1
    (hUncov :
      ∀ (q v : ℕ) (S : Fin v → Finset (Fin v)),
        (1 : ℕ) ≤ q →
        v = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ (l : Fin v), (S l).card = q + (1 : ℕ)) →
        ∀ (Y : Finset (Fin v)),
          Y.card ≤ q →
          ∃ p : Fin v, ∀ l ∈ Y, p ∉ S l)
    (hHalfWireLB :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
        (200 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →
        (∀ (Y : Finset (Fin x2)), Y.card ≤ x1 → ∃ p : Fin x2, ∀ l ∈ Y, p ∉ x3 l) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        x2 + x2 ≤ x5 →
        x5 < x4.output →
        x4.output < x2 + x2 + x4.size →
        (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) →
        x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x15 x16 : Finset (Fin x2)), x16.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x15 x16 → x4.eval (PEqualNP.GenericRejection.incidenceInput x15 x16) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 hx1 hx2 hLine hUniq hAO _hNotR2 houtLo houtHi hOutOr hRight hSafeOut
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
  let j : ℕ := x4.output - (x2 + x2)
  have hj : j < x4.gates.length := by
    change x4.output - (x2 + x2) < x4.size
    omega
  have houtEq : x4.output = x2 + x2 + j := by omega
  rcases hOutOr with ⟨g, hgSome, hgOr⟩
  have hgEq : x4.gates[j] = g := by
    have h1 : x4.gates[j]? = Option.some x4.gates[j] := List.getElem?_eq_getElem hj
    rw [h1] at hgSome
    exact Option.some.inj hgSome
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = g :=
    (List.getD_eq_getElem _ _ hj).trans hgEq
  have hmem : g ∈ x4.gates := by
    rw [← hgEq]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 g hmem)
  have haLt : a < x4.output := by
    rw [houtEq]
    have haIn : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs := by
      rw [hge, hab]; simp
    exact hAO.2.1 j hj a haIn
  have hbLt : b < x4.output := by
    rw [houtEq]
    have hbIn : b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs := by
      rw [hge, hab]; simp
    exact hAO.2.1 j hj b hbIn
  have heval_or : ∀ (X Y : Finset (Fin x2)),
      x4.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
      ((x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD a false ||
       (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD b false) := by
    intro X Y
    change (x4.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD x4.output false = _
    rw [houtEq]
    have hrg := run_gate x4.gates (PEqualNP.GenericRejection.incidenceInput X Y) j hj
    rw [hlen_inc X Y] at hrg
    rw [hrg, hgEq, hgOr, hab]
    have haLt' : a < x2 + x2 + j := by omega
    have hbLt' : b < x2 + x2 + j := by omega
    simp only [List.map_cons, List.map_nil, haLt', hbLt', ite_true]
    change ([(x4.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD a false,
      (x4.gates.foldl step (PEqualNP.GenericRejection.incidenceInput X Y)).getD b false].any id) = _
    simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rfl
  have hSafe_a : ∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 X Y →
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD a false = false := by
    intro X Y hY hF
    have h0 := hSafeOut X Y hY hF
    rw [heval_or X Y] at h0
    exact (Bool.or_eq_false_iff.mp h0).1
  have hSafe_b : ∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 X Y →
      (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD b false = false := by
    intro X Y hY hF
    have h0 := hSafeOut X Y hY hF
    rw [heval_or X Y] at h0
    exact (Bool.or_eq_false_iff.mp h0).2
  have hno_input_safe : ∀ w < x2 + x2,
      ¬(∀ (X Y : Finset (Fin x2)), Y.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 X Y →
        (x4.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD w false = false) := by
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
  have haGe : x2 + x2 ≤ a := by
    by_contra hlt
    exact hno_input_safe a (by omega) hSafe_a
  have hbGe : x2 + x2 ≤ b := by
    by_contra hlt
    exact hno_input_safe b (by omega) hSafe_b
  have hline_split : ∀ l : Fin x2,
      (x3 l).card ≤
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}.card +
      {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}.card := by
    intro l
    have hsub : x3 l ⊆
        {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true} ∪
        {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true} := by
      intro p hp
      have hev := hRight l p hp
      rw [heval_or {p} {l}, Bool.or_eq_true] at hev
      rw [Finset.mem_union]
      rcases hev with ha | hb
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, ha⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hp, hb⟩)
    exact Nat.le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hsum_split :
      x2 * (x1 + (1 : ℕ)) ≤
      (∑ l : Fin x2, {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}.card) +
      (∑ l : Fin x2, {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}.card) := by
    have htot : ∑ l : Fin x2, (x3 l).card = x2 * (x1 + (1 : ℕ)) := by
      simp [hLine]
    rw [← htot, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun l _ => hline_split l
  have hUncovInst := hUncov x1 x2 x3 (by omega) hx2 hLine
  by_cases hA : x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ l : Fin x2, {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD a false = true}.card
  · exact hHalfWireLB x1 x2 x3 x4 a hx1 hx2 hLine hUniq hUncovInst hAO haGe haLt houtHi hSafe_a hA
  · have hB : x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ l : Fin x2, {p ∈ x3 l | (x4.wires (PEqualNP.GenericRejection.incidenceInput {p} {l})).getD b false = true}.card := by
      omega
    exact hHalfWireLB x1 x2 x3 x4 b hx1 hx2 hLine hUniq hUncovInst hAO hbGe hbLt houtHi hSafe_b hB
