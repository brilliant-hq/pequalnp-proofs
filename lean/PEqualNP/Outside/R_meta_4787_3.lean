import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4787_3
    (normalize :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
          (∀ i : Fin D.gates.length, (D.gates.get i).inputs.length = 2 ∧
            ∀ j ∈ (D.gates.get i).inputs, j < 28 + i.val) ∧
          ∀ x : Fin 26 → Bool,
            D.wires (List.ofFn x ++ [true, false]) = C.wires (List.ofFn x ++ [true, false]))
    (clean_reduction :
      let x3 : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let x4 : Finset (Fin 13) → Fin 13 → Prop := fun P l => ∀ p ∈ P, ¬x3 p l
      let x6 : Fin 13 → Fin 13 → Fin 26 → Bool := fun p l i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      let x7 : Finset (Fin 13) → Fin 26 → Bool := fun P i =>
        decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ x4 P l)
      let x8 : Finset (Fin 13) → Prop := fun P =>
        (∀ p ∉ P, ∃ l, x4 P l ∧ x3 p l) ∧ ((∃ l, ∀ p ∈ P, x3 p l) ∨ ∃ p, ∀ l, x4 P l → x3 p l)
      let ok (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) :=
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 60 ∧
        (∀ i : Fin D.gates.length, (D.gates.get i).inputs.length = 2 ∧
          ∀ j ∈ (D.gates.get i).inputs, j < 28 + i.val) ∧
        a < 28 + D.size ∧ b < 28 + D.size ∧
        (let val := fun i x => (D.wires (List.ofFn x ++ [true, false])).getD i false
         (∀ p l, x3 p l → (val a (x6 p l) || val b (x6 p l)) = true) ∧
         (∀ P, x8 P → (val a (x7 P) || val b (x7 P)) = false))
      ∀ C a b, ok C a b →
        ∃ D a' b', ok D a' b' ∧
          ∀ i : Fin D.gates.length, (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ P, x8 P → (D.wires (List.ofFn (x7 P) ++ [true, false])).getD (28 + i.val) false = false) :
    (let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     x9.size ≤ (60 : ℕ) →       have x12 : ℕ → x5 → Bool := fun (x12 : ℕ) (x13 : x5) => (x9.wires (List.ofFn x13 ++ [Bool.true, Bool.false])).getD x12 Bool.false;       have x13 : (x5 → Bool) → Prop := fun (x13 : x5 → Bool) => ∀ (x14 x15 : x1), x3 x14 x15 → x13 (x6 x14 x15) = Bool.true;       ∀ (x14 x15 : ℕ), (x13 fun (x16 : x5) => x12 x14 x16 || x12 x15 x16) → ¬x13 (x12 x14) → ¬x13 (x12 x15) → (∀ (x19 : Finset x1), x8 x19 → ¬(x12 x14 (x7 x19) || x12 x15 (x7 x19)) = Bool.true) → False) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 C hMono hSize val inc a b hUnion hNa hNb hReject
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [List.length_append]
      omega
  have hwires_len : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 26 → Bool),
      (E.wires (List.ofFn x ++ [true, false])).length = 28 + E.size := by
    intro E x
    change (E.gates.foldl _ (List.ofFn x ++ [true, false])).length = 28 + E.gates.length
    rw [hfold_len]
    simp
  have hbeyond : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ),
      28 + E.size ≤ i → ∀ (x : Fin 26 → Bool), (E.wires (List.ofFn x ++ [true, false])).getD i false = false := by
    intro E i hi x
    rw [List.getD, List.getElem?_eq_none (by rw [hwires_len]; exact hi)]
    rfl
  have ha_lt : a < 28 + C.size := by
    by_contra! h
    apply hNb
    intro p l hp
    have h0 : val a (x6 p l) = false := hbeyond C a h (x6 p l)
    have hu := hUnion p l hp
    dsimp only [val] at h0 hu ⊢
    rw [h0, Bool.false_or] at hu
    exact hu
  have hb_lt : b < 28 + C.size := by
    by_contra! h
    apply hNa
    intro p l hp
    have h0 : val b (x6 p l) = false := hbeyond C b h (x6 p l)
    have hu := hUnion p l hp
    dsimp only [val] at h0 hu ⊢
    rw [h0, Bool.or_false] at hu
    exact hu
  obtain ⟨D0, hD0Mono, hD0Size, hD0Shape, hD0Wires⟩ := normalize C hMono
  have hD0_ok : D0.size ≤ 60 := hD0Size ▸ hSize
  have ha0_lt : a < 28 + D0.size := hD0Size ▸ ha_lt
  have hb0_lt : b < 28 + D0.size := hD0Size ▸ hb_lt
  have hx3_iff : ∀ p l : Fin 13, x3 p l ↔ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) := by
    intro p l
    dsimp only [x3, x2]
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, add_zero]
  obtain ⟨D, a', b', ⟨hDMono, hDSize, hDShape, ha', hb', hUnion', hReject'⟩, hClean⟩ :=
    clean_reduction D0 a b (by
      refine ⟨hD0Mono, hD0Size ▸ hSize, hD0Shape, ha0_lt, hb0_lt, ?_, ?_⟩
      · intro p l hp
        have heq : (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = x6 p l := rfl
        dsimp only
        rw [heq, hD0Wires]
        exact hUnion p l ((hx3_iff p l).mpr hp)
      · intro P hP
        have hP' : x8 P := by simpa only [x8, x4, hx3_iff] using hP
        have heq : (fun i : Fin 26 => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ P, ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9))) = x7 P := by
          funext i; dsimp only [x7, x4]; apply decide_eq_decide.mpr; simp only [hx3_iff]; exact Iff.rfl
        dsimp only
        rw [heq, hD0Wires]
        cases h : (val a (x7 P) || val b (x7 P)) with
        | false => exact rfl
        | true => exact False.elim (hReject P hP' h))
  -- Geometry facts
  have hEmpty : x8 ∅ := by
    refine ⟨fun p _ => ⟨p, fun _ h => False.elim (Finset.notMem_empty _ h), ⟨0, by decide, by simp⟩⟩,
      Or.inl ⟨0, fun _ h => False.elim (Finset.notMem_empty _ h)⟩⟩
  have hSingle_aux : ∀ a : Fin 13, a ≠ 0 → ∃ l : Fin 13,
      ¬(a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9) ∧ (0 = l ∨ 0 = l + 1 ∨ 0 = l + 3 ∨ 0 = l + 9) := by
    have hall : (List.finRange 13).all (fun a =>
        if a ≠ 0 then ([0, 12, 10, 4] : List (Fin 13)).any (fun l =>
          !(decide (a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9)) &&
          decide (0 = l ∨ 0 = l + 1 ∨ 0 = l + 3 ∨ 0 = l + 9)) else true) = true := by decide +kernel
    intro a ha
    have h1 := List.all_eq_true.mp hall a (List.mem_finRange a)
    rw [if_pos ha, List.any_eq_true] at h1
    obtain ⟨l, _, hl⟩ := h1
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hl
    exact ⟨l, hl⟩
  have hSingle : ∀ p : Fin 13, x8 {p} := by
    intro p
    refine ⟨fun q hq => ?_, Or.inl ⟨p, fun r hr => by rw [Finset.mem_singleton.mp hr]; exact ⟨0, by decide, by simp⟩⟩⟩
    obtain ⟨l, hnl, hql⟩ := hSingle_aux (p - q) (sub_ne_zero.mpr (fun h => hq (Finset.mem_singleton.mpr h.symm)))
    refine ⟨l + q, fun r hr => ?_, (hx3_iff q (l + q)).mpr ?_⟩
    · rw [Finset.mem_singleton.mp hr, hx3_iff]
      intro h; apply hnl
      rcases h with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
        (have h' := congrArg (· - q) h; abel_nf at h' ⊢; exact h')
    · rcases hql with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
        (have h' := congrArg (· + q) h; abel_nf at h' ⊢; exact h')
  have hAvoidLine_aux : ∀ a : Fin 13, a ≠ 0 → ∃ p : Fin 13,
      ¬(p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9) ∧ (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9) := by
    have hall : (List.finRange 13).all (fun a =>
        if a ≠ 0 then ([0, 1, 3, 9] : List (Fin 13)).any (fun p =>
          !(decide (p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9)) &&
          decide (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9)) else true) = true := by decide +kernel
    intro a ha
    have h1 := List.all_eq_true.mp hall a (List.mem_finRange a)
    rw [if_pos ha, List.any_eq_true] at h1
    obtain ⟨p, _, hp⟩ := h1
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hp
    exact ⟨p, hp⟩
  have hAvoidLine : ∀ l : Fin 13, x8 (Finset.univ.filter (fun p : Fin 13 => ¬x3 p l)) := by
    intro l
    refine ⟨fun q hq => ?_, Or.inr ⟨l, fun l' hl' => ?_⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hq
      exact ⟨l, fun p hp => (Finset.mem_filter.mp hp).2, hq⟩
    · by_contra hnl
      have hne : l - l' ≠ 0 := sub_ne_zero.mpr (fun h => hnl (by rw [h]; exact ⟨0, by decide, by simp⟩))
      obtain ⟨p, hpl, hpl'⟩ := hAvoidLine_aux (l - l') hne
      refine hl' (p + l') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩) ((hx3_iff (p + l') l').mpr ?_)
      · rw [hx3_iff]; intro h; apply hpl
        rcases h with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
          (have h' := congrArg (· - l') h; abel_nf at h' ⊢; exact h')
      · rcases hpl' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
          (rw [h]; abel_nf)
  have hPairPt_line_0 : ∀ a : Fin 13, a ≠ 0 → ∃ l : Fin 13,
      (a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9) ∧ (0 = l ∨ 0 = l + 1 ∨ 0 = l + 3 ∨ 0 = l + 9) := by
    have hall : (List.finRange 13).all (fun a =>
        if a ≠ 0 then ([0, 12, 10, 4] : List (Fin 13)).any (fun l =>
          decide (a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9) &&
          decide (0 = l ∨ 0 = l + 1 ∨ 0 = l + 3 ∨ 0 = l + 9)) else true) = true := by decide +kernel
    intro a ha
    have h1 := List.all_eq_true.mp hall a (List.mem_finRange a)
    rw [if_pos ha, List.any_eq_true] at h1
    obtain ⟨l, _, hl⟩ := h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    exact ⟨l, hl⟩
  have hPairPt_ext_0 : ∀ a b : Fin 13, a ≠ 0 → b ≠ 0 → ∃ l : Fin 13,
      ¬(a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9) ∧
      ¬(b = l ∨ b = l + 1 ∨ b = l + 3 ∨ b = l + 9) ∧
      (0 = l ∨ 0 = l + 1 ∨ 0 = l + 3 ∨ 0 = l + 9) := by
    have hall : (List.finRange 13).all (fun a => (List.finRange 13).all (fun b =>
        if a ≠ 0 ∧ b ≠ 0 then ([0, 12, 10, 4] : List (Fin 13)).any (fun l =>
          !(decide (a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9)) &&
          !(decide (b = l ∨ b = l + 1 ∨ b = l + 3 ∨ b = l + 9)) &&
          decide (0 = l ∨ 0 = l + 1 ∨ 0 = l + 3 ∨ 0 = l + 9)) else true)) = true := by decide +kernel
    intro a b ha hb
    have h1 := List.all_eq_true.mp hall a (List.mem_finRange a)
    have h2 := List.all_eq_true.mp h1 b (List.mem_finRange b)
    rw [if_pos ⟨ha, hb⟩, List.any_eq_true] at h2
    obtain ⟨l, _, hl⟩ := h2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hl
    exact ⟨l, hl.1.1, hl.1.2, hl.2⟩
  have hPairPt : ∀ p1 p2 : Fin 13, p1 ≠ p2 → x8 {p1, p2} := by
    intro p1 p2 hne
    obtain ⟨l0', hl1', hl2'⟩ := hPairPt_line_0 (p1 - p2) (sub_ne_zero.mpr hne)
    refine ⟨fun q hq => ?_, Or.inl ⟨l0' + p2, fun r hr => ?_⟩⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      obtain ⟨l, h1, h2, hq'⟩ := hPairPt_ext_0 (p1 - q) (p2 - q) (sub_ne_zero.mpr (Ne.symm hq.1)) (sub_ne_zero.mpr (Ne.symm hq.2))
      refine ⟨l + q, fun r hr => ?_, (hx3_iff q (l + q)).mpr ?_⟩
      · rcases Finset.mem_insert.mp hr with rfl | hr
        · rw [hx3_iff]; intro h; apply h1; rcases h with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;> (have h' := congrArg (· - q) h; abel_nf at h' ⊢; exact h')
        · rw [Finset.mem_singleton.mp hr, hx3_iff]; intro h; apply h2; rcases h with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;> (have h' := congrArg (· - q) h; abel_nf at h' ⊢; exact h')
      · rcases hq' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;> (have h' := congrArg (· + q) h; abel_nf at h' ⊢; exact h')
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · rw [hx3_iff]; rcases hl1' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
          (have h' := congrArg (· + p2) h; abel_nf at h' ⊢; exact h')
      · rw [Finset.mem_singleton.mp hr, hx3_iff]; rcases hl2' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
          (have h' := congrArg (· + p2) h; abel_nf at h' ⊢; exact h')
  have hPairLine_pt_0 : ∀ a : Fin 13, 0 ≠ a → ∃ p : Fin 13,
      (p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9) ∧ (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9) := by
    have hall : (List.finRange 13).all (fun a =>
        if 0 ≠ a then ([0, 1, 3, 9] : List (Fin 13)).any (fun p =>
          decide (p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9) &&
          decide (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9)) else true) = true := by decide +kernel
    intro a ha
    have h1 := List.all_eq_true.mp hall a (List.mem_finRange a)
    rw [if_pos ha, List.any_eq_true] at h1
    obtain ⟨p, _, hp⟩ := h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨p, hp⟩
  have hPairLine_ext_0 : ∀ a b : Fin 13, 0 ≠ a → 0 ≠ b → ∃ p : Fin 13,
      ¬(p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9) ∧
      ¬(p = b ∨ p = b + 1 ∨ p = b + 3 ∨ p = b + 9) ∧
      (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9) := by
    have hall : (List.finRange 13).all (fun a => (List.finRange 13).all (fun b =>
        if 0 ≠ a ∧ 0 ≠ b then ([0, 1, 3, 9] : List (Fin 13)).any (fun p =>
          !(decide (p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9)) &&
          !(decide (p = b ∨ p = b + 1 ∨ p = b + 3 ∨ p = b + 9)) &&
          decide (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9)) else true)) = true := by decide +kernel
    intro a b ha hb
    have h1 := List.all_eq_true.mp hall a (List.mem_finRange a)
    have h2 := List.all_eq_true.mp h1 b (List.mem_finRange b)
    rw [if_pos ⟨ha, hb⟩, List.any_eq_true] at h2
    obtain ⟨p, _, hp⟩ := h2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hp
    exact ⟨p, hp.1.1, hp.1.2, hp.2⟩
  have hPairLine : ∀ l1 l2 : Fin 13, l1 ≠ l2 → x8 (Finset.univ.filter (fun p : Fin 13 => ¬x3 p l1 ∧ ¬x3 p l2)) := by
    intro l1 l2 hne
    obtain ⟨p0', hp1', hp2'⟩ := hPairLine_pt_0 (l1 - l2) (sub_ne_zero.mpr hne).symm
    refine ⟨fun q hq => ?_, Or.inr ⟨p0' + l2, fun l' hl' => ?_⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hq
      by_cases h1 : x3 q l1
      · exact ⟨l1, fun p hp => (Finset.mem_filter.mp hp).2.1, h1⟩
      · exact ⟨l2, fun p hp => (Finset.mem_filter.mp hp).2.2, hq h1⟩
    · by_cases h1 : l' = l1
      · rw [h1, hx3_iff]; rcases hp1' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
          (have h' := congrArg (· + l2) h; abel_nf at h' ⊢; exact h')
      · by_cases h2 : l' = l2
        · rw [h2, hx3_iff]; rcases hp2' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;>
            (rw [h]; abel_nf)
        · obtain ⟨p, hn1, hn2, hp'⟩ := hPairLine_ext_0 (l1 - l') (l2 - l') (sub_ne_zero.mpr (Ne.symm h1)).symm (sub_ne_zero.mpr (Ne.symm h2)).symm
          refine False.elim (hl' (p + l') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩) ((hx3_iff (p + l') l').mpr ?_))
          · rw [hx3_iff]; intro h; apply hn1; rcases h with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;> (have h' := congrArg (· - l') h; abel_nf at h' ⊢; exact h')
          · rw [hx3_iff]; intro h; apply hn2; rcases h with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;> (have h' := congrArg (· - l') h; abel_nf at h' ⊢; exact h')
          · rcases hp' with h | h | h | h <;> [left; right; right; right] <;> [skip; left; (right; left); (right; right)] <;> (rw [h]; abel_nf)
  have hSidon4 : ∀ i1 i2 i3 i4 : Fin 4,
      let f : Fin 4 → Fin 13 := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 9
      f i1 - f i2 = f i3 - f i4 → f i1 ≠ f i2 → f i1 = f i3 := by
    have hall : (List.finRange 4).all (fun i1 => (List.finRange 4).all (fun i2 =>
        (List.finRange 4).all (fun i3 => (List.finRange 4).all (fun i4 =>
        let f : Fin 4 → Fin 13 := fun i => match i with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 9
        if f i1 - f i2 = f i3 - f i4 ∧ f i1 ≠ f i2 then decide (f i1 = f i3) else true)))) = true := by decide +kernel
    intro i1 i2 i3 i4 f heq hne
    have h1 := List.all_eq_true.mp hall i1 (List.mem_finRange i1)
    have h2 := List.all_eq_true.mp h1 i2 (List.mem_finRange i2)
    have h3 := List.all_eq_true.mp h2 i3 (List.mem_finRange i3)
    have h4 := List.all_eq_true.mp h3 i4 (List.mem_finRange i4)
    rw [if_pos ⟨heq, hne⟩, decide_eq_true_eq] at h4
    exact h4
  have hSidon : ∀ d1 d2 d3 d4 : Fin 13,
      (d1 = 0 ∨ d1 = 1 ∨ d1 = 3 ∨ d1 = 9) → (d2 = 0 ∨ d2 = 1 ∨ d2 = 3 ∨ d2 = 9) →
      (d3 = 0 ∨ d3 = 1 ∨ d3 = 3 ∨ d3 = 9) → (d4 = 0 ∨ d4 = 1 ∨ d4 = 3 ∨ d4 = 9) →
      d1 - d2 = d3 - d4 → d1 ≠ d2 → d1 = d3 := by
    intro d1 d2 d3 d4 hd1 hd2 hd3 hd4 heq hne
    have hidx : ∀ d : Fin 13, (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9) →
        ∃ i : Fin 4, d = match i with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 9 := by
      intro d hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    obtain ⟨i1, rfl⟩ := hidx d1 hd1
    obtain ⟨i2, rfl⟩ := hidx d2 hd2
    obtain ⟨i3, rfl⟩ := hidx d3 hd3
    obtain ⟨i4, rfl⟩ := hidx d4 hd4
    exact hSidon4 i1 i2 i3 i4 heq hne
  have hNoC4 : ∀ p1 p2 l1 l2 : Fin 13, p1 ≠ p2 → l1 ≠ l2 → x3 p1 l1 → x3 p2 l2 → ¬x3 p1 l2 ∨ ¬x3 p2 l1 := by
    intro p1 p2 l1 l2 hp hl h11 h22
    by_contra! h
    rcases h with ⟨h12, h21⟩
    obtain ⟨d1, hd1, e1⟩ := h11
    obtain ⟨d2, hd2, e2⟩ := h22
    obtain ⟨d3, hd3, e3⟩ := h12
    obtain ⟨d4, hd4, e4⟩ := h21
    simp only [x2, Finset.mem_insert, Finset.mem_singleton] at hd1 hd2 hd3 hd4
    have heq : d1 - d3 = d4 - d2 := by
      have ha : l1 + d1 = l2 + d3 := e1.symm.trans e3
      have hb : l1 + d4 = l2 + d2 := e4.symm.trans e2
      have hsub := congrArg (· + d4 - d3) (congrArg₂ (· - ·) ha hb)
      abel_nf at hsub ⊢
      exact hsub
    have hne : d1 ≠ d3 := fun h => hl (by
      have : l1 + d1 = l2 + d3 := e1.symm.trans e3
      rw [h] at this; exact add_right_cancel this)
    have h13 := hSidon d1 d3 d4 d2 hd1 hd3 hd4 hd2 heq hne
    exact hp (by rw [e1, e4, h13])
  -- Wire evaluation & monotonicity on D
  let valD : ℕ → (Fin 26 → Bool) → Bool := fun i x => (D.wires (List.ofFn x ++ [true, false])).getD i false
  have hfold_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length →
      (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih _ i (by simp [List.length_append]; omega)]
      rw [List.getD, List.getD, List.getElem?_append_left hi]
  have hvalD_lt : ∀ (i : ℕ) (hi : i < 26) (x : Fin 26 → Bool), valD i x = x ⟨i, hi⟩ := by
    intro i hi x
    dsimp only [valD, PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [hfold_prefix _ _ _ (by simp; omega)]
    rw [List.getD, List.getElem?_append_left (by simp; omega), List.getElem?_ofFn, dite_eq_left]
    rfl
  have hvalD_26 : ∀ x : Fin 26 → Bool, valD 26 x = true := by
    intro x
    dsimp only [valD, PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [hfold_prefix _ _ _ (by simp)]
    simp [List.getD]
  have hvalD_27 : ∀ x : Fin 26 → Bool, valD 27 x = false := by
    intro x
    dsimp only [valD, PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [hfold_prefix _ _ _ (by simp)]
    simp [List.getD]
  have hfold_take : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) w).getD (w.length + k) false =
      let wk := (gs.take k).foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) w
      (gs[k]).op.eval ((gs[k]).inputs.map fun j => wk.getD j false) := by
    intro gs
    induction gs with
    | nil => intro _ _ hk; simp at hk
    | cons g gs ih =>
      intro w k hk
      cases k with
      | zero =>
        simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero, Nat.add_zero]
        rw [hfold_prefix _ _ _ (by simp)]
        simp [List.getD]
      | succ k =>
        simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
        have hk' : k < gs.length := Nat.lt_of_succ_lt_succ hk
        have h := ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) k hk'
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        rw [show w.length + (k + 1) = w.length + 1 + k by omega]
        exact h
  have hvalD_gate : ∀ (k : Fin D.gates.length) (x : Fin 26 → Bool),
      valD (28 + k.val) x =
      (D.gates.get k).op.eval ((D.gates.get k).inputs.map fun j => valD j x) := by
    intro k x
    dsimp only [valD, PEqualNP.CircuitLowerBounds.Circuit.wires]
    have hlen : (List.ofFn x ++ [true, false]).length = 28 := by simp
    have ht := hfold_take D.gates (List.ofFn x ++ [true, false]) k.val k.isLt
    rw [hlen] at ht
    rw [ht]
    simp only [List.get_eq_getElem]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hjlt : j < 28 + k.val := (hDShape k).2 j hj
    have hsplit : D.gates = D.gates.take k.val ++ D.gates.drop k.val := (List.take_append_drop k.val D.gates).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    symm
    apply hfold_prefix
    rw [hfold_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt k.isLt), hlen]
    exact hjlt
  have hmonoD : ∀ (i : ℕ) (x y : Fin 26 → Bool),
      (∀ q : Fin 26, x q = true → y q = true) → valD i x = true → valD i y = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x y hxy hix
      by_cases hi26 : i < 26
      · rw [hvalD_lt i hi26 x] at hix
        rw [hvalD_lt i hi26 y]
        exact hxy ⟨i, hi26⟩ hix
      · by_cases hi26eq : i = 26
        · subst hi26eq; rw [hvalD_26]
        · by_cases hi27eq : i = 27
          · subst hi27eq; rw [hvalD_27] at hix ⊢; exact hix
          · have hi28 : 28 ≤ i := by omega
            by_cases hilen : i - 28 < D.gates.length
            · let k : Fin D.gates.length := ⟨i - 28, hilen⟩
              have hik : i = 28 + k.val := by dsimp [k]; omega
              rw [hik, hvalD_gate k x] at hix
              rw [hik, hvalD_gate k y]
              obtain ⟨hlen2, hbd⟩ := hDShape k
              have hop := (hDMono (D.gates.get k) (List.get_mem _ _)).1
              cases hge : (D.gates.get k).inputs with
              | nil => rw [hge] at hlen2; simp at hlen2
              | cons u t =>
                cases t with
                | nil => rw [hge] at hlen2; simp at hlen2
                | cons v t2 =>
                  cases t2 with
                  | cons _ _ => rw [hge] at hlen2; simp at hlen2
                  | nil =>
                    have hbd' : ∀ j ∈ [u, v], j < 28 + k.val := by rw [← hge]; exact hbd
                    have hu : u < i := by rw [hik]; exact hbd' u (by simp)
                    have hv : v < i := by rw [hik]; exact hbd' v (by simp)
                    rw [hge] at hix
                    rcases hop with hand | hor
                    · simp only [hand, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
                        List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hix ⊢
                      exact ⟨ih u hu x y hxy hix.1, ih v hv x y hxy hix.2⟩
                    · rw [Set.mem_singleton_iff] at hor
                      simp only [hor, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
                        List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hix ⊢
                      rcases hix with hix | hix
                      · left; exact ih u hu x y hxy hix
                      · right; exact ih v hv x y hxy hix
            · have hge : 28 + D.size ≤ i := by change 28 + D.gates.length ≤ i; omega
              have h0 : valD i x = false := hbeyond D i hge x
              rw [h0] at hix; cases hix
  -- OR-cone via fuel
  let orReachFuel : ℕ → ℕ → Finset ℕ := fun fuel =>
    Nat.rec (fun w => {w}) (fun _ rec w =>
      if h : 28 ≤ w ∧ w - 28 < D.gates.length then
        let k : Fin D.gates.length := ⟨w - 28, h.2⟩
        match (D.gates.get k).op with
        | PEqualNP.CircuitLowerBounds.GateOp.or =>
          let inps := (D.gates.get k).inputs
          have hinps_len : inps.length = 2 := (hDShape k).1
          insert w (rec (inps[0]'(by omega)) ∪ rec (inps[1]'(by omega)))
        | _ => {w}
      else {w}) fuel
  let orReach : ℕ → Finset ℕ := fun w => orReachFuel w w
  have horReach_fuel_eq : ∀ fuel1 fuel2 w, w ≤ fuel1 → w ≤ fuel2 → orReachFuel fuel1 w = orReachFuel fuel2 w := by
    intro fuel1
    induction fuel1 with
    | zero =>
      intro fuel2 w hw1 _
      have hw0 : w = 0 := by omega
      subst hw0
      cases fuel2 <;> simp [orReachFuel]
    | succ fuel1 ih =>
      intro fuel2 w hw1 hw2
      cases fuel2 with
      | zero =>
        have hw0 : w = 0 := by omega
        subst hw0; simp [orReachFuel]
      | succ fuel2 =>
        dsimp only [orReachFuel]
        split_ifs with h
        · cases hop : (D.gates.get ⟨w - 28, h.2⟩).op <;> try rfl
          dsimp only
          let k : Fin D.gates.length := ⟨w - 28, h.2⟩
          have hinps_len : (D.gates.get k).inputs.length = 2 := (hDShape k).1
          have h28 : 28 ≤ w := h.1
          have hk_eq : 28 + k.val = w := by change 28 + (w - 28) = w; omega
          have hu : (D.gates.get k).inputs[0]'(by omega) < w := by
            have := (hDShape k).2 ((D.gates.get k).inputs[0]'(by omega)) (List.getElem_mem _)
            rw [hk_eq] at this; exact this
          have hv : (D.gates.get k).inputs[1]'(by omega) < w := by
            have := (hDShape k).2 ((D.gates.get k).inputs[1]'(by omega)) (List.getElem_mem _)
            rw [hk_eq] at this; exact this
          dsimp only [k] at hu hv
          change insert w (orReachFuel fuel1 _ ∪ orReachFuel fuel1 _) = insert w (orReachFuel fuel2 _ ∪ orReachFuel fuel2 _)
          rw [ih fuel2 _ (by omega) (by omega), ih fuel2 _ (by omega) (by omega)]
        · rfl
  have horReach_mem_self : ∀ w, w ∈ orReach w := by
    intro w
    dsimp only [orReach]
    cases w with
    | zero => simp [orReachFuel]
    | succ w =>
      dsimp only [orReachFuel]
      split_ifs with h
      · cases hop : (D.gates.get ⟨w + 1 - 28, h.2⟩).op <;> simp
      · simp
  have horReach_sound : ∀ w < 28 + D.size, ∀ x : Fin 26 → Bool, valD w x = true →
      ∃ j ∈ orReach w,
        (j < 28 ∨ ∃ k : Fin D.gates.length, j = 28 + k.val ∧ (D.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        valD j x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw x hwx
      by_cases hw28 : w < 28
      · have hzero : orReach w = {w} := by
          dsimp only [orReach]
          cases w with
          | zero => simp [orReachFuel]
          | succ w' => dsimp only [orReachFuel]; rw [dif_neg (by omega)]
        rw [hzero]
        exact ⟨w, Finset.mem_singleton_self w, Or.inl hw28, hwx⟩
      · have hlen : w - 28 < D.gates.length := by change w < 28 + D.gates.length at hw; omega
        have hcond : 28 ≤ w ∧ w - 28 < D.gates.length := ⟨by omega, hlen⟩
        let k : Fin D.gates.length := ⟨w - 28, hlen⟩
        have hwk : w = 28 + k.val := by change w = 28 + (w - 28); omega
        have hop := (hDMono (D.gates.get k) (List.get_mem _ _)).1
        have hwpos : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        obtain ⟨w', hw'⟩ := hwpos
        have hor_unfold : orReach w =
            match (D.gates.get k).op with
            | PEqualNP.CircuitLowerBounds.GateOp.or =>
              let inps := (D.gates.get k).inputs
              have hinps_len : inps.length = 2 := (hDShape k).1
              insert w (orReach (inps[0]'(by omega)) ∪ orReach (inps[1]'(by omega)))
            | _ => {w} := by
          dsimp only [orReach]
          conv_lhs => rw [hw']; dsimp only [orReachFuel]; rw [dif_pos (by omega)]; simp only [← hw']
          cases hop' : (D.gates.get k).op with
          | or =>
            have hinps_len : (D.gates.get k).inputs.length = 2 := (hDShape k).1
            have hu : (D.gates.get k).inputs[0]'(by omega) < w := by
              have := (hDShape k).2 ((D.gates.get k).inputs[0]'(by omega)) (List.getElem_mem _)
              rw [← hwk] at this; exact this
            have hv : (D.gates.get k).inputs[1]'(by omega) < w := by
              have := (hDShape k).2 ((D.gates.get k).inputs[1]'(by omega)) (List.getElem_mem _)
              rw [← hwk] at this; exact this
            dsimp only
            congr 1; congr 1
            · exact horReach_fuel_eq w' _ _ (Nat.le_of_lt_succ (lt_of_lt_of_eq hu hw')) (le_refl _)
            · exact horReach_fuel_eq w' _ _ (Nat.le_of_lt_succ (lt_of_lt_of_eq hv hw')) (le_refl _)
          | _ => dsimp only
        rcases hop with hand | hor
        · rw [hor_unfold, hand]
          exact ⟨w, Finset.mem_singleton_self w, Or.inr ⟨k, hwk, hand⟩, hwx⟩
        · rw [Set.mem_singleton_iff] at hor
          rw [hor_unfold, hor]
          have hlen2 := (hDShape k).1
          let u := (D.gates.get k).inputs[0]'(by omega)
          let v := (D.gates.get k).inputs[1]'(by omega)
          have hu : u < w := by have := (hDShape k).2 u (List.getElem_mem _); rw [← hwk] at this; exact this
          have hv : v < w := by have := (hDShape k).2 v (List.getElem_mem _); rw [← hwk] at this; exact this
          have hvalw := hvalD_gate k x
          rw [← hwk, hwx, hor] at hvalw
          have hinps : (D.gates.get k).inputs = [u, v] := by
            have hlist2 : ∀ (l : List ℕ) (hl : l.length = 2), l = [l[0]'(by omega), l[1]'(by omega)] := by
              intro l hl; rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hl ⊢
            exact hlist2 _ hlen2
          rw [hinps] at hvalw
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false] at hvalw
          rcases (Bool.or_eq_true _ _).mp hvalw.symm with huval | hvval
          · obtain ⟨j, hjmem, hjkind, hjval⟩ := ih u hu (by omega) x huval
            exact ⟨j, Finset.mem_insert_of_mem (Finset.mem_union_left _ hjmem), hjkind, hjval⟩
          · obtain ⟨j, hjmem, hjkind, hjval⟩ := ih v hv (by omega) x hvval
            exact ⟨j, Finset.mem_insert_of_mem (Finset.mem_union_right _ hjmem), hjkind, hjval⟩
  have horReach_mono : ∀ w j, j ∈ orReach w → ∀ x : Fin 26 → Bool, valD j x = true → valD w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj x hjx
      by_cases hcond : 28 ≤ w ∧ w - 28 < D.gates.length
      · let k : Fin D.gates.length := ⟨w - 28, hcond.2⟩
        have hwk : w = 28 + k.val := by change w = 28 + (w - 28); omega
        have hwpos : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        obtain ⟨w', hw'⟩ := hwpos
        have h1 : orReach w = orReachFuel (w' + 1) w := by dsimp only [orReach]; rw [← hw']
        rw [h1] at hj; dsimp only [orReachFuel] at hj; rw [dif_pos (by omega)] at hj
        cases hop : (D.gates.get k).op with
        | or =>
          have hlen2 := (hDShape k).1
          let u := (D.gates.get k).inputs[0]'(by omega)
          let v := (D.gates.get k).inputs[1]'(by omega)
          have hu : u < w := by have := (hDShape k).2 u (List.getElem_mem _); rw [← hwk] at this; exact this
          have hv : v < w := by have := (hDShape k).2 v (List.getElem_mem _); rw [← hwk] at this; exact this
          simp only [k, hop] at hj
          change _ ∈ insert w (orReachFuel w' _ ∪ orReachFuel w' _) at hj
          rw [horReach_fuel_eq w' u u (by omega) (le_refl _), horReach_fuel_eq w' v v (by omega) (le_refl _)] at hj
          simp only [Finset.mem_insert, Finset.mem_union] at hj
          have hvalw := hvalD_gate k x
          rw [← hwk, hop] at hvalw
          have hinps : (D.gates.get k).inputs = [u, v] := by
            have hlist2 : ∀ (l : List ℕ) (hl : l.length = 2), l = [l[0]'(by omega), l[1]'(by omega)] := by
              intro l hl; rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hl ⊢
            exact hlist2 _ hlen2
          rw [hinps] at hvalw
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false] at hvalw
          rcases hj with rfl | hj | hj
          · exact hjx
          · rw [hvalw, ih u hu j hj x hjx, Bool.true_or]
          · rw [hvalw, ih v hv j hj x hjx, Bool.or_true]
        | _ =>
          simp only [k, hop, Finset.mem_singleton] at hj
          subst hj; exact hjx
      · have hzero : orReach w = {w} := by
          dsimp only [orReach]
          cases w with
          | zero => simp [orReachFuel]
          | succ w' => dsimp only [orReachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        rw [← hj]; exact hjx
  let sing : Fin 26 → Fin 26 → Bool := fun i j => decide (j = i)
  let Sings : ℕ → Finset (Fin 26) := fun w => Finset.univ.filter (fun i => valD w (sing i) = true)
  have hNoInputInCone : ∀ w, (∀ P : Finset (Fin 13), x8 P → valD w (x7 P) = false) →
      26 ∉ orReach w ∧ ∀ i : Fin 26, i.val ∉ orReach w := by
    intro w hw
    refine ⟨?_, ?_⟩
    · intro h26
      have h1 := horReach_mono w 26 h26 (x7 ∅) (hvalD_26 (x7 ∅))
      have h0 := hw ∅ hEmpty
      rw [h1] at h0; cases h0
    · intro i hi
      by_cases hi13 : i.val < 13
      · let p : Fin 13 := ⟨i.val, hi13⟩
        have hvalp : valD i.val (x7 {p}) = true := by
          rw [hvalD_lt i.val i.isLt (x7 {p})]
          dsimp only [x7]
          rw [decide_eq_true_eq]
          left; exact ⟨p, Finset.mem_singleton_self p, by ext; simp [p]⟩
        have h1 := horReach_mono w i.val hi (x7 {p}) hvalp
        have h0 := hw {p} (hSingle p)
        rw [h1] at h0; cases h0
      · let l : Fin 13 := ⟨i.val - 13, by omega⟩
        let P := Finset.univ.filter (fun p : Fin 13 => ¬x3 p l)
        have hvall : valD i.val (x7 P) = true := by
          rw [hvalD_lt i.val i.isLt (x7 P)]
          dsimp only [x7]
          rw [decide_eq_true_eq]
          right; refine ⟨l, ?_, fun p hp => (Finset.mem_filter.mp hp).2⟩
          ext; simp [l]; omega
        have h1 := horReach_mono w i.val hi (x7 P) hvall
        have h0 := hw P (hAvoidLine l)
        rw [h1] at h0; cases h0
  have hSings_and : ∀ k : Fin D.gates.length, (D.gates.get k).op = .and → Sings (28 + k.val) = ∅ := by
    intro k hk
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hi13 : i.val < 13
    · let p : Fin 13 := ⟨i.val, hi13⟩
      have hsub : ∀ q : Fin 26, sing i q = true → x7 {p} q = true := by
        intro q hq
        simp only [sing, decide_eq_true_eq] at hq
        subst hq
        dsimp only [x7]
        rw [decide_eq_true_eq]
        left; exact ⟨p, Finset.mem_singleton_self p, by ext; simp [p]⟩
      have h1 := hmonoD (28 + k.val) (sing i) (x7 {p}) hsub hi
      have h0 : valD (28 + k.val) (x7 {p}) = false := by
        have hS := hSingle p
        dsimp only [x8, x5, x4] at hS
        simp only [hx3_iff] at hS
        have hcl := hClean k hk {p} hS
        dsimp only at hcl
        have h7eq : (fun i : Fin 26 => decide ((∃ p_1 ∈ ({p} : Finset (Fin 13)), i = Fin.castAdd 13 p_1) ∨
            ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p_1 ∈ ({p} : Finset (Fin 13)), ¬(p_1 = l ∨ p_1 = l + 1 ∨ p_1 = l + 3 ∨ p_1 = l + 9))) = x7 {p} := by
          funext j; dsimp only [x7, x4]; simp only [hx3_iff]; exact decide_eq_decide.mpr Iff.rfl
        rw [h7eq] at hcl
        exact hcl
      rw [h1] at h0; cases h0
    · let l : Fin 13 := ⟨i.val - 13, by omega⟩
      let P := Finset.univ.filter (fun p : Fin 13 => ¬x3 p l)
      have hsub : ∀ q : Fin 26, sing i q = true → x7 P q = true := by
        intro q hq
        simp only [sing, decide_eq_true_eq] at hq
        subst hq
        dsimp only [x7]
        rw [decide_eq_true_eq]
        right; refine ⟨l, ?_, fun p hp => (Finset.mem_filter.mp hp).2⟩
        ext; simp [l]; omega
      have h1 := hmonoD (28 + k.val) (sing i) (x7 P) hsub hi
      have h0 : valD (28 + k.val) (x7 P) = false := by
        have hS := hAvoidLine l
        dsimp only [x8, x5, x4] at hS
        simp only [hx3_iff] at hS
        have hcl := hClean k hk _ hS
        dsimp only at hcl
        have h7eq : (fun i : Fin 26 => decide ((∃ p ∈ Finset.univ.filter (fun p : Fin 13 => ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)), i = Fin.castAdd 13 p) ∨
            ∃ l_1 : Fin 13, i = Fin.natAdd 13 l_1 ∧ ∀ p ∈ Finset.univ.filter (fun p : Fin 13 => ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)), ¬(p = l_1 ∨ p = l_1 + 1 ∨ p = l_1 + 3 ∨ p = l_1 + 9))) = x7 P := by
          funext j; dsimp only [x7, x4, P]; simp only [hx3_iff]; exact decide_eq_decide.mpr Iff.rfl
        rw [h7eq] at hcl
        exact hcl
      rw [h1] at h0; cases h0
  have hSings_lt : ∀ i : Fin 26, Sings i.val = {i} := by
    intro i; ext j
    simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hvalD_lt i.val i.isLt (sing j)]
    by_cases h : j = i <;> simp [h, sing, eq_comm]
  have hSings_27 : Sings 27 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and, hvalD_27] at hi
    cases hi
  have hSings_26 : Sings 26 = Finset.univ := by
    ext i; simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and, hvalD_26]
  have hSings_or : ∀ k : Fin D.gates.length, (D.gates.get k).op = .or →
      let inps := (D.gates.get k).inputs
      have hlen2 : inps.length = 2 := (hDShape k).1
      Sings (28 + k.val) = Sings (inps[0]'(by omega)) ∪ Sings (inps[1]'(by omega)) := by
    intro k hk inps hlen2
    ext i
    simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    have hval := hvalD_gate k (sing i)
    rw [hk] at hval
    have hlen_k : (D.gates.get k).inputs.length = 2 := (hDShape k).1
    have hinps : (D.gates.get k).inputs = [(D.gates.get k).inputs[0]'(by omega), (D.gates.get k).inputs[1]'(by omega)] := by
      have hlist2 : ∀ (l : List ℕ) (hl : l.length = 2), l = [l[0]'(by omega), l[1]'(by omega)] := by
        intro l hl; rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hl ⊢
      exact hlist2 _ hlen_k
    change valD (28 + k.val) (sing i) = _ at hval
    rw [hinps] at hval
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false] at hval
    dsimp only [inps]
    rw [hval, Bool.or_eq_true]
  let reachFuel : ℕ → ℕ → Finset ℕ := Nat.rec (fun w => {w}) (fun _ rec w =>
    if h : 28 ≤ w ∧ w - 28 < D.gates.length then
      let k : Fin D.gates.length := ⟨w - 28, h.2⟩
      let inps := (D.gates.get k).inputs
      have hinps_len : inps.length = 2 := (hDShape k).1
      insert w (rec (inps[0]'(by omega)) ∪ rec (inps[1]'(by omega)))
    else {w})
  let reach : ℕ → Finset ℕ := fun w => reachFuel w w
  have hreach_fuel_eq : ∀ fuel1 fuel2 w, w ≤ fuel1 → w ≤ fuel2 → reachFuel fuel1 w = reachFuel fuel2 w := by
    intro fuel1 fuel2 w hw1 hw2
    induction w using Nat.strong_induction_on generalizing fuel1 fuel2 with
    | ind w ih =>
      cases fuel1 with
      | zero =>
        obtain rfl : w = 0 := by omega
        cases fuel2 with
        | zero => rfl
        | succ f2 => dsimp only [reachFuel]; rw [dif_neg (by omega)]; rfl
      | succ f1 =>
        cases fuel2 with
        | zero =>
          obtain rfl : w = 0 := by omega
          dsimp only [reachFuel]; rw [dif_neg (by omega)]; rfl
        | succ f2 =>
          dsimp only [reachFuel]
          by_cases hcond : 28 ≤ w ∧ w - 28 < D.gates.length
          · rw [dif_pos hcond, dif_pos hcond]
            let k : Fin D.gates.length := ⟨w - 28, hcond.2⟩
            have hlen2 := (hDShape k).1
            have hk_eq : 28 + k.val = w := by change 28 + (w - 28) = w; omega
            have hu : (D.gates.get k).inputs[0]'(by omega) < w := by
              have := (hDShape k).2 ((D.gates.get k).inputs[0]'(by omega)) (List.getElem_mem _); rw [hk_eq] at this; exact this
            have hv : (D.gates.get k).inputs[1]'(by omega) < w := by
              have := (hDShape k).2 ((D.gates.get k).inputs[1]'(by omega)) (List.getElem_mem _); rw [hk_eq] at this; exact this
            congr 1; congr 1
            · exact ih _ hu f1 f2 (by omega) (by omega)
            · exact ih _ hv f1 f2 (by omega) (by omega)
          · rw [dif_neg hcond, dif_neg hcond]
  have hreach_mem_self : ∀ w, w ∈ reach w := by
    intro w
    cases w with
    | zero => simp [reach, reachFuel]
    | succ w' =>
      dsimp only [reach, reachFuel]
      by_cases hcond : 28 ≤ w' + 1 ∧ w' + 1 - 28 < D.gates.length
      · rw [dif_pos hcond]; exact Finset.mem_insert_self _ _
      · rw [dif_neg hcond]; exact Finset.mem_singleton_self _
  have horReach_sub_reach : ∀ w, orReach w ⊆ reach w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj
      by_cases hcond : 28 ≤ w ∧ w - 28 < D.gates.length
      · have hwpos : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        obtain ⟨w', hw'⟩ := hwpos
        have h1 : orReach w = orReachFuel (w' + 1) w := by dsimp only [orReach]; rw [← hw']
        rw [h1] at hj; dsimp only [orReachFuel] at hj; rw [dif_pos (by omega)] at hj
        have h2 : reach w = reachFuel (w' + 1) w := by dsimp only [reach]; rw [← hw']
        rw [h2]; dsimp only [reachFuel]; rw [dif_pos (by omega)]
        let k : Fin D.gates.length := ⟨w - 28, hcond.2⟩
        have hk_eq : 28 + k.val = w := by change 28 + (w - 28) = w; omega
        have hlen2 := (hDShape k).1
        let u := (D.gates.get k).inputs[0]'(by omega)
        let v := (D.gates.get k).inputs[1]'(by omega)
        have hu : u < w := by have := (hDShape k).2 u (List.getElem_mem _); rw [hk_eq] at this; exact this
        have hv : v < w := by have := (hDShape k).2 v (List.getElem_mem _); rw [hk_eq] at this; exact this
        change _ ∈ insert w (reachFuel w' _ ∪ reachFuel w' _)
        rw [hreach_fuel_eq w' u u (by omega) (le_refl _), hreach_fuel_eq w' v v (by omega) (le_refl _)]
        cases hop : (D.gates.get k).op with
        | or =>
          simp only [k, hop] at hj
          change _ ∈ insert w (orReachFuel w' _ ∪ orReachFuel w' _) at hj
          rw [horReach_fuel_eq w' u u (by omega) (le_refl _), horReach_fuel_eq w' v v (by omega) (le_refl _)] at hj
          simp only [Finset.mem_insert, Finset.mem_union] at hj ⊢
          rcases hj with rfl | hj | hj
          · left; rfl
          · right; left; exact ih u hu hj
          · right; right; exact ih v hv hj
        | _ =>
          simp only [k, hop, Finset.mem_singleton] at hj
          subst hj; exact Finset.mem_insert_self _ _
      · have hzero : orReach w = {w} := by
          dsimp only [orReach]
          cases w with
          | zero => simp [orReachFuel]
          | succ w' => dsimp only [orReachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        subst hj; exact hreach_mem_self _
  have hreach_unfold : ∀ w, (h : 28 ≤ w ∧ w - 28 < D.gates.length) →
      let kw : Fin D.gates.length := ⟨w - 28, h.2⟩
      have hlenw : (D.gates.get kw).inputs.length = 2 := (hDShape kw).1
      reach w = insert w (reach ((D.gates.get kw).inputs[0]'(by omega)) ∪ reach ((D.gates.get kw).inputs[1]'(by omega))) := by
    intro w h kw hlenw
    have hwpos : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    obtain ⟨w', hw'⟩ := hwpos
    have hkw_eq : 28 + kw.val = w := by change 28 + (w - 28) = w; omega
    have hu : (D.gates.get kw).inputs[0]'(by omega) < w := by
      have := (hDShape kw).2 ((D.gates.get kw).inputs[0]'(by omega)) (List.getElem_mem _); rw [hkw_eq] at this; exact this
    have hv : (D.gates.get kw).inputs[1]'(by omega) < w := by
      have := (hDShape kw).2 ((D.gates.get kw).inputs[1]'(by omega)) (List.getElem_mem _); rw [hkw_eq] at this; exact this
    have h1 : reach w = reachFuel (w' + 1) w := by dsimp only [reach]; rw [← hw']
    rw [h1]
    dsimp only [reachFuel]
    rw [dif_pos (by omega)]
    change insert w (reachFuel w' _ ∪ reachFuel w' _) = _
    rw [hreach_fuel_eq w' ((D.gates.get kw).inputs[0]'(by omega)) ((D.gates.get kw).inputs[0]'(by omega)) (by omega) (le_refl _),
        hreach_fuel_eq w' ((D.gates.get kw).inputs[1]'(by omega)) ((D.gates.get kw).inputs[1]'(by omega)) (by omega) (le_refl _)]
  have hreach_le : ∀ w j, j ∈ reach w → j ≤ w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj
      by_cases hw : 28 ≤ w ∧ w - 28 < D.gates.length
      · rw [hreach_unfold w hw] at hj
        let kw : Fin D.gates.length := ⟨w - 28, hw.2⟩
        have hlenw := (hDShape kw).1
        let uw := (D.gates.get kw).inputs[0]'(by omega)
        let vw := (D.gates.get kw).inputs[1]'(by omega)
        have huw : uw < w := by have := (hDShape kw).2 uw (List.getElem_mem _); dsimp [kw] at this; omega
        have hvw : vw < w := by have := (hDShape kw).2 vw (List.getElem_mem _); dsimp [kw] at this; omega
        simp only [Finset.mem_insert, Finset.mem_union] at hj
        rcases hj with rfl | hj | hj
        · exact le_refl _
        · exact Nat.le_trans (ih uw huw j hj) (Nat.le_of_lt huw)
        · exact Nat.le_trans (ih vw hvw j hj) (Nat.le_of_lt hvw)
      · have hzero : reach w = {w} := by
          dsimp only [reach]
          cases w with
          | zero => simp [reachFuel]
          | succ w' => dsimp only [reachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        omega
  have hreach_closed : ∀ w j, j ∈ reach w →
      (h : 28 ≤ j ∧ j - 28 < D.gates.length) →
      let k : Fin D.gates.length := ⟨j - 28, h.2⟩
      have hlen2 : (D.gates.get k).inputs.length = 2 := (hDShape k).1
      ((D.gates.get k).inputs[0]'(by omega)) ∈ reach w ∧ ((D.gates.get k).inputs[1]'(by omega)) ∈ reach w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj hcond k hlen2
      by_cases hw : 28 ≤ w ∧ w - 28 < D.gates.length
      · rw [hreach_unfold w hw] at hj ⊢
        let kw : Fin D.gates.length := ⟨w - 28, hw.2⟩
        have hlenw := (hDShape kw).1
        let uw := (D.gates.get kw).inputs[0]'(by omega)
        let vw := (D.gates.get kw).inputs[1]'(by omega)
        have huw : uw < w := by have := (hDShape kw).2 uw (List.getElem_mem _); dsimp [kw] at this; omega
        have hvw : vw < w := by have := (hDShape kw).2 vw (List.getElem_mem _); dsimp [kw] at this; omega
        simp only [Finset.mem_insert, Finset.mem_union] at hj ⊢
        rcases hj with rfl | hj | hj
        · exact ⟨Or.inr (Or.inl (hreach_mem_self _)), Or.inr (Or.inr (hreach_mem_self _))⟩
        · have hrec := ih uw huw j hj hcond
          exact ⟨Or.inr (Or.inl hrec.1), Or.inr (Or.inl hrec.2)⟩
        · have hrec := ih vw hvw j hj hcond
          exact ⟨Or.inr (Or.inr hrec.1), Or.inr (Or.inr hrec.2)⟩
      · have hzero : reach w = {w} := by
          dsimp only [reach]
          cases w with
          | zero => simp [reachFuel]
          | succ w' => dsimp only [reachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        subst hj; omega
  have hreach_trans : ∀ w j, j ∈ reach w → reach j ⊆ reach w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj x hx
      by_cases hw : 28 ≤ w ∧ w - 28 < D.gates.length
      · rw [hreach_unfold w hw] at hj ⊢
        let kw : Fin D.gates.length := ⟨w - 28, hw.2⟩
        have hlenw := (hDShape kw).1
        let uw := (D.gates.get kw).inputs[0]'(by omega)
        let vw := (D.gates.get kw).inputs[1]'(by omega)
        have huw : uw < w := by have := (hDShape kw).2 uw (List.getElem_mem _); dsimp [kw] at this; omega
        have hvw : vw < w := by have := (hDShape kw).2 vw (List.getElem_mem _); dsimp [kw] at this; omega
        simp only [Finset.mem_insert, Finset.mem_union] at hj ⊢
        rcases hj with rfl | hj | hj
        · rw [hreach_unfold j hw] at hx
          simp only [Finset.mem_insert, Finset.mem_union] at hx
          exact hx
        · right; left; exact ih uw huw j hj hx
        · right; right; exact ih vw hvw j hj hx
      · have hzero : reach w = {w} := by
          dsimp only [reach]
          cases w with
          | zero => simp [reachFuel]
          | succ w' => dsimp only [reachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        subst hj; exact hx
  let ReachSet : Finset ℕ := reach a' ∪ reach b'
  have hReachSet_mem : a' ∈ ReachSet ∧ b' ∈ ReachSet :=
    ⟨Finset.mem_union_left _ (hreach_mem_self a'), Finset.mem_union_right _ (hreach_mem_self b')⟩
  have hReachSet_closed : ∀ j ∈ ReachSet, (h : 28 ≤ j ∧ j - 28 < D.gates.length) →
      let k : Fin D.gates.length := ⟨j - 28, h.2⟩
      have hlen2 : (D.gates.get k).inputs.length = 2 := (hDShape k).1
      ((D.gates.get k).inputs[0]'(by omega)) ∈ ReachSet ∧ ((D.gates.get k).inputs[1]'(by omega)) ∈ ReachSet := by
    intro j hj hcond k hlen2
    rcases Finset.mem_union.mp hj with hj | hj
    · have hc := hreach_closed a' j hj hcond
      exact ⟨Finset.mem_union_left _ hc.1, Finset.mem_union_left _ hc.2⟩
    · have hc := hreach_closed b' j hj hcond
      exact ⟨Finset.mem_union_right _ hc.1, Finset.mem_union_right _ hc.2⟩
  have hReachSet_reach : ∀ w ∈ ReachSet, reach w ⊆ ReachSet := by
    intro w hw j hj
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ (hreach_trans a' w hw hj)
    · exact Finset.mem_union_right _ (hreach_trans b' w hw hj)
  have hReject_x8 : ∀ P : Finset (Fin 13), x8 P → (valD a' (x7 P) || valD b' (x7 P)) = false := by
    intro P hP
    dsimp only [x8, x5, x4] at hP
    simp only [hx3_iff] at hP
    have hrej := hReject' P hP
    dsimp only at hrej
    have h7eq : (fun i : Fin 26 => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ P, ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9))) = x7 P := by
      funext i; dsimp only [x7, x4]; simp only [hx3_iff]; exact decide_eq_decide.mpr Iff.rfl
    rw [h7eq] at hrej
    exact hrej
  have hClean_x8 : ∀ i : Fin D.gates.length, (D.gates.get i).op = .and →
      ∀ P : Finset (Fin 13), x8 P → valD (28 + i.val) (x7 P) = false := by
    intro i hi P hP
    dsimp only [x8, x5, x4] at hP
    simp only [hx3_iff] at hP
    have hcl := hClean i hi P hP
    dsimp only at hcl
    have h7eq : (fun i : Fin 26 => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ P, ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9))) = x7 P := by
      funext j; dsimp only [x7, x4]; simp only [hx3_iff]; exact decide_eq_decide.mpr Iff.rfl
    rw [h7eq] at hcl
    exact hcl
  have hNoInput_a' := hNoInputInCone a' (fun P hP => (Bool.or_eq_false_iff.mp (hReject_x8 P hP)).1)
  have hNoInput_b' := hNoInputInCone b' (fun P hP => (Bool.or_eq_false_iff.mp (hReject_x8 P hP)).2)
  have hEveryEdge : ∀ p l : Fin 13, x3 p l →
      ∃ k : Fin D.gates.length, (D.gates.get k).op = .and ∧ 28 + k.val ∈ ReachSet ∧ valD (28 + k.val) (x6 p l) = true := by
    intro p l hpl
    have hu := hUnion' p l ((hx3_iff p l).mp hpl)
    change (valD a' (x6 p l) || valD b' (x6 p l)) = true at hu
    simp only [Bool.or_eq_true] at hu
    rcases hu with ha | hb
    · obtain ⟨j, hjmem, hjkind, hjval⟩ := horReach_sound a' ha' (x6 p l) ha
      rcases hjkind with hj28 | ⟨k, rfl, hkop⟩
      · exfalso
        have h26 : j ≠ 26 := fun h => hNoInput_a'.1 (h ▸ hjmem)
        have h27 : j ≠ 27 := fun h => by rw [h, hvalD_27] at hjval; cases hjval
        exact hNoInput_a'.2 ⟨j, by omega⟩ hjmem
      · exact ⟨k, hkop, Finset.mem_union_left _ (horReach_sub_reach a' hjmem), hjval⟩
    · obtain ⟨j, hjmem, hjkind, hjval⟩ := horReach_sound b' hb' (x6 p l) hb
      rcases hjkind with hj28 | ⟨k, rfl, hkop⟩
      · exfalso
        have h26 : j ≠ 26 := fun h => hNoInput_b'.1 (h ▸ hjmem)
        have h27 : j ≠ 27 := fun h => by rw [h, hvalD_27] at hjval; cases hjval
        exact hNoInput_b'.2 ⟨j, by omega⟩ hjmem
      · exact ⟨k, hkop, Finset.mem_union_right _ (horReach_sub_reach b' hjmem), hjval⟩
  let edgeCand : Fin 13 → Fin 13 → Finset (Fin D.gates.length) := fun p l => by
    classical
    exact Finset.univ.filter (fun k => (D.gates.get k).op = .and ∧ 28 + k.val ∈ ReachSet ∧ valD (28 + k.val) (x6 p l) = true)
  let owner : ∀ p l : Fin 13, x3 p l → Fin D.gates.length := fun p l hpl => by
    classical
    exact (edgeCand p l).min' (by
      obtain ⟨k, hk1, hk2, hk3⟩ := hEveryEdge p l hpl
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk1, hk2, hk3⟩⟩)
  have howner_spec : ∀ p l (hpl : x3 p l),
      let k := owner p l hpl
      (D.gates.get k).op = .and ∧ 28 + k.val ∈ ReachSet ∧ valD (28 + k.val) (x6 p l) = true := by
    intro p l hpl
    classical
    have hmem := Finset.min'_mem (edgeCand p l) (by
      obtain ⟨k, hk1, hk2, hk3⟩ := hEveryEdge p l hpl
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk1, hk2, hk3⟩⟩)
    exact (Finset.mem_filter.mp hmem).2
  have howner_min : ∀ p l (hpl : x3 p l) k,
      (D.gates.get k).op = .and → 28 + k.val ∈ ReachSet → valD (28 + k.val) (x6 p l) = true →
      owner p l hpl ≤ k := by
    intro p l hpl k hk1 hk2 hk3
    classical
    exact Finset.min'_le (edgeCand p l) k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk1, hk2, hk3⟩)
  let Owned : Finset (Fin D.gates.length) := by
    classical
    exact Finset.univ.filter (fun k => ∃ p l, ∃ hpl : x3 p l, owner p l hpl = k)
  let E_of : Fin D.gates.length → Finset (Fin 13 × Fin 13) := fun k => by
    classical
    exact Finset.univ.filter (fun pl => ∃ hpl : x3 pl.1 pl.2, owner pl.1 pl.2 hpl = k)
  have hvalD_edge_sound : ∀ k : Fin D.gates.length, (D.gates.get k).op = .and →
      ∀ p l : Fin 13, valD (28 + k.val) (x6 p l) = true → x3 p l := by
    intro k hk p l hval
    by_contra hnot
    have hsub : ∀ q : Fin 26, x6 p l q = true → x7 {p} q = true := by
      intro q hq
      dsimp only [x6] at hq
      rw [decide_eq_true_eq] at hq
      dsimp only [x7]
      rw [decide_eq_true_eq]
      rcases hq with rfl | rfl
      · left; exact ⟨p, Finset.mem_singleton_self p, rfl⟩
      · right; refine ⟨l, rfl, fun p' hp' => ?_⟩
        rw [Finset.mem_singleton] at hp'; subst hp'; exact hnot
    have h1 := hmonoD (28 + k.val) (x6 p l) (x7 {p}) hsub hval
    have h0 := hClean_x8 k hk {p} (hSingle p)
    rw [h1] at h0; cases h0
  have hOwner_sides : ∀ p l (hpl : x3 p l),
      let k := owner p l hpl
      have hlen2 : (D.gates.get k).inputs.length = 2 := (hDShape k).1
      let u := (D.gates.get k).inputs[0]'(by omega)
      let v := (D.gates.get k).inputs[1]'(by omega)
      (Fin.castAdd 13 p ∈ Sings u ∧ Fin.natAdd 13 l ∈ Sings v) ∨
      (Fin.natAdd 13 l ∈ Sings u ∧ Fin.castAdd 13 p ∈ Sings v) := by
    intro p l hpl k hlen2 u v
    obtain ⟨hkop, hkreach, hkval⟩ := howner_spec p l hpl
    have hval := hvalD_gate k (x6 p l)
    rw [hkop] at hval
    have hinps : (D.gates.get k).inputs = [u, v] := by
      cases hge : (D.gates.get k).inputs with
      | nil => rw [hge] at hlen2; simp at hlen2
      | cons a t => cases t with | nil => rw [hge] at hlen2; simp at hlen2 | cons b t2 => cases t2 with | cons _ _ => rw [hge] at hlen2; simp at hlen2 | nil => dsimp only [u, v]; simp only [hge]; rfl
    rw [hinps] at hval
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true] at hval
    change valD (28 + k.val) (x6 p l) = (valD u (x6 p l) && valD v (x6 p l)) at hval
    rw [hkval] at hval
    have hval' := hval.symm
    rw [Bool.and_eq_true] at hval'
    have hu_lt : u < 28 + D.size := by have := (hDShape k).2 u (List.getElem_mem _); simp only [CircuitLowerBounds.Circuit.size]; omega
    have hv_lt : v < 28 + D.size := by have := (hDShape k).2 v (List.getElem_mem _); simp only [CircuitLowerBounds.Circuit.size]; omega
    have hclosed := hReachSet_closed (28 + k.val) hkreach ⟨by omega, by omega⟩
    have hu_reach : u ∈ ReachSet := by convert hclosed.1 using 2; ext; simp [k]
    have hv_reach : v ∈ ReachSet := by convert hclosed.2 using 2; ext; simp [k]
    obtain ⟨ju, hju_mem, hju_kind, hju_val⟩ := horReach_sound u hu_lt (x6 p l) hval'.1
    obtain ⟨jv, hjv_mem, hjv_kind, hjv_val⟩ := horReach_sound v hv_lt (x6 p l) hval'.2
    have hju_lt : ju < 28 := by
      rcases hju_kind with h28 | ⟨k', rfl, hk'op⟩
      · exact h28
      · exfalso
        have hk'_reach : 28 + k'.val ∈ ReachSet := hReachSet_reach u hu_reach (horReach_sub_reach u hju_mem)
        have hle := howner_min p l hpl k' hk'op hk'_reach hju_val
        have hle_u := hreach_le u (28 + k'.val) (horReach_sub_reach u hju_mem)
        have hu_k := (hDShape k).2 u (List.getElem_mem _)
        omega
    have hjv_lt : jv < 28 := by
      rcases hjv_kind with h28 | ⟨k', rfl, hk'op⟩
      · exact h28
      · exfalso
        have hk'_reach : 28 + k'.val ∈ ReachSet := hReachSet_reach v hv_reach (horReach_sub_reach v hjv_mem)
        have hle := howner_min p l hpl k' hk'op hk'_reach hjv_val
        have hle_v := hreach_le v (28 + k'.val) (horReach_sub_reach v hjv_mem)
        have hv_k := (hDShape k).2 v (List.getElem_mem _)
        omega
    have hju_ne27 : ju ≠ 27 := fun h => by rw [h, hvalD_27] at hju_val; cases hju_val
    have hjv_ne27 : jv ≠ 27 := fun h => by rw [h, hvalD_27] at hjv_val; cases hjv_val
    have hju_ne26 : ju ≠ 26 := by
      intro h26
      have h26_mem : 26 ∈ orReach u := h26 ▸ hju_mem
      have hv_false : ∀ P : Finset (Fin 13), x8 P → valD v (x7 P) = false := by
        intro P hP
        have hu_true := horReach_mono u 26 h26_mem (x7 P) (hvalD_26 (x7 P))
        have hk_false := hClean_x8 k hkop P hP
        have hvalP := hvalD_gate k (x7 P)
        rw [hkop, hinps] at hvalP
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
        change valD (28 + k.val) (x7 P) = (valD u (x7 P) && valD v (x7 P)) at hvalP
        rw [hk_false, hu_true, Bool.true_and] at hvalP
        exact hvalP.symm
      have hno := hNoInputInCone v hv_false
      by_cases hjv26 : jv = 26
      · exact hno.1 (hjv26 ▸ hjv_mem)
      · exact hno.2 ⟨jv, by omega⟩ hjv_mem
    have hjv_ne26 : jv ≠ 26 := by
      intro h26
      have h26_mem : 26 ∈ orReach v := h26 ▸ hjv_mem
      have hu_false : ∀ P : Finset (Fin 13), x8 P → valD u (x7 P) = false := by
        intro P hP
        have hv_true := horReach_mono v 26 h26_mem (x7 P) (hvalD_26 (x7 P))
        have hk_false := hClean_x8 k hkop P hP
        have hvalP := hvalD_gate k (x7 P)
        rw [hkop, hinps] at hvalP
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
        change valD (28 + k.val) (x7 P) = (valD u (x7 P) && valD v (x7 P)) at hvalP
        rw [hk_false, hv_true, Bool.and_true] at hvalP
        exact hvalP.symm
      have hno := hNoInputInCone u hu_false
      exact hno.2 ⟨ju, by omega⟩ hju_mem
    have hju_26 : ju < 26 := by omega
    have hjv_26 : jv < 26 := by omega
    rw [hvalD_lt ju hju_26 (x6 p l)] at hju_val
    rw [hvalD_lt jv hjv_26 (x6 p l)] at hjv_val
    dsimp only [x6] at hju_val hjv_val
    rw [decide_eq_true_eq] at hju_val hjv_val
    have hju_sings : ⟨ju, hju_26⟩ ∈ Sings u := by
      simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and]
      exact horReach_mono u ju hju_mem (sing ⟨ju, hju_26⟩) (by rw [hvalD_lt ju hju_26]; simp [sing])
    have hjv_sings : ⟨jv, hjv_26⟩ ∈ Sings v := by
      simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and]
      exact horReach_mono v jv hjv_mem (sing ⟨jv, hjv_26⟩) (by rw [hvalD_lt jv hjv_26]; simp [sing])
    rcases hju_val with hup | hul <;> rcases hjv_val with hvp | hvl
    · exfalso
      have hsing_p : (Fin.castAdd 13 p : Fin 26) ∈ Sings u ∧ (Fin.castAdd 13 p : Fin 26) ∈ Sings v :=
        ⟨by rw [← hup]; exact hju_sings, by rw [← hvp]; exact hjv_sings⟩
      have hsub : ∀ q : Fin 26, sing (Fin.castAdd 13 p) q = true → x7 {p} q = true := by
        intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq
        dsimp only [x7]; rw [decide_eq_true_eq]; left; exact ⟨p, Finset.mem_singleton_self p, rfl⟩
      have hu_t := hmonoD u (sing (Fin.castAdd 13 p)) (x7 {p}) hsub (Finset.mem_filter.mp hsing_p.1).2
      have hv_t := hmonoD v (sing (Fin.castAdd 13 p)) (x7 {p}) hsub (Finset.mem_filter.mp hsing_p.2).2
      have hvalP := hvalD_gate k (x7 {p})
      rw [hkop, hinps] at hvalP
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
      change valD (28 + k.val) (x7 {p}) = (valD u (x7 {p}) && valD v (x7 {p})) at hvalP
      rw [hu_t, hv_t] at hvalP
      have h0 := hClean_x8 k hkop {p} (hSingle p)
      rw [h0] at hvalP; cases hvalP
    · left; exact ⟨by rw [← hup]; exact hju_sings, by rw [← hvl]; exact hjv_sings⟩
    · right; exact ⟨by rw [← hul]; exact hju_sings, by rw [← hvp]; exact hjv_sings⟩
    · exfalso
      have hsing_l : (Fin.natAdd 13 l : Fin 26) ∈ Sings u ∧ (Fin.natAdd 13 l : Fin 26) ∈ Sings v :=
        ⟨by rw [← hul]; exact hju_sings, by rw [← hvl]; exact hjv_sings⟩
      let P := Finset.univ.filter (fun p' : Fin 13 => ¬x3 p' l)
      have hsub : ∀ q : Fin 26, sing (Fin.natAdd 13 l) q = true → x7 P q = true := by
        intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq
        dsimp only [x7]; rw [decide_eq_true_eq]; right; exact ⟨l, rfl, fun p' hp' => (Finset.mem_filter.mp hp').2⟩
      have hu_t := hmonoD u (sing (Fin.natAdd 13 l)) (x7 P) hsub (Finset.mem_filter.mp hsing_l.1).2
      have hv_t := hmonoD v (sing (Fin.natAdd 13 l)) (x7 P) hsub (Finset.mem_filter.mp hsing_l.2).2
      have hvalP := hvalD_gate k (x7 P)
      rw [hkop, hinps] at hvalP
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
      change valD (28 + k.val) (x7 P) = (valD u (x7 P) && valD v (x7 P)) at hvalP
      rw [hu_t, hv_t] at hvalP
      have h0 := hClean_x8 k hkop P (hAvoidLine l)
      rw [h0] at hvalP; cases hvalP
  have hAnd_pair : ∀ k : Fin D.gates.length, (D.gates.get k).op = .and →
      ∀ (p l : Fin 13),
      have hlen2 : (D.gates.get k).inputs.length = 2 := (hDShape k).1
      let u := (D.gates.get k).inputs[0]'(by omega)
      let v := (D.gates.get k).inputs[1]'(by omega)
      (Fin.castAdd 13 p ∈ Sings u ∧ Fin.natAdd 13 l ∈ Sings v) ∨
      (Fin.natAdd 13 l ∈ Sings u ∧ Fin.castAdd 13 p ∈ Sings v) →
      valD (28 + k.val) (x6 p l) = true := by
    intro k hk p l hlen2 u v hmem
    have hinps : (D.gates.get k).inputs = [u, v] := by
      cases hge : (D.gates.get k).inputs with
      | nil => rw [hge] at hlen2; simp at hlen2
      | cons a t => cases t with | nil => rw [hge] at hlen2; simp at hlen2 | cons b t2 => cases t2 with | cons _ _ => rw [hge] at hlen2; simp at hlen2 | nil => dsimp only [u, v]; simp only [hge]; rfl
    have hval := hvalD_gate k (x6 p l)
    rw [hk, hinps] at hval
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true] at hval
    change valD (28 + k.val) (x6 p l) = (valD u (x6 p l) && valD v (x6 p l)) at hval
    rw [hval, Bool.and_eq_true]
    have hsubp : ∀ q : Fin 26, sing (Fin.castAdd 13 p) q = true → x6 p l q = true := by
      intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq; dsimp only [x6]; rw [decide_eq_true_eq]; left; rfl
    have hsubl : ∀ q : Fin 26, sing (Fin.natAdd 13 l) q = true → x6 p l q = true := by
      intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq; dsimp only [x6]; rw [decide_eq_true_eq]; right; rfl
    rcases hmem with ⟨hp, hl⟩ | ⟨hl, hp⟩
    · exact ⟨hmonoD u _ _ hsubp (Finset.mem_filter.mp hp).2, hmonoD v _ _ hsubl (Finset.mem_filter.mp hl).2⟩
    · exact ⟨hmonoD u _ _ hsubl (Finset.mem_filter.mp hl).2, hmonoD v _ _ hsubp (Finset.mem_filter.mp hp).2⟩
  have hNoCrossPt : ∀ k : Fin D.gates.length, (D.gates.get k).op = .and →
      have hlen2 : (D.gates.get k).inputs.length = 2 := (hDShape k).1
      let u := (D.gates.get k).inputs[0]'(by omega)
      let v := (D.gates.get k).inputs[1]'(by omega)
      ∀ p1 p2 : Fin 13, Fin.castAdd 13 p1 ∈ Sings u → Fin.castAdd 13 p2 ∈ Sings v → p1 = p2 := by
    intro k hk hlen2 u v p1 p2 hp1 hp2
    by_contra hne
    have hinps : (D.gates.get k).inputs = [u, v] := by
      cases hge : (D.gates.get k).inputs with
      | nil => rw [hge] at hlen2; simp at hlen2
      | cons a t => cases t with | nil => rw [hge] at hlen2; simp at hlen2 | cons b t2 => cases t2 with | cons _ _ => rw [hge] at hlen2; simp at hlen2 | nil => dsimp only [u, v]; simp only [hge]; rfl
    have hsub1 : ∀ q : Fin 26, sing (Fin.castAdd 13 p1) q = true → x7 {p1, p2} q = true := by
      intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq; dsimp only [x7]; rw [decide_eq_true_eq]
      left; exact ⟨p1, Finset.mem_insert_self _ _, rfl⟩
    have hsub2 : ∀ q : Fin 26, sing (Fin.castAdd 13 p2) q = true → x7 {p1, p2} q = true := by
      intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq; dsimp only [x7]; rw [decide_eq_true_eq]
      left; exact ⟨p2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl⟩
    have hu_t := hmonoD u _ _ hsub1 (Finset.mem_filter.mp hp1).2
    have hv_t := hmonoD v _ _ hsub2 (Finset.mem_filter.mp hp2).2
    have hval := hvalD_gate k (x7 {p1, p2})
    rw [hk, hinps] at hval
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true] at hval
    change valD (28 + k.val) (x7 {p1, p2}) = (valD u (x7 {p1, p2}) && valD v (x7 {p1, p2})) at hval
    rw [hu_t, hv_t] at hval
    have h0 := hClean_x8 k hk {p1, p2} (hPairPt p1 p2 hne)
    rw [h0] at hval; cases hval
  have hNoCrossLine : ∀ k : Fin D.gates.length, (D.gates.get k).op = .and →
      have hlen2 : (D.gates.get k).inputs.length = 2 := (hDShape k).1
      let u := (D.gates.get k).inputs[0]'(by omega)
      let v := (D.gates.get k).inputs[1]'(by omega)
      ∀ l1 l2 : Fin 13, Fin.natAdd 13 l1 ∈ Sings u → Fin.natAdd 13 l2 ∈ Sings v → l1 = l2 := by
    intro k hk hlen2 u v l1 l2 hl1 hl2
    by_contra hne
    have hinps : (D.gates.get k).inputs = [u, v] := by
      cases hge : (D.gates.get k).inputs with
      | nil => rw [hge] at hlen2; simp at hlen2
      | cons a t => cases t with | nil => rw [hge] at hlen2; simp at hlen2 | cons b t2 => cases t2 with | cons _ _ => rw [hge] at hlen2; simp at hlen2 | nil => dsimp only [u, v]; simp only [hge]; rfl
    let P := Finset.univ.filter (fun p : Fin 13 => ¬x3 p l1 ∧ ¬x3 p l2)
    have hsub1 : ∀ q : Fin 26, sing (Fin.natAdd 13 l1) q = true → x7 P q = true := by
      intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq; dsimp only [x7]; rw [decide_eq_true_eq]
      right; exact ⟨l1, rfl, fun p hp => (Finset.mem_filter.mp hp).2.1⟩
    have hsub2 : ∀ q : Fin 26, sing (Fin.natAdd 13 l2) q = true → x7 P q = true := by
      intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq; dsimp only [x7]; rw [decide_eq_true_eq]
      right; exact ⟨l2, rfl, fun p hp => (Finset.mem_filter.mp hp).2.2⟩
    have hu_t := hmonoD u _ _ hsub1 (Finset.mem_filter.mp hl1).2
    have hv_t := hmonoD v _ _ hsub2 (Finset.mem_filter.mp hl2).2
    have hval := hvalD_gate k (x7 P)
    rw [hk, hinps] at hval
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true] at hval
    change valD (28 + k.val) (x7 P) = (valD u (x7 P) && valD v (x7 P)) at hval
    rw [hu_t, hv_t] at hval
    have h0 := hClean_x8 k hk P (hPairLine l1 l2 hne)
    rw [h0] at hval; cases hval
  have hStar_pair : ∀ k ∈ Owned, ∀ pl1 ∈ E_of k, ∀ pl2 ∈ E_of k, pl1.1 = pl2.1 ∨ pl1.2 = pl2.2 := by
    intro k hk pl1 hpl1 pl2 hpl2
    by_contra hnot
    simp only [not_or] at hnot
    obtain ⟨hx1, ho1⟩ := (Finset.mem_filter.mp hpl1).2
    obtain ⟨hx2, ho2⟩ := (Finset.mem_filter.mp hpl2).2
    have hkop : (D.gates.get k).op = .and := ho1 ▸ (howner_spec pl1.1 pl1.2 hx1).1
    have hs1 := hOwner_sides pl1.1 pl1.2 hx1
    have hs2 := hOwner_sides pl2.1 pl2.2 hx2
    dsimp only at hs1 hs2
    have h_in0_eq : ∀ a b : Fin D.gates.length, a = b →
        (D.gates.get a).inputs[0]'(by have := (hDShape a).1; omega) =
        (D.gates.get b).inputs[0]'(by have := (hDShape b).1; omega) := fun _ _ h => h ▸ rfl
    have h_in1_eq : ∀ a b : Fin D.gates.length, a = b →
        (D.gates.get a).inputs[1]'(by have := (hDShape a).1; omega) =
        (D.gates.get b).inputs[1]'(by have := (hDShape b).1; omega) := fun _ _ h => h ▸ rfl
    rw [h_in0_eq _ k ho1, h_in1_eq _ k ho1] at hs1
    rw [h_in0_eq _ k ho2, h_in1_eq _ k ho2] at hs2
    have h12 : valD (28 + k.val) (x6 pl1.1 pl2.2) = true := by
      apply hAnd_pair k hkop
      rcases hs1 with ⟨hp1, hl1⟩ | ⟨hl1, hp1⟩ <;> rcases hs2 with ⟨hp2, hl2⟩ | ⟨hl2, hp2⟩
      · exact Or.inl ⟨hp1, hl2⟩
      · exact absurd (hNoCrossPt k hkop pl1.1 pl2.1 hp1 hp2) hnot.1
      · exact absurd (hNoCrossPt k hkop pl2.1 pl1.1 hp2 hp1).symm hnot.1
      · exact Or.inr ⟨hl2, hp1⟩
    have h21 : valD (28 + k.val) (x6 pl2.1 pl1.2) = true := by
      apply hAnd_pair k hkop
      rcases hs1 with ⟨hp1, hl1⟩ | ⟨hl1, hp1⟩ <;> rcases hs2 with ⟨hp2, hl2⟩ | ⟨hl2, hp2⟩
      · exact Or.inl ⟨hp2, hl1⟩
      · exact absurd (hNoCrossLine k hkop pl2.2 pl1.2 hl2 hl1).symm hnot.2
      · exact absurd (hNoCrossLine k hkop pl1.2 pl2.2 hl1 hl2) hnot.2
      · exact Or.inr ⟨hl1, hp2⟩
    have hx12 := hvalD_edge_sound k hkop pl1.1 pl2.2 h12
    have hx21 := hvalD_edge_sound k hkop pl2.1 pl1.2 h21
    rcases hNoC4 pl1.1 pl2.1 pl1.2 pl2.2 hnot.1 hnot.2 hx1 hx2 with h | h
    · exact h hx12
    · exact h hx21
  have hStar_center : ∀ k ∈ Owned, (∃ p0, ∀ pl ∈ E_of k, pl.1 = p0) ∨ (∃ l0, ∀ pl ∈ E_of k, pl.2 = l0) := by
    intro k hk
    obtain ⟨p0, l0, hpl0, ho0⟩ := (Finset.mem_filter.mp hk).2
    have hmem0 : (p0, l0) ∈ E_of k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl0, ho0⟩
    by_cases hp : ∀ pl ∈ E_of k, pl.1 = p0
    · exact Or.inl ⟨p0, hp⟩
    · push Not at hp
      obtain ⟨⟨p1, l1⟩, hmem1, hp1⟩ := hp
      have hl1 : l1 = l0 := (hStar_pair k hk (p1, l1) hmem1 (p0, l0) hmem0).resolve_left hp1
      right; refine ⟨l0, fun ⟨p2, l2⟩ hmem2 => ?_⟩
      rcases hStar_pair k hk (p2, l2) hmem2 (p0, l0) hmem0 with h20 | h20
      · rcases hStar_pair k hk (p2, l2) hmem2 (p1, l1) hmem1 with h21 | h21
        · exact absurd (h20.symm.trans h21) (Ne.symm hp1)
        · exact h21.trans hl1
      · exact h20
  have hE_of_le4 : ∀ k ∈ Owned, (E_of k).card ≤ 4 := by
    intro k hk
    rcases hStar_center k hk with ⟨p0, hp0⟩ | ⟨l0, hl0⟩
    · let S : Finset (Fin 13 × Fin 13) :=
        {(p0, p0), (p0, p0 - 1), (p0, p0 - 3), (p0, p0 - 9)}
      have hsub : E_of k ⊆ S := by
        intro ⟨p, l⟩ hpl
        have hpeq : p = p0 := hp0 (p, l) hpl
        obtain ⟨hx, _⟩ := (Finset.mem_filter.mp hpl).2
        rw [hx3_iff, hpeq] at hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hpeq, true_and]
        rcases hx with h | h | h | h
        · left; exact h.symm
        · right; left; have := congrArg (· - 1) h; abel_nf at this ⊢; exact this.symm
        · right; right; left; have := congrArg (· - 3) h; abel_nf at this ⊢; exact this.symm
        · right; right; right; have := congrArg (· - 9) h; abel_nf at this ⊢; exact this.symm
      have hcard4 : S.card ≤ 4 :=
        le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
          (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
            (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))))
      exact le_trans (Finset.card_le_card hsub) hcard4
    · let S : Finset (Fin 13 × Fin 13) :=
        {(l0, l0), (l0 + 1, l0), (l0 + 3, l0), (l0 + 9, l0)}
      have hsub : E_of k ⊆ S := by
        intro ⟨p, l⟩ hpl
        have hleq : l = l0 := hl0 (p, l) hpl
        obtain ⟨hx, _⟩ := (Finset.mem_filter.mp hpl).2
        rw [hx3_iff, hleq] at hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hleq, and_true]
        exact hx
      have hcard4 : S.card ≤ 4 :=
        le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
          (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ
            (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (Finset.card_singleton _).le)))))
      exact le_trans (Finset.card_le_card hsub) hcard4
  have hSum_E_of : ∑ k ∈ Owned, (E_of k).card = 52 := by
    let AllE : Finset (Fin 13 × Fin 13) := Finset.univ.filter (fun pl => x3 pl.1 pl.2)
    have hpart : AllE = Owned.biUnion E_of := by
      ext ⟨p, l⟩
      simp only [AllE, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hx
        exact ⟨owner p l hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, l, hx, rfl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, rfl⟩⟩
      · rintro ⟨k, _, hmem⟩
        exact (Finset.mem_filter.mp hmem).2.1
    have hdisj : ∀ k1 ∈ Owned, ∀ k2 ∈ Owned, k1 ≠ k2 → Disjoint (E_of k1) (E_of k2) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro pl h1 h2
      obtain ⟨hx1, ho1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨hx2, ho2⟩ := (Finset.mem_filter.mp h2).2
      exact hne (ho1.symm.trans ho2)
    have hcard_eq : AllE.card = ∑ k ∈ Owned, (E_of k).card := by
      rw [hpart, Finset.card_biUnion hdisj]
    have hAllE_card : AllE.card = 52 := by
      let row : Fin 13 → Finset (Fin 13 × Fin 13) := fun l =>
        {(l, l), (l + 1, l), (l + 3, l), (l + 9, l)}
      have hrow_part : AllE = Finset.univ.biUnion row := by
        ext ⟨p, l⟩
        simp only [AllE, row, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hx3_iff]
        constructor
        · intro h; exact ⟨l, by rcases h with h | h | h | h <;> [left; (right; left); (right; right; left); (right; right; right)] <;> exact ⟨h, rfl⟩⟩
        · rintro ⟨l', h⟩; rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> [left; (right; left); (right; right; left); (right; right; right)] <;> exact h1
      have hrow_disj : ∀ l1 ∈ (Finset.univ : Finset (Fin 13)), ∀ l2 ∈ (Finset.univ : Finset (Fin 13)), l1 ≠ l2 → Disjoint (row l1) (row l2) := by
        intro l1 _ l2 _ hne
        rw [Finset.disjoint_left]
        intro ⟨p, l⟩ h1 h2
        simp only [row, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
        have hl1 : l = l1 := by rcases h1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
        have hl2 : l = l2 := by rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
        exact hne (hl1.symm.trans hl2)
      have hrow_card : ∀ l : Fin 13, (row l).card = 4 := by
        intro l
        have h1 : (l, l) ∉ ({(l + 1, l), (l + 3, l), (l + 9, l)} : Finset (Fin 13 × Fin 13)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> (have := congrArg (· - l) h; abel_nf at this; revert this; decide)
        have h2 : (l + 1, l) ∉ ({(l + 3, l), (l + 9, l)} : Finset (Fin 13 × Fin 13)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          rintro (⟨h, _⟩ | ⟨h, _⟩) <;> (have := congrArg (· - l) h; abel_nf at this; revert this; decide)
        have h3 : (l + 3, l) ∉ ({(l + 9, l)} : Finset (Fin 13 × Fin 13)) := by
          simp only [Finset.mem_singleton, Prod.mk.injEq]
          rintro ⟨h, _⟩; have := congrArg (· - l) h; abel_nf at this; revert this; decide
        simp only [row, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
          Finset.card_insert_of_notMem h3, Finset.card_singleton]
      rw [hrow_part, Finset.card_biUnion hrow_disj]
      simp [hrow_card]
    exact hcard_eq.symm.trans hAllE_card
  have hOwned_card : 13 ≤ Owned.card := by
    have hle : ∑ k ∈ Owned, (E_of k).card ≤ ∑ _k ∈ Owned, 4 := Finset.sum_le_sum (fun k hk => hE_of_le4 k hk)
    rw [hSum_E_of, Finset.sum_const, smul_eq_mul] at hle
    omega
  let R_gates : Finset (Fin D.gates.length) := Finset.univ.filter (fun g => 28 + g.val ∈ ReachSet)
  let Z : Finset (Fin D.gates.length) := by
    classical
    exact R_gates.filter (fun g => Sings (28 + g.val) = ∅)
  have hOwned_sub_Z : Owned ⊆ Z := by
    intro k hk
    obtain ⟨p, l, hpl, rfl⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨hkop, hkreach, _⟩ := howner_spec p l hpl
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkreach⟩, hSings_and _ hkop⟩
  have hZ_not_input_Owned : ∀ z ∈ Z, ∀ k ∈ Owned, 28 + z.val ∉ (D.gates.get k).inputs := by
    intro z hz k hk hmem
    have hz_reach : 28 + z.val ∈ ReachSet := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hz_empty : Sings (28 + z.val) = ∅ := (Finset.mem_filter.mp hz).2
    obtain ⟨p, l, hpl, rfl⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨hkop, hkreach, hkval⟩ := howner_spec p l hpl
    have hval := hvalD_gate (owner p l hpl) (x6 p l)
    rw [hkop] at hval
    change valD (28 + (owner p l hpl).val) (x6 p l) = _ at hval
    rw [hkval] at hval
    have hval_z : valD (28 + z.val) (x6 p l) = true := by
      have hall := List.all_eq_true.mp hval.symm
      exact hall (valD (28 + z.val) (x6 p l)) (List.mem_map.mpr ⟨28 + z.val, hmem, rfl⟩)
    have hz_lt : 28 + z.val < 28 + D.size := by simp only [CircuitLowerBounds.Circuit.size]; omega
    obtain ⟨j, hjmem, hjkind, hjval⟩ := horReach_sound (28 + z.val) hz_lt (x6 p l) hval_z
    rcases hjkind with hj28 | ⟨k', rfl, hk'op⟩
    · have hj26 : j ≠ 26 := by
        intro h26
        have hsing := horReach_mono (28 + z.val) 26 (h26 ▸ hjmem) (sing 0) (hvalD_26 (sing 0))
        have hmem0 : (0 : Fin 26) ∈ Sings (28 + z.val) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsing⟩
        rw [hz_empty] at hmem0; exact Finset.notMem_empty _ hmem0
      have hj27 : j ≠ 27 := fun h => by rw [h, hvalD_27] at hjval; cases hjval
      have hj26_lt : j < 26 := by omega
      have hsing := horReach_mono (28 + z.val) j hjmem (sing ⟨j, hj26_lt⟩) (by rw [hvalD_lt j hj26_lt]; simp [sing])
      have hmemj : ⟨j, hj26_lt⟩ ∈ Sings (28 + z.val) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsing⟩
      rw [hz_empty] at hmemj; exact Finset.notMem_empty _ hmemj
    · have hk'_reach : 28 + k'.val ∈ ReachSet := hReachSet_reach (28 + z.val) hz_reach (horReach_sub_reach _ hjmem)
      have hle := howner_min p l hpl k' hk'op hk'_reach hjval
      have hle_z := hreach_le (28 + z.val) (28 + k'.val) (horReach_sub_reach _ hjmem)
      have hz_k := (hDShape (owner p l hpl)).2 (28 + z.val) hmem
      omega
  let center : Fin D.gates.length → Fin 13 ⊕ Fin 13 := fun k => by
    classical
    exact if hk : k ∈ Owned then
      if hp : ∃ p0, ∀ pl ∈ E_of k, pl.1 = p0 then Sum.inl hp.choose
      else Sum.inr ((hStar_center k hk).resolve_left hp).choose
    else Sum.inl 0
  let in0 : Fin D.gates.length → ℕ := fun g => (D.gates.get g).inputs[0]'(by have := (hDShape g).1; omega)
  let in1 : Fin D.gates.length → ℕ := fun g => (D.gates.get g).inputs[1]'(by have := (hDShape g).1; omega)
  have hin0_eq : ∀ a b : Fin D.gates.length, a = b → in0 a = in0 b := fun _ _ h => h ▸ rfl
  have hin1_eq : ∀ a b : Fin D.gates.length, a = b → in1 a = in1 b := fun _ _ h => h ▸ rfl
  have hOwner_sides_k : ∀ k ∈ Owned, ∀ pl ∈ E_of k,
      (Fin.castAdd 13 pl.1 ∈ Sings (in0 k) ∧ Fin.natAdd 13 pl.2 ∈ Sings (in1 k)) ∨
      (Fin.natAdd 13 pl.2 ∈ Sings (in0 k) ∧ Fin.castAdd 13 pl.1 ∈ Sings (in1 k)) := by
    intro k _ pl hpl
    obtain ⟨hx, ho⟩ := (Finset.mem_filter.mp hpl).2
    have hs := hOwner_sides pl.1 pl.2 hx
    change (Fin.castAdd 13 pl.1 ∈ Sings (in0 (owner pl.1 pl.2 hx)) ∧ Fin.natAdd 13 pl.2 ∈ Sings (in1 (owner pl.1 pl.2 hx))) ∨
      (Fin.natAdd 13 pl.2 ∈ Sings (in0 (owner pl.1 pl.2 hx)) ∧ Fin.castAdd 13 pl.1 ∈ Sings (in1 (owner pl.1 pl.2 hx))) at hs
    rw [hin0_eq _ k ho, hin1_eq _ k ho] at hs
    exact hs
  have hStar_side : ∀ k ∈ Owned, 2 ≤ (E_of k).card →
      ∃ side : Fin 2,
        let vk := if side = 0 then in0 k else in1 k
        vk ∈ ReachSet ∧ 26 ∉ orReach vk ∧ (E_of k).card ≤ (Sings vk).card ∧
        (match center k with
         | Sum.inl p0 => (∀ pl ∈ E_of k, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings vk) ∧ (∀ q ∈ Sings vk, 13 ≤ q.val)
         | Sum.inr l0 => (∀ pl ∈ E_of k, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings vk) ∧ (∀ q ∈ Sings vk, q.val < 13)) := by
    intro k hk hcard2
    obtain ⟨pl1, hpl1, pl2, hpl2, hne⟩ := Finset.one_lt_card.mp hcard2
    obtain ⟨p0, l0, hpl0, ho0⟩ := (Finset.mem_filter.mp hk).2
    have hkop : (D.gates.get k).op = .and := ho0 ▸ (howner_spec p0 l0 hpl0).1
    have hkreach : 28 + k.val ∈ ReachSet := ho0 ▸ (howner_spec p0 l0 hpl0).2.1
    have hclosed := hReachSet_closed (28 + k.val) hkreach ⟨by omega, by omega⟩
    have hk_sub_eq : (⟨28 + k.val - 28, (by omega : 28 + k.val - 28 < D.gates.length)⟩ : Fin D.gates.length) = k :=
      Fin.ext (by simp)
    have hin0_reach : in0 k ∈ ReachSet := hin0_eq _ k hk_sub_eq ▸ hclosed.1
    have hin1_reach : in1 k ∈ ReachSet := hin1_eq _ k hk_sub_eq ▸ hclosed.2
    have hinps : (D.gates.get k).inputs = [in0 k, in1 k] := by
      have hlen2 := (hDShape k).1
      cases hge : (D.gates.get k).inputs with
      | nil => rw [hge] at hlen2; simp at hlen2
      | cons a t => cases t with | nil => rw [hge] at hlen2; simp at hlen2 | cons b t2 => cases t2 with | cons _ _ => rw [hge] at hlen2; simp at hlen2 | nil => dsimp only [in0, in1]; simp only [hge]; rfl
    have hno26_of_sing : ∀ a b : ℕ, (a = in0 k ∧ b = in1 k ∨ a = in1 k ∧ b = in0 k) →
        (Sings b).Nonempty → 26 ∉ orReach a := by
      intro a b hab ⟨qb, hqb⟩ ha26
      have ha_true : ∀ P : Finset (Fin 13), valD a (x7 P) = true :=
        fun P => horReach_mono a 26 ha26 (x7 P) (hvalD_26 (x7 P))
      have hb_false : ∀ P : Finset (Fin 13), x8 P → valD b (x7 P) = false := by
        intro P hP
        have hk_false := hClean_x8 k hkop P hP
        have hvalP := hvalD_gate k (x7 P)
        rw [hkop, hinps] at hvalP
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
        change valD (28 + k.val) (x7 P) = (valD (in0 k) (x7 P) && valD (in1 k) (x7 P)) at hvalP
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hk_false, ha_true P, Bool.true_and] at hvalP; exact hvalP.symm
        · rw [hk_false, ha_true P, Bool.and_true] at hvalP; exact hvalP.symm
      by_cases hqb13 : qb.val < 13
      · let p : Fin 13 := ⟨qb.val, hqb13⟩
        have hsub : ∀ q : Fin 26, sing qb q = true → x7 {p} q = true := by
          intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq
          dsimp only [x7]; rw [decide_eq_true_eq]; left; exact ⟨p, Finset.mem_singleton_self p, by ext; simp [p]⟩
        have ht := hmonoD b _ _ hsub (Finset.mem_filter.mp hqb).2
        rw [hb_false {p} (hSingle p)] at ht; cases ht
      · let l : Fin 13 := ⟨qb.val - 13, by omega⟩
        let P := Finset.univ.filter (fun p : Fin 13 => ¬x3 p l)
        have hsub : ∀ q : Fin 26, sing qb q = true → x7 P q = true := by
          intro q hq; simp only [sing, decide_eq_true_eq] at hq; subst hq
          dsimp only [x7]; rw [decide_eq_true_eq]; right; refine ⟨l, ?_, fun p hp => (Finset.mem_filter.mp hp).2⟩
          ext; simp [l]; omega
        have ht := hmonoD b _ _ hsub (Finset.mem_filter.mp hqb).2
        rw [hb_false P (hAvoidLine l)] at ht; cases ht
    have hs1 := hOwner_sides_k k hk pl1 hpl1
    have hs2 := hOwner_sides_k k hk pl2 hpl2
    dsimp only [center]
    rw [dif_pos hk]
    split_ifs with hp
    · have hp0 := hp.choose_spec
      set p_c := hp.choose
      have hp1 : pl1.1 = p_c := hp0 pl1 hpl1
      have hp2 : pl2.1 = p_c := hp0 pl2 hpl2
      have hl_ne : pl1.2 ≠ pl2.2 := fun h => hne (Prod.ext (hp1.trans hp2.symm) h)
      have h_no_pt : ∀ (vk uk : ℕ), (vk = in0 k ∧ uk = in1 k ∨ vk = in1 k ∧ uk = in0 k) →
          Fin.castAdd 13 p_c ∈ Sings uk → ∀ q ∈ Sings vk, 13 ≤ q.val := by
        intro vk uk hvkuk huk_p q hq
        by_contra hlt13
        have hlt : q.val < 13 := by omega
        let p' : Fin 13 := ⟨q.val, hlt⟩
        have hqeq : q = Fin.castAdd 13 p' := by ext; simp [p']
        rw [hqeq] at hq
        by_cases hpp : p' = p_c
        · rw [hpp] at hq
          have hsub : ∀ r : Fin 26, sing (Fin.castAdd 13 p_c) r = true → x7 {p_c} r = true := by
            intro r hr; simp only [sing, decide_eq_true_eq] at hr; subst hr; dsimp only [x7]; rw [decide_eq_true_eq]
            left; exact ⟨p_c, Finset.mem_singleton_self p_c, rfl⟩
          have ht1 := hmonoD vk _ _ hsub (Finset.mem_filter.mp hq).2
          have ht2 := hmonoD uk _ _ hsub (Finset.mem_filter.mp huk_p).2
          have hvalP := hvalD_gate k (x7 {p_c})
          rw [hkop, hinps] at hvalP
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
          change valD (28 + k.val) (x7 {p_c}) = (valD (in0 k) (x7 {p_c}) && valD (in1 k) (x7 {p_c})) at hvalP
          rcases hvkuk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [ht1, ht2] at hvalP; have h0 := hClean_x8 k hkop {p_c} (hSingle p_c); rw [h0] at hvalP; cases hvalP
          · rw [ht1, ht2] at hvalP; have h0 := hClean_x8 k hkop {p_c} (hSingle p_c); rw [h0] at hvalP; cases hvalP
        · rcases hvkuk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hpp (hNoCrossPt k hkop p' p_c hq huk_p)
          · exact hpp (hNoCrossPt k hkop p_c p' huk_p hq).symm
      have h_pt_branch : ∀ (s : Fin 2) (vk uk : ℕ),
          (s = 0 ∧ vk = in0 k ∧ uk = in1 k ∨ s = 1 ∧ vk = in1 k ∧ uk = in0 k) →
          vk ∈ ReachSet → Fin.castAdd 13 p_c ∈ Sings uk →
          Fin.natAdd 13 pl1.2 ∈ Sings vk → Fin.natAdd 13 pl2.2 ∈ Sings vk →
          ∃ side : Fin 2,
            let vk' := if side = 0 then in0 k else in1 k
            vk' ∈ ReachSet ∧ 26 ∉ orReach vk' ∧ (E_of k).card ≤ (Sings vk').card ∧
            (∀ pl ∈ E_of k, pl.1 = p_c ∧ Fin.natAdd 13 pl.2 ∈ Sings vk') ∧ (∀ q ∈ Sings vk', 13 ≤ q.val) := by
        intro s vk uk hs hvk_reach huk_p hl1_v hl2_v
        have h_all : ∀ pl ∈ E_of k, pl.1 = p_c ∧ Fin.natAdd 13 pl.2 ∈ Sings vk := by
          intro pl hpl
          refine ⟨hp0 pl hpl, ?_⟩
          have hs' := hOwner_sides_k k hk pl hpl
          rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · rcases hs' with ⟨_, hl⟩ | ⟨hl, _⟩
            · exfalso; exact hl_ne ((hNoCrossLine k hkop pl1.2 pl.2 hl1_v hl).trans (hNoCrossLine k hkop pl2.2 pl.2 hl2_v hl).symm)
            · exact hl
          · rcases hs' with ⟨_, hl⟩ | ⟨hl, _⟩
            · exact hl
            · exfalso; exact hl_ne ((hNoCrossLine k hkop pl.2 pl1.2 hl hl1_v).symm.trans (hNoCrossLine k hkop pl.2 pl2.2 hl hl2_v))
        have hinj : ∀ a ∈ E_of k, ∀ b ∈ E_of k, Fin.natAdd 13 a.2 = Fin.natAdd 13 b.2 → a = b := by
          intro a ha b hb heq
          have h2 : a.2 = b.2 := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
          exact Prod.ext ((hp0 a ha).trans (hp0 b hb).symm) h2
        have hcard_le : (E_of k).card ≤ (Sings vk).card :=
          Finset.card_le_card_of_injOn (fun pl => Fin.natAdd 13 pl.2) (fun pl hpl => (h_all pl hpl).2) hinj
        have hvk_no26 : 26 ∉ orReach vk := by
          rcases hs with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
          · exact hno26_of_sing (in0 k) (in1 k) (Or.inl ⟨rfl, rfl⟩) ⟨_, huk_p⟩
          · exact hno26_of_sing (in1 k) (in0 k) (Or.inr ⟨rfl, rfl⟩) ⟨_, huk_p⟩
        have hvk_no_pt : ∀ q ∈ Sings vk, 13 ≤ q.val := by
          rcases hs with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
          · exact h_no_pt (in0 k) (in1 k) (Or.inl ⟨rfl, rfl⟩) huk_p
          · exact h_no_pt (in1 k) (in0 k) (Or.inr ⟨rfl, rfl⟩) huk_p
        rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact ⟨0, hvk_reach, hvk_no26, hcard_le, h_all, hvk_no_pt⟩
        · exact ⟨1, hvk_reach, hvk_no26, hcard_le, h_all, hvk_no_pt⟩
      rcases hs1 with ⟨hp1_0, hl1_1⟩ | ⟨hl1_0, hp1_1⟩ <;> rcases hs2 with ⟨hp2_0, hl2_1⟩ | ⟨hl2_0, hp2_1⟩
      · exact h_pt_branch 1 (in1 k) (in0 k) (Or.inr ⟨rfl, rfl, rfl⟩) hin1_reach (hp1 ▸ hp1_0) hl1_1 hl2_1
      · exact absurd (hNoCrossLine k hkop pl2.2 pl1.2 hl2_0 hl1_1).symm hl_ne
      · exact absurd (hNoCrossLine k hkop pl1.2 pl2.2 hl1_0 hl2_1) hl_ne
      · exact h_pt_branch 0 (in0 k) (in1 k) (Or.inl ⟨rfl, rfl, rfl⟩) hin0_reach (hp1 ▸ hp1_1) hl1_0 hl2_0
    · have hl0 := ((hStar_center k hk).resolve_left hp).choose_spec
      set l_c := ((hStar_center k hk).resolve_left hp).choose
      have hl1 : pl1.2 = l_c := hl0 pl1 hpl1
      have hl2 : pl2.2 = l_c := hl0 pl2 hpl2
      have hp_ne : pl1.1 ≠ pl2.1 := fun h => hne (Prod.ext h (hl1.trans hl2.symm))
      have h_no_line : ∀ (vk uk : ℕ), (vk = in0 k ∧ uk = in1 k ∨ vk = in1 k ∧ uk = in0 k) →
          Fin.natAdd 13 l_c ∈ Sings uk → ∀ q ∈ Sings vk, q.val < 13 := by
        intro vk uk hvkuk huk_l q hq
        by_contra hge13
        have hlt : q.val - 13 < 13 := by omega
        let l' : Fin 13 := ⟨q.val - 13, hlt⟩
        have hqeq : q = Fin.natAdd 13 l' := by ext; simp [l']; omega
        rw [hqeq] at hq
        by_cases hll : l' = l_c
        · rw [hll] at hq
          let P := Finset.univ.filter (fun p : Fin 13 => ¬x3 p l_c)
          have hsub : ∀ r : Fin 26, sing (Fin.natAdd 13 l_c) r = true → x7 P r = true := by
            intro r hr; simp only [sing, decide_eq_true_eq] at hr; subst hr; dsimp only [x7]; rw [decide_eq_true_eq]
            right; exact ⟨l_c, rfl, fun p hp => (Finset.mem_filter.mp hp).2⟩
          have ht1 := hmonoD vk _ _ hsub (Finset.mem_filter.mp hq).2
          have ht2 := hmonoD uk _ _ hsub (Finset.mem_filter.mp huk_l).2
          have hvalP := hvalD_gate k (x7 P)
          rw [hkop, hinps] at hvalP
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true] at hvalP
          change valD (28 + k.val) (x7 P) = (valD (in0 k) (x7 P) && valD (in1 k) (x7 P)) at hvalP
          rcases hvkuk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [ht1, ht2] at hvalP; have h0 := hClean_x8 k hkop P (hAvoidLine l_c); rw [h0] at hvalP; cases hvalP
          · rw [ht1, ht2] at hvalP; have h0 := hClean_x8 k hkop P (hAvoidLine l_c); rw [h0] at hvalP; cases hvalP
        · rcases hvkuk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hll (hNoCrossLine k hkop l' l_c hq huk_l)
          · exact hll (hNoCrossLine k hkop l_c l' huk_l hq).symm
      have h_line_branch : ∀ (s : Fin 2) (vk uk : ℕ),
          (s = 0 ∧ vk = in0 k ∧ uk = in1 k ∨ s = 1 ∧ vk = in1 k ∧ uk = in0 k) →
          vk ∈ ReachSet → Fin.natAdd 13 l_c ∈ Sings uk →
          Fin.castAdd 13 pl1.1 ∈ Sings vk → Fin.castAdd 13 pl2.1 ∈ Sings vk →
          ∃ side : Fin 2,
            let vk' := if side = 0 then in0 k else in1 k
            vk' ∈ ReachSet ∧ 26 ∉ orReach vk' ∧ (E_of k).card ≤ (Sings vk').card ∧
            (∀ pl ∈ E_of k, pl.2 = l_c ∧ Fin.castAdd 13 pl.1 ∈ Sings vk') ∧ (∀ q ∈ Sings vk', q.val < 13) := by
        intro s vk uk hs hvk_reach huk_l hp1_v hp2_v
        have h_all : ∀ pl ∈ E_of k, pl.2 = l_c ∧ Fin.castAdd 13 pl.1 ∈ Sings vk := by
          intro pl hpl
          refine ⟨hl0 pl hpl, ?_⟩
          have hs' := hOwner_sides_k k hk pl hpl
          rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · rcases hs' with ⟨hp', _⟩ | ⟨_, hp'⟩
            · exact hp'
            · exfalso; exact hp_ne ((hNoCrossPt k hkop pl1.1 pl.1 hp1_v hp').trans (hNoCrossPt k hkop pl2.1 pl.1 hp2_v hp').symm)
          · rcases hs' with ⟨hp', _⟩ | ⟨_, hp'⟩
            · exfalso; exact hp_ne ((hNoCrossPt k hkop pl.1 pl1.1 hp' hp1_v).symm.trans (hNoCrossPt k hkop pl.1 pl2.1 hp' hp2_v))
            · exact hp'
        have hinj : ∀ a ∈ E_of k, ∀ b ∈ E_of k, Fin.castAdd 13 a.1 = Fin.castAdd 13 b.1 → a = b := by
          intro a ha b hb heq
          have h1 : a.1 = b.1 := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
          exact Prod.ext h1 ((hl0 a ha).trans (hl0 b hb).symm)
        have hcard_le : (E_of k).card ≤ (Sings vk).card :=
          Finset.card_le_card_of_injOn (fun pl => Fin.castAdd 13 pl.1) (fun pl hpl => (h_all pl hpl).2) hinj
        have hvk_no26 : 26 ∉ orReach vk := by
          rcases hs with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
          · exact hno26_of_sing (in0 k) (in1 k) (Or.inl ⟨rfl, rfl⟩) ⟨_, huk_l⟩
          · exact hno26_of_sing (in1 k) (in0 k) (Or.inr ⟨rfl, rfl⟩) ⟨_, huk_l⟩
        have hvk_no_line : ∀ q ∈ Sings vk, q.val < 13 := by
          rcases hs with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
          · exact h_no_line (in0 k) (in1 k) (Or.inl ⟨rfl, rfl⟩) huk_l
          · exact h_no_line (in1 k) (in0 k) (Or.inr ⟨rfl, rfl⟩) huk_l
        rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact ⟨0, hvk_reach, hvk_no26, hcard_le, h_all, hvk_no_line⟩
        · exact ⟨1, hvk_reach, hvk_no26, hcard_le, h_all, hvk_no_line⟩
      rcases hs1 with ⟨hp1_0, hl1_1⟩ | ⟨hl1_0, hp1_1⟩ <;> rcases hs2 with ⟨hp2_0, hl2_1⟩ | ⟨hl2_0, hp2_1⟩
      · exact h_line_branch 0 (in0 k) (in1 k) (Or.inl ⟨rfl, rfl, rfl⟩) hin0_reach (hl1 ▸ hl1_1) hp1_0 hp2_0
      · exact absurd (hNoCrossPt k hkop pl1.1 pl2.1 hp1_0 hp2_1) hp_ne
      · exact absurd (hNoCrossPt k hkop pl2.1 pl1.1 hp2_0 hp1_1).symm hp_ne
      · exact h_line_branch 1 (in1 k) (in0 k) (Or.inr ⟨rfl, rfl, rfl⟩) hin1_reach (hl1 ▸ hl1_0) hp1_1 hp2_1
  let starSide : Fin D.gates.length → ℕ := fun k => by
    classical
    exact if hk : k ∈ Owned ∧ 2 ≤ (E_of k).card then
      let side := (hStar_side k hk.1 hk.2).choose
      if side = 0 then in0 k else in1 k
    else 27
  let I_of : Fin D.gates.length → Finset (Fin D.gates.length) := fun k => by
    classical
    exact if hk : k ∈ Owned ∧ 2 ≤ (E_of k).card then
      Finset.univ.filter (fun g => 28 + g.val ∈ orReach (starSide k) ∧ 2 ≤ (Sings (28 + g.val)).card)
    else ∅
  let G_c : (Fin 13 ⊕ Fin 13) → Finset (Fin D.gates.length) := fun c =>
    (Owned.filter (fun k => center k = c)).biUnion I_of
  have hSings_orReach_sub : ∀ w j, j ∈ orReach w → Sings j ⊆ Sings w := by
    intro w j hj q hq
    simp only [Sings, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact horReach_mono w j hj (sing q) hq
  have hG_disjoint : ∀ c1 c2 : Fin 13 ⊕ Fin 13, c1 ≠ c2 → Disjoint (G_c c1) (G_c c2) := by
    intro c1 c2 hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    simp only [G_c, Finset.mem_biUnion, Finset.mem_filter] at hg1 hg2
    obtain ⟨k1, ⟨hk1_own, hc1⟩, hg1_I⟩ := hg1
    obtain ⟨k2, ⟨hk2_own, hc2⟩, hg2_I⟩ := hg2
    dsimp only [I_of] at hg1_I hg2_I
    split_ifs at hg1_I with h1; swap; exact Finset.notMem_empty _ hg1_I
    split_ifs at hg2_I with h2; swap; exact Finset.notMem_empty _ hg2_I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg1_I hg2_I
    obtain ⟨hg1_reach, hg1_card⟩ := hg1_I
    obtain ⟨hg2_reach, _⟩ := hg2_I
    obtain ⟨q1, hq1, q2, hq2, hqne⟩ := Finset.one_lt_card.mp hg1_card
    have hsp1 := (hStar_side k1 hk1_own h1.2).choose_spec
    have hsp2 := (hStar_side k2 hk2_own h2.2).choose_spec
    have hvk1_eq : starSide k1 = if (hStar_side k1 hk1_own h1.2).choose = 0 then in0 k1 else in1 k1 := by
      dsimp only [starSide]; rw [dif_pos h1]
    have hvk2_eq : starSide k2 = if (hStar_side k2 hk2_own h2.2).choose = 0 then in0 k2 else in1 k2 := by
      dsimp only [starSide]; rw [dif_pos h2]
    rw [← hvk1_eq] at hsp1
    rw [← hvk2_eq] at hsp2
    have hq1_1 : q1 ∈ Sings (starSide k1) := hSings_orReach_sub _ _ hg1_reach hq1
    have hq2_1 : q2 ∈ Sings (starSide k1) := hSings_orReach_sub _ _ hg1_reach hq2
    have hq1_2 : q1 ∈ Sings (starSide k2) := hSings_orReach_sub _ _ hg2_reach hq1
    have hq2_2 : q2 ∈ Sings (starSide k2) := hSings_orReach_sub _ _ hg2_reach hq2
    obtain ⟨p1_0, l1_0, hpl1_0, ho1_0⟩ := (Finset.mem_filter.mp hk1_own).2
    obtain ⟨p2_0, l2_0, hpl2_0, ho2_0⟩ := (Finset.mem_filter.mp hk2_own).2
    have hkop1 : (D.gates.get k1).op = .and := ho1_0 ▸ (howner_spec p1_0 l1_0 hpl1_0).1
    have hkop2 : (D.gates.get k2).op = .and := ho2_0 ▸ (howner_spec p2_0 l2_0 hpl2_0).1
    have hother_pt : ∀ (k : Fin D.gates.length) (hk : k ∈ Owned) (h2 : 2 ≤ (E_of k).card) (p_c : Fin 13), center k = Sum.inl p_c →
        Fin.castAdd 13 p_c ∈ Sings (if (hStar_side k hk h2).choose = 0 then in1 k else in0 k) := by
      intro k hk h2 p_c hck
      have hm : (∀ pl ∈ E_of k, pl.1 = p_c ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
          ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), 13 ≤ q.val := by
        have h := (hStar_side k hk h2).choose_spec.2.2.2
        have helim : ∀ (x : Fin 13 ⊕ Fin 13) (p_c : Fin 13), x = Sum.inl p_c →
            (match x with
              | Sum.inl p0 => (∀ pl ∈ E_of k, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
                ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), 13 ≤ q.val
              | Sum.inr l0 => (∀ pl ∈ E_of k, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
                ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), q.val < 13) →
            (∀ pl ∈ E_of k, pl.1 = p_c ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
              ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), 13 ≤ q.val := by
          rintro (p0 | l0) p_c hxe hx
          · cases hxe; exact hx
          · cases hxe
        exact helim (center k) p_c hck h
      obtain ⟨pl, hpl⟩ := Finset.card_pos.mp (by omega : 0 < (E_of k).card)
      have hp_eq := (hm.1 pl hpl).1
      have hs := hOwner_sides_k k hk pl hpl
      rw [hp_eq] at hs
      by_cases hch : (hStar_side k hk h2).choose = 0
      · rw [if_pos hch]
        rcases hs with ⟨hp', _⟩ | ⟨_, hp'⟩
        · exfalso; exact absurd (hm.2 (Fin.castAdd 13 p_c) (by rw [if_pos hch]; exact hp')) (by simp)
        · exact hp'
      · rw [if_neg hch]
        rcases hs with ⟨hp', _⟩ | ⟨_, hp'⟩
        · exact hp'
        · exfalso; exact absurd (hm.2 (Fin.castAdd 13 p_c) (by rw [if_neg hch]; exact hp')) (by simp)
    have hother_line : ∀ (k : Fin D.gates.length) (hk : k ∈ Owned) (h2 : 2 ≤ (E_of k).card) (l_c : Fin 13), center k = Sum.inr l_c →
        Fin.natAdd 13 l_c ∈ Sings (if (hStar_side k hk h2).choose = 0 then in1 k else in0 k) := by
      intro k hk h2 l_c hck
      have hm : (∀ pl ∈ E_of k, pl.2 = l_c ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
          ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), q.val < 13 := by
        have h := (hStar_side k hk h2).choose_spec.2.2.2
        have helim : ∀ (x : Fin 13 ⊕ Fin 13) (l_c : Fin 13), x = Sum.inr l_c →
            (match x with
              | Sum.inl p0 => (∀ pl ∈ E_of k, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
                ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), 13 ≤ q.val
              | Sum.inr l0 => (∀ pl ∈ E_of k, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
                ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), q.val < 13) →
            (∀ pl ∈ E_of k, pl.2 = l_c ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k)) ∧
              ∀ q ∈ Sings (if (hStar_side k hk h2).choose = 0 then in0 k else in1 k), q.val < 13 := by
          rintro (p0 | l0) l_c hxe hx
          · cases hxe
          · cases hxe; exact hx
        exact helim (center k) l_c hck h
      obtain ⟨pl, hpl⟩ := Finset.card_pos.mp (by omega : 0 < (E_of k).card)
      have hl_eq := (hm.1 pl hpl).1
      have hs := hOwner_sides_k k hk pl hpl
      rw [hl_eq] at hs
      by_cases hch : (hStar_side k hk h2).choose = 0
      · rw [if_pos hch]
        rcases hs with ⟨_, hl'⟩ | ⟨hl', _⟩
        · exact hl'
        · exfalso; exact absurd (hm.2 (Fin.natAdd 13 l_c) (by rw [if_pos hch]; exact hl')) (by simp)
      · rw [if_neg hch]
        rcases hs with ⟨_, hl'⟩ | ⟨hl', _⟩
        · exfalso; exact absurd (hm.2 (Fin.natAdd 13 l_c) (by rw [if_neg hch]; exact hl')) (by simp)
        · exact hl'
    cases hc1_eq : center k1 with
    | inl p1 =>
      rw [hc1_eq] at hsp1
      have h13_1 := hsp1.2.2.2.2 q1 hq1_1
      have h13_2 := hsp1.2.2.2.2 q2 hq2_1
      cases hc2_eq : center k2 with
      | inr l2 => rw [hc2_eq] at hsp2; have hlt := hsp2.2.2.2.2 q1 hq1_2; omega
      | inl p2 =>
        rw [hc2_eq] at hsp2
        have hpne : p1 ≠ p2 := fun h => hne (hc1.symm.trans (hc1_eq.trans (h ▸ hc2_eq.symm.trans hc2)))
        let l1 : Fin 13 := ⟨q1.val - 13, by omega⟩
        let l2 : Fin 13 := ⟨q2.val - 13, by omega⟩
        have hlne : l1 ≠ l2 := fun h => hqne (Fin.ext (by have := congrArg Fin.val h; simp [l1, l2] at this; omega))
        have hq1_eq : q1 = Fin.natAdd 13 l1 := Fin.ext (by simp [l1]; omega)
        have hq2_eq : q2 = Fin.natAdd 13 l2 := Fin.ext (by simp [l2]; omega)
        have hk1_other := hother_pt k1 hk1_own h1.2 p1 hc1_eq
        have hk2_other := hother_pt k2 hk2_own h2.2 p2 hc2_eq
        have hk1_acc : ∀ l : Fin 13, Fin.natAdd 13 l ∈ Sings (starSide k1) → x3 p1 l := by
          intro l hl
          apply hvalD_edge_sound k1 hkop1 p1 l
          apply hAnd_pair k1 hkop1 p1 l
          rw [hvk1_eq] at hl
          by_cases hch : (hStar_side k1 hk1_own h1.2).choose = 0
          · rw [if_pos hch] at hl hk1_other; exact Or.inr ⟨hl, hk1_other⟩
          · rw [if_neg hch] at hl hk1_other; exact Or.inl ⟨hk1_other, hl⟩
        have hk2_acc : ∀ l : Fin 13, Fin.natAdd 13 l ∈ Sings (starSide k2) → x3 p2 l := by
          intro l hl
          apply hvalD_edge_sound k2 hkop2 p2 l
          apply hAnd_pair k2 hkop2 p2 l
          rw [hvk2_eq] at hl
          by_cases hch : (hStar_side k2 hk2_own h2.2).choose = 0
          · rw [if_pos hch] at hl hk2_other; exact Or.inr ⟨hl, hk2_other⟩
          · rw [if_neg hch] at hl hk2_other; exact Or.inl ⟨hk2_other, hl⟩
        rcases hNoC4 p1 p2 l1 l2 hpne hlne (hk1_acc l1 (hq1_eq ▸ hq1_1)) (hk2_acc l2 (hq2_eq ▸ hq2_2)) with h | h
        · exact h (hk1_acc l2 (hq2_eq ▸ hq2_1))
        · exact h (hk2_acc l1 (hq1_eq ▸ hq1_2))
    | inr l1 =>
      rw [hc1_eq] at hsp1
      have h13_1 := hsp1.2.2.2.2 q1 hq1_1
      have h13_2 := hsp1.2.2.2.2 q2 hq2_1
      cases hc2_eq : center k2 with
      | inl p2 => rw [hc2_eq] at hsp2; have hge := hsp2.2.2.2.2 q1 hq1_2; omega
      | inr l2 =>
        rw [hc2_eq] at hsp2
        have hlne : l1 ≠ l2 := fun h => hne (hc1.symm.trans (hc1_eq.trans (h ▸ hc2_eq.symm.trans hc2)))
        let p1 : Fin 13 := ⟨q1.val, h13_1⟩
        let p2 : Fin 13 := ⟨q2.val, h13_2⟩
        have hpne : p1 ≠ p2 := fun h => hqne (Fin.ext (by have := congrArg Fin.val h; simp [p1, p2] at this; exact this))
        have hq1_eq : q1 = Fin.castAdd 13 p1 := Fin.ext (by simp [p1])
        have hq2_eq : q2 = Fin.castAdd 13 p2 := Fin.ext (by simp [p2])
        have hk1_other := hother_line k1 hk1_own h1.2 l1 hc1_eq
        have hk2_other := hother_line k2 hk2_own h2.2 l2 hc2_eq
        have hk1_acc : ∀ p : Fin 13, Fin.castAdd 13 p ∈ Sings (starSide k1) → x3 p l1 := by
          intro p hp
          apply hvalD_edge_sound k1 hkop1 p l1
          apply hAnd_pair k1 hkop1 p l1
          rw [hvk1_eq] at hp
          by_cases hch : (hStar_side k1 hk1_own h1.2).choose = 0
          · rw [if_pos hch] at hp hk1_other; exact Or.inl ⟨hp, hk1_other⟩
          · rw [if_neg hch] at hp hk1_other; exact Or.inr ⟨hk1_other, hp⟩
        have hk2_acc : ∀ p : Fin 13, Fin.castAdd 13 p ∈ Sings (starSide k2) → x3 p l2 := by
          intro p hp
          apply hvalD_edge_sound k2 hkop2 p l2
          apply hAnd_pair k2 hkop2 p l2
          rw [hvk2_eq] at hp
          by_cases hch : (hStar_side k2 hk2_own h2.2).choose = 0
          · rw [if_pos hch] at hp hk2_other; exact Or.inl ⟨hp, hk2_other⟩
          · rw [if_neg hch] at hp hk2_other; exact Or.inr ⟨hk2_other, hp⟩
        rcases hNoC4 p1 p2 l1 l2 hpne hlne (hk1_acc p1 (hq1_eq ▸ hq1_1)) (hk2_acc p2 (hq2_eq ▸ hq2_2)) with h | h
        · exact h (hk2_acc p1 (hq1_eq ▸ hq1_2))
        · exact h (hk1_acc p2 (hq2_eq ▸ hq2_1))
  have horReach_parent : ∀ w j, j ∈ orReach w → j ≠ w →
      ∃ g : Fin D.gates.length, 28 + g.val ∈ orReach w ∧ (D.gates.get g).op = .or ∧ (j = in0 g ∨ j = in1 g) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj hjne
      by_cases hw : 28 ≤ w ∧ w - 28 < D.gates.length
      · have hwpos : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        obtain ⟨w', hw'⟩ := hwpos
        have h1 : orReach w = orReachFuel (w' + 1) w := by dsimp only [orReach]; rw [← hw']
        rw [h1] at hj
        dsimp only [orReachFuel] at hj
        rw [dif_pos (by omega)] at hj
        let kw : Fin D.gates.length := ⟨w - 28, hw.2⟩
        cases hop : (D.gates.get kw).op with
        | or =>
          have hlenw := (hDShape kw).1
          let uw := (D.gates.get kw).inputs[0]'(by omega)
          let vw := (D.gates.get kw).inputs[1]'(by omega)
          have huw : uw < w := by have := (hDShape kw).2 uw (List.getElem_mem _); dsimp [kw] at this; omega
          have hvw : vw < w := by have := (hDShape kw).2 vw (List.getElem_mem _); dsimp [kw] at this; omega
          simp only [kw, hop] at hj
          change j ∈ insert w (orReachFuel w' uw ∪ orReachFuel w' vw) at hj
          rw [horReach_fuel_eq w' uw uw (by omega) (le_refl _), horReach_fuel_eq w' vw vw (by omega) (le_refl _)] at hj
          simp only [Finset.mem_insert, Finset.mem_union] at hj
          have hin0_kw : in0 kw = uw := rfl
          have hin1_kw : in1 kw = vw := rfl
          rcases hj with rfl | hj | hj
          · exact absurd rfl hjne
          · by_cases hju : j = uw
            · exact ⟨kw, by rw [show 28 + kw.val = w from by dsimp [kw]; omega]; exact horReach_mem_self w, hop, Or.inl (hju.trans hin0_kw.symm)⟩
            · obtain ⟨g, hg_mem, hg_op, hg_inp⟩ := ih uw huw j hj hju
              have hg_sub : orReach uw ⊆ orReach w := by
                intro x hx
                rw [h1]; dsimp only [orReachFuel]; rw [dif_pos (by omega)]
                simp only [kw, hop]
                change x ∈ insert w (orReachFuel w' uw ∪ orReachFuel w' vw)
                rw [horReach_fuel_eq w' uw uw (by omega) (le_refl _)]
                exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
              exact ⟨g, hg_sub hg_mem, hg_op, hg_inp⟩
          · by_cases hjv : j = vw
            · exact ⟨kw, by rw [show 28 + kw.val = w from by dsimp [kw]; omega]; exact horReach_mem_self w, hop, Or.inr (hjv.trans hin1_kw.symm)⟩
            · obtain ⟨g, hg_mem, hg_op, hg_inp⟩ := ih vw hvw j hj hjv
              have hg_sub : orReach vw ⊆ orReach w := by
                intro x hx
                rw [h1]; dsimp only [orReachFuel]; rw [dif_pos (by omega)]
                simp only [kw, hop]
                change x ∈ insert w (orReachFuel w' uw ∪ orReachFuel w' vw)
                rw [horReach_fuel_eq w' vw vw (by omega) (le_refl _)]
                exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
              exact ⟨g, hg_sub hg_mem, hg_op, hg_inp⟩
        | _ =>
          simp only [kw, hop, Finset.mem_singleton] at hj
          exact absurd hj hjne
      · have hzero : orReach w = {w} := by
          dsimp only [orReach]
          cases w with
          | zero => simp [orReachFuel]
          | succ w' => dsimp only [orReachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        exact absurd hj hjne
  have hreach_parent : ∀ w j, j ∈ reach w → j ≠ w →
      ∃ g : Fin D.gates.length, 28 + g.val ∈ reach w ∧ (j = in0 g ∨ j = in1 g) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro j hj hjne
      by_cases hw : 28 ≤ w ∧ w - 28 < D.gates.length
      · rw [hreach_unfold w hw] at hj
        let kw : Fin D.gates.length := ⟨w - 28, hw.2⟩
        have hlenw := (hDShape kw).1
        let uw := (D.gates.get kw).inputs[0]'(by omega)
        let vw := (D.gates.get kw).inputs[1]'(by omega)
        have huw : uw < w := by have := (hDShape kw).2 uw (List.getElem_mem _); dsimp [kw] at this; omega
        have hvw : vw < w := by have := (hDShape kw).2 vw (List.getElem_mem _); dsimp [kw] at this; omega
        simp only [Finset.mem_insert, Finset.mem_union] at hj
        have hin0_kw : in0 kw = uw := rfl
        have hin1_kw : in1 kw = vw := rfl
        rcases hj with rfl | hj | hj
        · exact absurd rfl hjne
        · by_cases hju : j = uw
          · exact ⟨kw, by rw [show 28 + kw.val = w from by dsimp [kw]; omega]; exact hreach_mem_self w, Or.inl (hju.trans hin0_kw.symm)⟩
          · obtain ⟨g, hg_mem, hg_inp⟩ := ih uw huw j hj hju
            have hg_sub : reach uw ⊆ reach w := hreach_trans w uw (by rw [hreach_unfold w hw]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hreach_mem_self _)))
            exact ⟨g, hg_sub hg_mem, hg_inp⟩
        · by_cases hjv : j = vw
          · exact ⟨kw, by rw [show 28 + kw.val = w from by dsimp [kw]; omega]; exact hreach_mem_self w, Or.inr (hjv.trans hin1_kw.symm)⟩
          · obtain ⟨g, hg_mem, hg_inp⟩ := ih vw hvw j hj hjv
            have hg_sub : reach vw ⊆ reach w := hreach_trans w vw (by rw [hreach_unfold w hw]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hreach_mem_self _)))
            exact ⟨g, hg_sub hg_mem, hg_inp⟩
      · have hzero : reach w = {w} := by
          dsimp only [reach]
          cases w with
          | zero => simp [reachFuel]
          | succ w' => dsimp only [reachFuel]; rw [dif_neg (by omega)]
        rw [hzero, Finset.mem_singleton] at hj
        exact absurd hj hjne
  let inZ : ℕ → ℕ := fun w => by
    classical
    exact if ∃ z ∈ Z, 28 + z.val = w then 1 else 0
  let Z_in : Finset (Fin D.gates.length) → ℕ := fun S => ∑ g ∈ S, (inZ (in0 g) + inZ (in1 g))
  let inS : Finset (Fin D.gates.length) → ℕ → ℕ := fun S w => by
    classical
    exact if ∃ g ∈ S, 28 + g.val = w then 1 else 0
  have hSings_or_in : ∀ g : Fin D.gates.length, (D.gates.get g).op = .or →
      Sings (28 + g.val) = Sings (in0 g) ∪ Sings (in1 g) := fun g hg => hSings_or g hg
  have hSings_lt_card : ∀ n (hn : n < 26), (Sings n).card = 1 := fun n hn => by
    rw [show n = (⟨n, hn⟩ : Fin 26).val from rfl, hSings_lt ⟨n, hn⟩, Finset.card_singleton]
  have hstarSide_spec : ∀ (k : Fin D.gates.length) (hk : k ∈ Owned) (hk2 : 2 ≤ (E_of k).card),
      starSide k ∈ ReachSet ∧ 26 ∉ orReach (starSide k) ∧ (E_of k).card ≤ (Sings (starSide k)).card ∧
      (match center k with
       | Sum.inl p0 => (∀ pl ∈ E_of k, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (starSide k)) ∧ (∀ q ∈ Sings (starSide k), 13 ≤ q.val)
       | Sum.inr l0 => (∀ pl ∈ E_of k, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (starSide k)) ∧ (∀ q ∈ Sings (starSide k), q.val < 13)) := by
    intro k hk hk2
    have hvk : starSide k = if (hStar_side k hk hk2).choose = 0 then in0 k else in1 k := by
      dsimp only [starSide]; rw [dif_pos ⟨hk, hk2⟩]
    rw [hvk]
    exact (hStar_side k hk hk2).choose_spec
  have hG_prop : ∀ c g, g ∈ G_c c → 28 + g.val ∈ ReachSet ∧ (D.gates.get g).op = .or ∧ 2 ≤ (Sings (28 + g.val)).card := by
    intro c g hg
    simp only [G_c, Finset.mem_biUnion, Finset.mem_filter] at hg
    obtain ⟨k, ⟨hk_own, _⟩, hg_I⟩ := hg
    dsimp only [I_of] at hg_I
    split_ifs at hg_I with hk2; swap; exact absurd hg_I (Finset.notMem_empty _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg_I
    obtain ⟨hg_reach, hg_card⟩ := hg_I
    have hsp := hstarSide_spec k hk_own hk2.2
    have h_greach : 28 + g.val ∈ ReachSet := hReachSet_reach _ hsp.1 (horReach_sub_reach _ hg_reach)
    have h_gop : (D.gates.get g).op = .or := by
      rcases (hDMono (D.gates.get g) (List.get_mem _ _)).1 with hop | hop
      · exfalso; have := hSings_and g hop; rw [this, Finset.card_empty] at hg_card; omega
      · exact hop
    exact ⟨h_greach, h_gop, hg_card⟩
  have hG_card : ∀ c : Fin 13 ⊕ Fin 13,
      let O_c := Owned.filter (fun k => center k = c)
      ∑ k ∈ O_c, (E_of k).card + Z_in (G_c c) ≤ (G_c c).card + O_c.card := by
    intro c O_c
    let O_c2 := O_c.filter (fun k => 2 ≤ (E_of k).card)
    let O_c1 := O_c.filter (fun k => (E_of k).card = 1)
    have hO_split : O_c.card = O_c1.card + O_c2.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext k
        simp only [O_c1, O_c2, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hk
          have hpos : 1 ≤ (E_of k).card := by
            have hk_own : k ∈ Owned := (Finset.mem_filter.mp hk).1
            obtain ⟨p0, l0, hpl0, ho0⟩ := (Finset.mem_filter.mp hk_own).2
            exact Finset.card_pos.mpr ⟨(p0, l0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl0, ho0⟩⟩
          rcases (by omega : (E_of k).card = 1 ∨ 2 ≤ (E_of k).card) with h1 | h2
          · left; exact ⟨hk, h1⟩
          · right; exact ⟨hk, h2⟩
        · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
      · rw [Finset.disjoint_left]; intro k h1 h2; simp only [O_c1, O_c2, Finset.mem_filter] at h1 h2; omega
    have hSum_split : ∑ k ∈ O_c, (E_of k).card = O_c1.card + ∑ k ∈ O_c2, (E_of k).card := by
      have hpart : O_c = O_c1 ∪ O_c2 := by
        ext k; simp only [O_c1, O_c2, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hk
          have hpos : 1 ≤ (E_of k).card := by
            have hk_own : k ∈ Owned := (Finset.mem_filter.mp hk).1
            obtain ⟨p0, l0, hpl0, ho0⟩ := (Finset.mem_filter.mp hk_own).2
            exact Finset.card_pos.mpr ⟨(p0, l0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl0, ho0⟩⟩
          rcases (by omega : (E_of k).card = 1 ∨ 2 ≤ (E_of k).card) with h1 | h2
          · left; exact ⟨hk, h1⟩
          · right; exact ⟨hk, h2⟩
        · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
      have hdisj : Disjoint O_c1 O_c2 := by
        rw [Finset.disjoint_left]; intro k h1 h2; simp only [O_c1, O_c2, Finset.mem_filter] at h1 h2; omega
      rw [hpart, Finset.sum_union hdisj]
      have h1 : ∑ k ∈ O_c1, (E_of k).card = O_c1.card := by
        have h1' : ∑ k ∈ O_c1, (E_of k).card = ∑ _k ∈ O_c1, 1 := Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.mp hk).2)
        rw [h1', Finset.sum_const, smul_eq_mul, mul_one]
      omega
    have hstar_gate : ∀ k ∈ O_c2, ∃ gk : Fin D.gates.length, 28 + gk.val = starSide k ∧ gk ∈ G_c c := by
      intro k hk
      have hk_own : k ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
      have hk_c : center k = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
      have hk2 : 2 ≤ (E_of k).card := (Finset.mem_filter.mp hk).2
      have hsp := hstarSide_spec k hk_own hk2
      have hcard_vk : 2 ≤ (Sings (starSide k)).card := le_trans hk2 hsp.2.2.1
      have hge28 : 28 ≤ starSide k := by
        by_contra hlt28
        by_cases h27 : starSide k = 27
        · rw [h27, hSings_27, Finset.card_empty] at hcard_vk; exact absurd hcard_vk (by decide)
        · by_cases h26 : starSide k = 26
          · have hmem26 : 26 ∈ orReach (starSide k) := by rw [h26]; exact horReach_mem_self 26
            exact hsp.2.1 hmem26
          · have hlt26 : starSide k < 26 := by omega
            rw [hSings_lt_card _ hlt26] at hcard_vk; exact absurd hcard_vk (by decide)
      have hlt_len : starSide k - 28 < D.gates.length := by
        have hvk : starSide k = if (hStar_side k hk_own hk2).choose = 0 then in0 k else in1 k := by
          dsimp only [starSide]; rw [dif_pos ⟨hk_own, hk2⟩]
        have : starSide k < 28 + k.val := by
          rw [hvk]
          by_cases hch : (hStar_side k hk_own hk2).choose = 0
          · rw [if_pos hch]; exact (hDShape k).2 (in0 k) (List.getElem_mem _)
          · rw [if_neg hch]; exact (hDShape k).2 (in1 k) (List.getElem_mem _)
        omega
      let gk : Fin D.gates.length := ⟨starSide k - 28, hlt_len⟩
      have hgk_eq : 28 + gk.val = starSide k := by dsimp [gk]; omega
      refine ⟨gk, hgk_eq, ?_⟩
      simp only [G_c, Finset.mem_biUnion, Finset.mem_filter]
      refine ⟨k, ⟨hk_own, hk_c⟩, ?_⟩
      dsimp only [I_of]; rw [dif_pos ⟨hk_own, hk2⟩]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hgk_eq.symm ▸ horReach_mem_self _, hgk_eq.symm ▸ hcard_vk⟩
    let S_c : Finset (Fin 26) := (G_c c).biUnion (fun g => Sings (28 + g.val))
    have hE_le_Sc : ∑ k ∈ O_c2, (E_of k).card ≤ S_c.card := by
      have hdisjE : ∀ k1 ∈ O_c2, ∀ k2 ∈ O_c2, k1 ≠ k2 → Disjoint (E_of k1) (E_of k2) := by
        intro k1 _ k2 _ hne
        rw [Finset.disjoint_left]; intro pl h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
      rw [← Finset.card_biUnion hdisjE]
      cases hc : c with
      | inl p0 =>
        have hinj : ∀ a ∈ (O_c2.biUnion E_of : Finset (Fin 13 × Fin 13)), ∀ b ∈ (O_c2.biUnion E_of : Finset (Fin 13 × Fin 13)), Fin.natAdd 13 a.2 = Fin.natAdd 13 b.2 → a = b := by
          intro a ha b hb heq
          simp only [Finset.mem_coe, Finset.mem_biUnion] at ha hb
          obtain ⟨ka, hka, haE⟩ := ha
          obtain ⟨kb, hkb, hbE⟩ := hb
          have hka_own : ka ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hka).1).1
          have hka_c : center ka = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hka).1).2
          have hka2 : 2 ≤ (E_of ka).card := (Finset.mem_filter.mp hka).2
          have hkb_own : kb ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hkb).1).1
          have hkb_c : center kb = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hkb).1).2
          have hkb2 : 2 ≤ (E_of kb).card := (Finset.mem_filter.mp hkb).2
          have hspa := (hStar_side ka hka_own hka2).choose_spec
          have hspb := (hStar_side kb hkb_own hkb2).choose_spec
          have hma : (∀ pl ∈ E_of ka, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
              ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), 13 ≤ q.val := by
            have h := hspa.2.2.2
            have helim : ∀ x, x = Sum.inl p0 → (match x with
              | Sum.inl p => (∀ pl ∈ E_of ka, pl.1 = p ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
                ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), 13 ≤ q.val
              | Sum.inr l => (∀ pl ∈ E_of ka, pl.2 = l ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
                ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), q.val < 13) →
              (∀ pl ∈ E_of ka, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
                ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), 13 ≤ q.val := by
              rintro (p | l) hxe hx <;> cases hxe; exact hx
            exact helim (center ka) (hka_c.trans hc) h
          have hmb : (∀ pl ∈ E_of kb, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
              ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), 13 ≤ q.val := by
            have h := hspb.2.2.2
            have helim : ∀ x, x = Sum.inl p0 → (match x with
              | Sum.inl p => (∀ pl ∈ E_of kb, pl.1 = p ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
                ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), 13 ≤ q.val
              | Sum.inr l => (∀ pl ∈ E_of kb, pl.2 = l ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
                ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), q.val < 13) →
              (∀ pl ∈ E_of kb, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
                ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), 13 ≤ q.val := by
              rintro (p | l) hxe hx <;> cases hxe; exact hx
            exact helim (center kb) (hkb_c.trans hc) h
          have ha1 : a.1 = p0 := (hma.1 a haE).1
          have hb1 : b.1 = p0 := (hmb.1 b hbE).1
          have h2 : a.2 = b.2 := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
          exact Prod.ext (ha1.trans hb1.symm) h2
        refine Finset.card_le_card_of_injOn (fun pl => Fin.natAdd 13 pl.2) (fun pl hpl => ?_) hinj
        simp only [Finset.mem_coe, Finset.mem_biUnion] at hpl
        obtain ⟨k, hk, hplE⟩ := hpl
        obtain ⟨gk, hgk_eq, hgk_mem⟩ := hstar_gate k hk
        have hk_own : k ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
        have hk_c : center k = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
        have hk2 : 2 ≤ (E_of k).card := (Finset.mem_filter.mp hk).2
        have hm : (∀ pl ∈ E_of k, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), 13 ≤ q.val := by
          have h := (hstarSide_spec k hk_own hk2).2.2.2
          have helim : ∀ x, x = Sum.inl p0 → (match x with
            | Sum.inl p => (∀ pl ∈ E_of k, pl.1 = p ∧ Fin.natAdd 13 pl.2 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), 13 ≤ q.val
            | Sum.inr l => (∀ pl ∈ E_of k, pl.2 = l ∧ Fin.castAdd 13 pl.1 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), q.val < 13) →
            (∀ pl ∈ E_of k, pl.1 = p0 ∧ Fin.natAdd 13 pl.2 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), 13 ≤ q.val := by
            rintro (p | l) hxe hx <;> cases hxe; exact hx
          exact helim (center k) (hk_c.trans hc) h
        exact Finset.mem_biUnion.mpr ⟨gk, hgk_mem, hgk_eq.symm ▸ (hm.1 pl hplE).2⟩
      | inr l0 =>
        have hinj : ∀ a ∈ (O_c2.biUnion E_of : Finset (Fin 13 × Fin 13)), ∀ b ∈ (O_c2.biUnion E_of : Finset (Fin 13 × Fin 13)), Fin.castAdd 13 a.1 = Fin.castAdd 13 b.1 → a = b := by
          intro a ha b hb heq
          simp only [Finset.mem_coe, Finset.mem_biUnion] at ha hb
          obtain ⟨ka, hka, haE⟩ := ha
          obtain ⟨kb, hkb, hbE⟩ := hb
          have hka_own : ka ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hka).1).1
          have hka_c : center ka = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hka).1).2
          have hka2 : 2 ≤ (E_of ka).card := (Finset.mem_filter.mp hka).2
          have hkb_own : kb ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hkb).1).1
          have hkb_c : center kb = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hkb).1).2
          have hkb2 : 2 ≤ (E_of kb).card := (Finset.mem_filter.mp hkb).2
          have hspa := (hStar_side ka hka_own hka2).choose_spec
          have hspb := (hStar_side kb hkb_own hkb2).choose_spec
          have hma : (∀ pl ∈ E_of ka, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
              ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), q.val < 13 := by
            have h := hspa.2.2.2
            have helim : ∀ x, x = Sum.inr l0 → (match x with
              | Sum.inl p => (∀ pl ∈ E_of ka, pl.1 = p ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
                ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), 13 ≤ q.val
              | Sum.inr l => (∀ pl ∈ E_of ka, pl.2 = l ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
                ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), q.val < 13) →
              (∀ pl ∈ E_of ka, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka)) ∧
                ∀ q ∈ Sings (if (hStar_side ka hka_own hka2).choose = 0 then in0 ka else in1 ka), q.val < 13 := by
              rintro (p | l) hxe hx <;> cases hxe; exact hx
            exact helim (center ka) (hka_c.trans hc) h
          have hmb : (∀ pl ∈ E_of kb, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
              ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), q.val < 13 := by
            have h := hspb.2.2.2
            have helim : ∀ x, x = Sum.inr l0 → (match x with
              | Sum.inl p => (∀ pl ∈ E_of kb, pl.1 = p ∧ Fin.natAdd 13 pl.2 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
                ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), 13 ≤ q.val
              | Sum.inr l => (∀ pl ∈ E_of kb, pl.2 = l ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
                ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), q.val < 13) →
              (∀ pl ∈ E_of kb, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb)) ∧
                ∀ q ∈ Sings (if (hStar_side kb hkb_own hkb2).choose = 0 then in0 kb else in1 kb), q.val < 13 := by
              rintro (p | l) hxe hx <;> cases hxe; exact hx
            exact helim (center kb) (hkb_c.trans hc) h
          have ha2 : a.2 = l0 := (hma.1 a haE).1
          have hb2 : b.2 = l0 := (hmb.1 b hbE).1
          have h1 : a.1 = b.1 := Fin.ext (by have := congrArg Fin.val heq; simp at this; omega)
          exact Prod.ext h1 (ha2.trans hb2.symm)
        refine Finset.card_le_card_of_injOn (fun pl => Fin.castAdd 13 pl.1) (fun pl hpl => ?_) hinj
        simp only [Finset.mem_coe, Finset.mem_biUnion] at hpl
        obtain ⟨k, hk, hplE⟩ := hpl
        obtain ⟨gk, hgk_eq, hgk_mem⟩ := hstar_gate k hk
        have hk_own : k ∈ Owned := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
        have hk_c : center k = c := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
        have hk2 : 2 ≤ (E_of k).card := (Finset.mem_filter.mp hk).2
        have hm : (∀ pl ∈ E_of k, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), q.val < 13 := by
          have h := (hstarSide_spec k hk_own hk2).2.2.2
          have helim : ∀ x, x = Sum.inr l0 → (match x with
            | Sum.inl p => (∀ pl ∈ E_of k, pl.1 = p ∧ Fin.natAdd 13 pl.2 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), 13 ≤ q.val
            | Sum.inr l => (∀ pl ∈ E_of k, pl.2 = l ∧ Fin.castAdd 13 pl.1 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), q.val < 13) →
            (∀ pl ∈ E_of k, pl.2 = l0 ∧ Fin.castAdd 13 pl.1 ∈ Sings (starSide k)) ∧ ∀ q ∈ Sings (starSide k), q.val < 13 := by
            rintro (p | l) hxe hx <;> cases hxe; exact hx
          exact helim (center k) (hk_c.trans hc) h
        exact Finset.mem_biUnion.mpr ⟨gk, hgk_mem, hgk_eq.symm ▸ (hm.1 pl hplE).2⟩
    have hSlot_le1 : ∀ g ∈ G_c c, ∀ w, inZ w + inS (G_c c) w ≤ 1 := by
      intro g _ w
      dsimp only [inZ, inS]
      by_cases hz : ∃ z ∈ Z, 28 + z.val = w
      · obtain ⟨z, hz_mem, rfl⟩ := hz
        have hnoS : ¬∃ g' ∈ G_c c, 28 + g'.val = 28 + z.val := by
          rintro ⟨g', hg', heq⟩
          have hg_eq : g' = z := Fin.ext (by omega)
          have hcard := (hG_prop c g' hg').2.2
          have hemp : Sings (28 + z.val) = ∅ := (Finset.mem_filter.mp hz_mem).2
          rw [hg_eq, hemp, Finset.card_empty] at hcard; omega
        rw [if_pos ⟨z, hz_mem, rfl⟩, if_neg hnoS]
      · rw [if_neg hz, Nat.zero_add]
        by_cases hs : ∃ g' ∈ G_c c, 28 + g'.val = w
        · rw [if_pos hs]
        · rw [if_neg hs]; decide
    have hSc_le_free : S_c.card ≤ ∑ g ∈ G_c c, ((1 - inZ (in0 g) - inS (G_c c) (in0 g)) + (1 - inZ (in1 g) - inS (G_c c) (in1 g))) := by
      have hfree_eq : ∑ g ∈ G_c c, ((1 - inZ (in0 g) - inS (G_c c) (in0 g)) + (1 - inZ (in1 g) - inS (G_c c) (in1 g))) =
          ((G_c c ×ˢ ({0, 1} : Finset (Fin 2))).filter (fun gp =>
            let w := if gp.2 = 0 then in0 gp.1 else in1 gp.1
            inZ w = 0 ∧ inS (G_c c) w = 0)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun g hg => ?_)
        have h01 : ({0, 1} : Finset (Fin 2)) = Finset.univ := by decide
        rw [h01, Fin.sum_univ_two]
        simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false]
        have s0 := hSlot_le1 g hg (in0 g)
        have s1 := hSlot_le1 g hg (in1 g)
        have hif : ∀ w, inZ w + inS (G_c c) w ≤ 1 →
            (1 - inZ w - inS (G_c c) w) = if inZ w = 0 ∧ inS (G_c c) w = 0 then 1 else 0 := by
          intro w hw
          have h0 : inZ w = 0 ∨ inZ w = 1 := by
            dsimp only [inZ]
            by_cases h : ∃ z ∈ Z, 28 + z.val = w
            · right; exact if_pos h
            · left; exact if_neg h
          have h1 : inS (G_c c) w = 0 ∨ inS (G_c c) w = 1 := by
            dsimp only [inS]
            by_cases h : ∃ g' ∈ G_c c, 28 + g'.val = w
            · right; exact if_pos h
            · left; exact if_neg h
          rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
          · rw [h0, h1]; simp
          · rw [h0, h1]; simp
          · rw [h0, h1]; simp
          · omega
        rw [hif (in0 g) s0, hif (in1 g) s1]
      rw [hfree_eq]
      let minG : ∀ q ∈ S_c, Fin D.gates.length := fun q hq =>
        ((G_c c).filter (fun g => q ∈ Sings (28 + g.val))).min' (by
          obtain ⟨g, hg, hqg⟩ := Finset.mem_biUnion.mp hq
          exact ⟨g, Finset.mem_filter.mpr ⟨hg, hqg⟩⟩)
      have hminG_spec : ∀ q (hq : q ∈ S_c),
          let g := minG q hq
          g ∈ G_c c ∧ q ∈ Sings (28 + g.val) ∧ ∀ g' ∈ G_c c, q ∈ Sings (28 + g'.val) → g ≤ g' := by
        intro q hq
        have hmem := Finset.min'_mem ((G_c c).filter (fun g => q ∈ Sings (28 + g.val))) (by
          obtain ⟨g, hg, hqg⟩ := Finset.mem_biUnion.mp hq
          exact ⟨g, Finset.mem_filter.mpr ⟨hg, hqg⟩⟩)
        have hm := Finset.mem_filter.mp hmem
        refine ⟨hm.1, hm.2, fun g' hg' hqg' => Finset.min'_le _ g' (Finset.mem_filter.mpr ⟨hg', hqg'⟩)⟩
      have hminG_side : ∀ q (hq : q ∈ S_c),
          ∃ pos : Fin 2,
            let g := minG q hq
            let w := if pos = 0 then in0 g else in1 g
            Sings w = {q} ∧ inZ w = 0 ∧ inS (G_c c) w = 0 := by
        intro q hq
        obtain ⟨hg_mem, hqg, hg_min⟩ := hminG_spec q hq
        have hgop := (hG_prop c (minG q hq) hg_mem).2.1
        have hsor := hSings_or_in (minG q hq) hgop
        rw [hsor, Finset.mem_union] at hqg
        have hw_prop : ∀ w, w = in0 (minG q hq) ∨ w = in1 (minG q hq) → q ∈ Sings w →
            Sings w = {q} ∧ inZ w = 0 ∧ inS (G_c c) w = 0 := by
          intro w hw hqw
          have hnoZ : inZ w = 0 := by
            dsimp only [inZ]
            rw [if_neg]; rintro ⟨z, hz, rfl⟩
            have hemp : Sings (28 + z.val) = ∅ := (Finset.mem_filter.mp hz).2
            rw [hemp] at hqw; exact Finset.notMem_empty _ hqw
          have hnoS : inS (G_c c) w = 0 := by
            dsimp only [inS]
            rw [if_neg]; rintro ⟨g', hg', heq⟩
            have hlt : g' < minG q hq := by
              have := (hDShape (minG q hq)).2 w (by rcases hw with rfl | rfl <;> exact List.getElem_mem _)
              omega
            have hle := hg_min g' hg' (heq.symm ▸ hqw)
            omega
          have hSings_eq : Sings w = {q} := by
            by_contra hne_sing
            have hcard2 : 2 ≤ (Sings w).card := by
              have hne : (Sings w).Nonempty := ⟨q, hqw⟩
              have h1 : 1 ≤ (Sings w).card := Finset.card_pos.mpr hne
              by_contra hlt2
              have hcard1 : (Sings w).card = 1 := by omega
              obtain ⟨q', hq'⟩ := Finset.card_eq_one.mp hcard1
              rw [hq'] at hqw; simp at hqw; subst hqw; exact hne_sing hq'
            -- w must be in G_c c!
            simp only [G_c, Finset.mem_biUnion, Finset.mem_filter] at hg_mem
            obtain ⟨k, ⟨hk_own, hk_c⟩, hg_I⟩ := hg_mem
            dsimp only [I_of] at hg_I
            split_ifs at hg_I with hk2; swap; exact absurd hg_I (Finset.notMem_empty _)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg_I
            have hg_or := hg_I.1
            have hsp := hstarSide_spec k hk_own hk2.2
            have hw_or : w ∈ orReach (starSide k) := by
              have hw_sub : w ∈ orReach (28 + (minG q hq).val) := by
                have h1 : orReach (28 + (minG q hq).val) = orReachFuel (28 + (minG q hq).val) (28 + (minG q hq).val) := rfl
                have hwpos : ∃ w', 28 + (minG q hq).val = w' + 1 := ⟨27 + (minG q hq).val, by omega⟩
                obtain ⟨w', hw'⟩ := hwpos
                have h2 : orReach (28 + (minG q hq).val) = orReachFuel (w' + 1) (28 + (minG q hq).val) := by
                  dsimp only [orReach]; rw [← hw']
                rw [h2]; dsimp only [orReachFuel]; rw [dif_pos (by omega)]
                have hkeq : (⟨28 + (minG q hq).val - 28, (by omega : 28 + (minG q hq).val - 28 < D.gates.length)⟩ : Fin D.gates.length) = minG q hq := Fin.ext (by simp)
                simp only [hkeq, hgop]
                have huw : in0 (minG q hq) < 28 + (minG q hq).val := (hDShape (minG q hq)).2 (in0 (minG q hq)) (List.getElem_mem _)
                have hvw : in1 (minG q hq) < 28 + (minG q hq).val := (hDShape (minG q hq)).2 (in1 (minG q hq)) (List.getElem_mem _)
                change w ∈ insert (28 + (minG q hq).val) (orReachFuel w' _ ∪ orReachFuel w' _)
                rw [horReach_fuel_eq w' (in0 (minG q hq)) (in0 (minG q hq)) (by omega) (le_refl _),
                    horReach_fuel_eq w' (in1 (minG q hq)) (in1 (minG q hq)) (by omega) (le_refl _)]
                rcases hw with rfl | rfl
                · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (horReach_mem_self _))
                · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (horReach_mem_self _))
              -- need horReach_trans:
              have htrans : ∀ a b, b ∈ orReach a → orReach b ⊆ orReach a := by
                intro a
                induction a using Nat.strong_induction_on with
                | ind a iha =>
                  intro b hb x hx
                  by_cases ha : 28 ≤ a ∧ a - 28 < D.gates.length
                  · obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
                    have h1 : orReach a = orReachFuel (a' + 1) a := by dsimp only [orReach]; rw [← ha']
                    rw [h1] at hb ⊢; dsimp only [orReachFuel] at hb ⊢; rw [dif_pos (by omega)] at hb ⊢
                    let ka : Fin D.gates.length := ⟨a - 28, ha.2⟩
                    cases hopa : (D.gates.get ka).op with
                    | or =>
                      have hlena := (hDShape ka).1
                      let ua := (D.gates.get ka).inputs[0]'(by omega)
                      let va := (D.gates.get ka).inputs[1]'(by omega)
                      have hua : ua < a := by have := (hDShape ka).2 ua (List.getElem_mem _); dsimp [ka] at this; omega
                      have hva : va < a := by have := (hDShape ka).2 va (List.getElem_mem _); dsimp [ka] at this; omega
                      simp only [ka, hopa] at hb ⊢
                      change _ ∈ insert a (orReachFuel a' _ ∪ orReachFuel a' _) at hb ⊢
                      rw [horReach_fuel_eq a' ua ua (by omega) (le_refl _), horReach_fuel_eq a' va va (by omega) (le_refl _)] at hb ⊢
                      simp only [Finset.mem_insert, Finset.mem_union] at hb ⊢
                      rcases hb with rfl | hb | hb
                      · rw [h1] at hx; dsimp only [orReachFuel] at hx; rw [dif_pos (by omega)] at hx
                        simp only [ka, hopa] at hx
                        change _ ∈ insert b (orReachFuel a' _ ∪ orReachFuel a' _) at hx
                        rw [horReach_fuel_eq a' ua ua (by omega) (le_refl _), horReach_fuel_eq a' va va (by omega) (le_refl _)] at hx
                        simp only [Finset.mem_insert, Finset.mem_union] at hx
                        exact hx
                      · right; left; exact iha ua hua b hb hx
                      · right; right; exact iha va hva b hb hx
                    | _ =>
                      simp only [ka, hopa, Finset.mem_singleton] at hb; subst hb
                      rw [h1] at hx; dsimp only [orReachFuel] at hx; rw [dif_pos (by omega)] at hx
                      simp only [ka, hopa] at hx; exact hx
                  · have hzero : orReach a = {a} := by
                      dsimp only [orReach]
                      cases a with | zero => simp [orReachFuel] | succ a' => dsimp only [orReachFuel]; rw [dif_neg (by omega)]
                    rw [hzero, Finset.mem_singleton] at hb; subst hb; exact hx
              exact htrans (starSide k) (28 + (minG q hq).val) hg_or hw_sub
            have hw28 : 28 ≤ w := by
              by_contra hlt28
              by_cases h27 : w = 27
              · rw [h27, hSings_27, Finset.card_empty] at hcard2; omega
              · by_cases h26 : w = 26
                · exact hsp.2.1 (h26 ▸ hw_or)
                · have hlt26 : w < 26 := by omega
                  rw [hSings_lt_card _ hlt26] at hcard2; omega
            have hw_lt : w - 28 < D.gates.length := by
              have := (hDShape (minG q hq)).2 w (by rcases hw with rfl | rfl <;> exact List.getElem_mem _)
              omega
            let g' : Fin D.gates.length := ⟨w - 28, hw_lt⟩
            have hg'_eq : 28 + g'.val = w := by dsimp [g']; omega
            have hg'_in : g' ∈ G_c c := by
              simp only [G_c, Finset.mem_biUnion, Finset.mem_filter]
              refine ⟨k, ⟨hk_own, hk_c⟩, ?_⟩
              dsimp only [I_of]; rw [dif_pos hk2]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hg'_eq.symm ▸ hw_or, hg'_eq.symm ▸ hcard2⟩
            have : inS (G_c c) w = 1 := by dsimp only [inS]; rw [if_pos ⟨g', hg'_in, hg'_eq⟩]
            omega
          exact ⟨hSings_eq, hnoZ, hnoS⟩
        rcases hqg with h0 | h1
        · exact ⟨0, hw_prop _ (Or.inl rfl) h0⟩
        · exact ⟨1, hw_prop _ (Or.inr rfl) h1⟩
      classical
      have hDlen_pos : 0 < D.gates.length := by
        obtain ⟨g0, _⟩ := Finset.card_pos.mp (by omega : 0 < Owned.card)
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) g0.isLt
      let f : Fin 26 → Fin D.gates.length × Fin 2 := fun q =>
        if hq : q ∈ S_c then (minG q hq, (hminG_side q hq).choose) else (⟨0, hDlen_pos⟩, 0)
      refine Finset.card_le_card_of_injOn f (fun q hq => ?_) (fun q1 hq1 q2 hq2 heq => ?_)
      · dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hq)]
        have hsp := (hminG_side q (Finset.mem_coe.mp hq)).choose_spec
        have hg := (hminG_spec q (Finset.mem_coe.mp hq)).1
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
        refine ⟨⟨hg, by omega⟩, hsp.2.1, hsp.2.2⟩
      · dsimp only [f] at heq; rw [dif_pos (Finset.mem_coe.mp hq1), dif_pos (Finset.mem_coe.mp hq2)] at heq
        have h1 := (hminG_side q1 (Finset.mem_coe.mp hq1)).choose_spec
        have h2 := (hminG_side q2 (Finset.mem_coe.mp hq2)).choose_spec
        have hgeq : minG q1 (Finset.mem_coe.mp hq1) = minG q2 (Finset.mem_coe.mp hq2) := (Prod.ext_iff.mp heq).1
        have hpeq : (hminG_side q1 (Finset.mem_coe.mp hq1)).choose = (hminG_side q2 (Finset.mem_coe.mp hq2)).choose := (Prod.ext_iff.mp heq).2
        have hsing1 : Sings (if (hminG_side q1 (Finset.mem_coe.mp hq1)).choose = 0 then in0 (minG q1 (Finset.mem_coe.mp hq1)) else in1 (minG q1 (Finset.mem_coe.mp hq1))) = {q1} := h1.1
        have hsing2 : Sings (if (hminG_side q2 (Finset.mem_coe.mp hq2)).choose = 0 then in0 (minG q2 (Finset.mem_coe.mp hq2)) else in1 (minG q2 (Finset.mem_coe.mp hq2))) = {q2} := h2.1
        rw [hpeq] at hsing1
        have hw_eq : (if (hminG_side q2 (Finset.mem_coe.mp hq2)).choose = 0 then in0 (minG q1 (Finset.mem_coe.mp hq1)) else in1 (minG q1 (Finset.mem_coe.mp hq1))) =
            (if (hminG_side q2 (Finset.mem_coe.mp hq2)).choose = 0 then in0 (minG q2 (Finset.mem_coe.mp hq2)) else in1 (minG q2 (Finset.mem_coe.mp hq2))) := by
          split_ifs
          · exact hin0_eq _ _ hgeq
          · exact hin1_eq _ _ hgeq
        rw [hw_eq, hsing2] at hsing1
        exact Finset.singleton_injective hsing1.symm
    have hEdges_in_Gc : (G_c c).card ≤ O_c2.card + ∑ g ∈ G_c c, (inS (G_c c) (in0 g) + inS (G_c c) (in1 g)) := by
      let Roots_c : Finset (Fin D.gates.length) := by
        classical
        exact (G_c c).filter (fun g => ∃ k ∈ O_c2, 28 + g.val = starSide k)
      have hRoots_le : Roots_c.card ≤ O_c2.card := by
        classical
        have hsub : Roots_c ⊆ O_c2.biUnion (fun k => (G_c c).filter (fun g => 28 + g.val = starSide k)) := by
          intro g hg
          obtain ⟨_, k, hk, heq⟩ := Finset.mem_filter.mp hg
          exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1, heq⟩⟩
        refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
        have h1 : ∀ k ∈ O_c2, ((G_c c).filter (fun g => 28 + g.val = starSide k)).card ≤ 1 := by
          intro k _
          rw [Finset.card_le_one]
          intro g1 hg1 g2 hg2
          exact Fin.ext (by have h1 := (Finset.mem_filter.mp hg1).2; have h2 := (Finset.mem_filter.mp hg2).2; omega)
        calc ∑ k ∈ O_c2, ((G_c c).filter (fun g => 28 + g.val = starSide k)).card
            ≤ ∑ _k ∈ O_c2, 1 := Finset.sum_le_sum h1
          _ = O_c2.card := by simp
      have hNonRoots_le : ((G_c c) \ Roots_c).card ≤ ∑ g ∈ G_c c, (inS (G_c c) (in0 g) + inS (G_c c) (in1 g)) := by
        have hsum_eq : ∑ g ∈ G_c c, (inS (G_c c) (in0 g) + inS (G_c c) (in1 g)) =
            ((G_c c ×ˢ ({0, 1} : Finset (Fin 2))).filter (fun gp =>
              let w := if gp.2 = 0 then in0 gp.1 else in1 gp.1
              inS (G_c c) w = 1)).card := by
          rw [Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          have h01 : ({0, 1} : Finset (Fin 2)) = Finset.univ := by decide
          rw [h01, Fin.sum_univ_two]
          simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false]
          have hS01 : ∀ w, inS (G_c c) w = if inS (G_c c) w = 1 then 1 else 0 := fun w => by
            dsimp only [inS]; by_cases h : ∃ g' ∈ G_c c, 28 + g'.val = w <;> simp [h]
          rw [← hS01 (in0 g), ← hS01 (in1 g)]
        rw [hsum_eq]
        have hpar : ∀ g ∈ G_c c \ Roots_c, ∃ gp ∈ (G_c c ×ˢ ({0, 1} : Finset (Fin 2))).filter (fun gp =>
            inS (G_c c) (if gp.2 = 0 then in0 gp.1 else in1 gp.1) = 1),
            (if gp.2 = 0 then in0 gp.1 else in1 gp.1) = 28 + g.val := by
          intro g hg
          have hg_mem := (Finset.mem_sdiff.mp hg).1
          have hg_nroot := (Finset.mem_sdiff.mp hg).2
          simp only [G_c, Finset.mem_biUnion, Finset.mem_filter] at hg_mem
          obtain ⟨k, ⟨hk_own, hk_c⟩, hg_I⟩ := hg_mem
          dsimp only [I_of] at hg_I
          split_ifs at hg_I with hk2; swap; exact absurd hg_I (Finset.notMem_empty _)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg_I
          obtain ⟨hg_or, hg_card⟩ := hg_I
          have hk_Oc2 : k ∈ O_c2 := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hk_own, hk_c⟩, hk2.2⟩
          have hne_star : 28 + g.val ≠ starSide k := fun h => hg_nroot (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hg).1, k, hk_Oc2, h⟩)
          obtain ⟨g', hg'_or, hg'_op, hg'_inp⟩ := horReach_parent (starSide k) (28 + g.val) hg_or hne_star
          have hg'_card : 2 ≤ (Sings (28 + g'.val)).card := by
            have hsub : Sings (28 + g.val) ⊆ Sings (28 + g'.val) := by
              rw [hSings_or_in g' hg'_op]
              rcases hg'_inp with h0 | h1
              · rw [← h0]; exact Finset.subset_union_left
              · rw [← h1]; exact Finset.subset_union_right
            exact le_trans hg_card (Finset.card_le_card hsub)
          have hg'_mem : g' ∈ G_c c := by
            simp only [G_c, Finset.mem_biUnion, Finset.mem_filter]
            refine ⟨k, ⟨hk_own, hk_c⟩, ?_⟩
            dsimp only [I_of]; rw [dif_pos hk2]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hg'_or, hg'_card⟩
          rcases hg'_inp with h0 | h1
          · refine ⟨(g', 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg'_mem, by simp⟩, ?_⟩, by simp [h0]⟩
            dsimp only [inS]; simp only [Fin.isValue, ite_true]; rw [if_pos ⟨g, (Finset.mem_sdiff.mp hg).1, h0⟩]
          · refine ⟨(g', 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg'_mem, by simp⟩, ?_⟩, by simp [h1]⟩
            dsimp only [inS]; simp only [Fin.isValue, Fin.reduceEq, ite_false]; rw [if_pos ⟨g, (Finset.mem_sdiff.mp hg).1, h1⟩]
        classical
        have hDlen_pos : 0 < D.gates.length := by
          obtain ⟨g0, _⟩ := Finset.card_pos.mp (by omega : 0 < Owned.card)
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) g0.isLt
        let f : Fin D.gates.length → Fin D.gates.length × Fin 2 := fun g =>
          if hg : g ∈ G_c c \ Roots_c then (hpar g hg).choose else (⟨0, hDlen_pos⟩, 0)
        refine Finset.card_le_card_of_injOn f (fun g hg => ?_) (fun g1 hg1 g2 hg2 heq => ?_)
        · dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hg)]; exact (hpar g (Finset.mem_coe.mp hg)).choose_spec.1
        · dsimp only [f] at heq; rw [dif_pos (Finset.mem_coe.mp hg1), dif_pos (Finset.mem_coe.mp hg2)] at heq
          have h1 := (hpar g1 (Finset.mem_coe.mp hg1)).choose_spec.2
          have h2 := (hpar g2 (Finset.mem_coe.mp hg2)).choose_spec.2
          rw [heq] at h1
          exact Fin.ext (by omega)
      have hsplit : (G_c c).card = Roots_c.card + ((G_c c) \ Roots_c).card := by
        have hsub : Roots_c ⊆ G_c c := Finset.filter_subset _ _
        have h := Finset.card_sdiff_add_card_inter (G_c c) Roots_c
        rw [Finset.inter_eq_right.mpr hsub] at h; omega
      omega
    have hcomb : (G_c c).card + O_c.card ≥ (∑ k ∈ O_c, (E_of k).card) + Z_in (G_c c) := by
      have h_two : 2 * (G_c c).card =
          ∑ g ∈ G_c c, ((1 - inZ (in0 g) - inS (G_c c) (in0 g)) + (1 - inZ (in1 g) - inS (G_c c) (in1 g))) +
          Z_in (G_c c) + ∑ g ∈ G_c c, (inS (G_c c) (in0 g) + inS (G_c c) (in1 g)) := by
        dsimp only [Z_in]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        have h2 : ∑ g ∈ G_c c, 2 = 2 * (G_c c).card := by simp only [Finset.sum_const, smul_eq_mul, mul_comm]
        rw [← h2]
        refine Finset.sum_congr rfl (fun g hg => ?_)
        have s0 := hSlot_le1 g hg (in0 g)
        have s1 := hSlot_le1 g hg (in1 g)
        omega
      omega
    exact hcomb
  -- Final global counting
  let U_I : Finset (Fin D.gates.length) := Finset.univ.biUnion G_c
  have hU_I_card : 52 + Z_in U_I ≤ U_I.card + Owned.card := by
    have hU_card : U_I.card = ∑ c : Fin 13 ⊕ Fin 13, (G_c c).card :=
      Finset.card_biUnion (fun c1 _ c2 _ hne => hG_disjoint c1 c2 hne)
    have hU_Z : Z_in U_I = ∑ c : Fin 13 ⊕ Fin 13, Z_in (G_c c) :=
      Finset.sum_biUnion (fun c1 _ c2 _ hne => hG_disjoint c1 c2 hne)
    have hO_part : Owned = Finset.univ.biUnion (fun c => Owned.filter (fun k => center k = c)) := by
      ext k; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      exact ⟨fun hk => ⟨center k, hk, rfl⟩, fun ⟨_, hk, _⟩ => hk⟩
    have hO_disj : ∀ c1 ∈ (Finset.univ : Finset (Fin 13 ⊕ Fin 13)), ∀ c2 ∈ (Finset.univ : Finset (Fin 13 ⊕ Fin 13)),
        c1 ≠ c2 → Disjoint (Owned.filter (fun k => center k = c1)) (Owned.filter (fun k => center k = c2)) := by
      intro c1 _ c2 _ hne; rw [Finset.disjoint_left]; intro k h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hO_card : Owned.card = ∑ c : Fin 13 ⊕ Fin 13, (Owned.filter (fun k => center k = c)).card := by
      conv_lhs => rw [hO_part]
      exact Finset.card_biUnion hO_disj
    have hE_sum : ∑ c : Fin 13 ⊕ Fin 13, ∑ k ∈ Owned.filter (fun k => center k = c), (E_of k).card = 52 := by
      rw [← Finset.sum_biUnion hO_disj, ← hO_part]
      exact hSum_E_of
    have hsum_le := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hG_card c)
    simp only [Finset.sum_add_distrib] at hsum_le
    rw [hE_sum, ← hU_Z, ← hU_card, ← hO_card] at hsum_le
    exact hsum_le
  let G0' : Finset (Fin D.gates.length) := Z \ Owned
  let J : Finset (Fin D.gates.length) := (R_gates \ Z) \ U_I
  have hU_I_sub_R : U_I ⊆ R_gates := by
    intro g hg
    obtain ⟨c, _, hgc⟩ := Finset.mem_biUnion.mp hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hG_prop c g hgc).1⟩
  have hU_I_disj_Z : Disjoint U_I Z := by
    rw [Finset.disjoint_left]; intro g hgU hgZ
    obtain ⟨c, _, hgc⟩ := Finset.mem_biUnion.mp hgU
    have hcard := (hG_prop c g hgc).2.2
    have hemp : Sings (28 + g.val) = ∅ := (Finset.mem_filter.mp hgZ).2
    rw [hemp] at hcard; simp at hcard
  have hZ_count : Z.card ≤ 2 + 2 * G0'.card + J.card + Z_in U_I := by
    let Z_roots : Finset (Fin D.gates.length) := Z.filter (fun z => 28 + z.val = a' ∨ 28 + z.val = b')
    have hZr_le : Z_roots.card ≤ 2 := by
      let S : Finset ℕ := {a', b'}
      have hinj : ∀ z1 ∈ Z_roots, ∀ z2 ∈ Z_roots, 28 + z1.val = 28 + z2.val → z1 = z2 := fun _ _ _ _ h => Fin.ext (by omega)
      have hle := Finset.card_le_card_of_injOn (t := S) (fun z : Fin D.gates.length => 28 + z.val) (fun z hz => by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2; simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]; exact this) hinj
      exact le_trans hle (le_trans (Finset.card_insert_le _ _) (by simp))
    let OutSet : Finset (Fin D.gates.length) := G0' ∪ J ∪ U_I
    have hOut_disj1 : Disjoint G0' J := by
      rw [Finset.disjoint_left]; intro g h1 h2
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2 (Finset.mem_sdiff.mp h1).1
    have hOut_disj2 : Disjoint (G0' ∪ J) U_I := by
      rw [Finset.disjoint_left]; intro g h1 h2
      rcases Finset.mem_union.mp h1 with hG | hJ
      · exact (Finset.disjoint_left.mp hU_I_disj_Z) h2 (Finset.mem_sdiff.mp hG).1
      · exact (Finset.mem_sdiff.mp hJ).2 h2
    have hZ_nroot : ∀ z ∈ Z \ Z_roots, ∃ gp ∈ (OutSet ×ˢ ({0, 1} : Finset (Fin 2))).filter (fun gp =>
        inZ (if gp.2 = 0 then in0 gp.1 else in1 gp.1) = 1),
        (if gp.2 = 0 then in0 gp.1 else in1 gp.1) = 28 + z.val := by
      intro z hz
      have hzZ := (Finset.mem_sdiff.mp hz).1
      have hzne := (Finset.mem_sdiff.mp hz).2
      have hne_ab : 28 + z.val ≠ a' ∧ 28 + z.val ≠ b' :=
        ⟨fun h => hzne (Finset.mem_filter.mpr ⟨hzZ, Or.inl h⟩), fun h => hzne (Finset.mem_filter.mpr ⟨hzZ, Or.inr h⟩)⟩
      have hz_reach : 28 + z.val ∈ ReachSet := (Finset.mem_filter.mp (Finset.mem_filter.mp hzZ).1).2
      have hex_g : ∃ g : Fin D.gates.length, 28 + g.val ∈ ReachSet ∧ (28 + z.val = in0 g ∨ 28 + z.val = in1 g) := by
        rcases Finset.mem_union.mp hz_reach with ha | hb
        · obtain ⟨g, hg, hin⟩ := hreach_parent a' (28 + z.val) ha hne_ab.1
          exact ⟨g, Finset.mem_union_left _ hg, hin⟩
        · obtain ⟨g, hg, hin⟩ := hreach_parent b' (28 + z.val) hb hne_ab.2
          exact ⟨g, Finset.mem_union_right _ hg, hin⟩
      obtain ⟨g, hg_reach, hg_in⟩ := hex_g
      have hg_not_owned : g ∉ Owned := fun hown =>
        hZ_not_input_Owned z hzZ g hown (by rcases hg_in with h | h <;> rw [h] <;> exact List.getElem_mem _)
      have hg_out : g ∈ OutSet := by
        have hg_R : g ∈ R_gates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_reach⟩
        by_cases hgZ : g ∈ Z
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hgZ, hg_not_owned⟩))
        · by_cases hgU : g ∈ U_I
          · exact Finset.mem_union_right _ hgU
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hg_R, hgZ⟩, hgU⟩))
      rcases hg_in with h0 | h1
      · refine ⟨(g, 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg_out, by simp⟩, ?_⟩, by simp [h0]⟩
        dsimp only [inZ]; simp only [Fin.isValue, ite_true]; rw [if_pos ⟨z, hzZ, h0⟩]
      · refine ⟨(g, 1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg_out, by simp⟩, ?_⟩, by simp [h1]⟩
        dsimp only [inZ]; simp only [Fin.isValue, Fin.reduceEq, ite_false]; rw [if_pos ⟨z, hzZ, h1⟩]
    have hZ_sdiff_le : (Z \ Z_roots).card ≤ Z_in OutSet := by
      have hsum_eq : Z_in OutSet = ((OutSet ×ˢ ({0, 1} : Finset (Fin 2))).filter (fun gp =>
          inZ (if gp.2 = 0 then in0 gp.1 else in1 gp.1) = 1)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        dsimp only [Z_in]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        have h01 : ({0, 1} : Finset (Fin 2)) = Finset.univ := by decide
        rw [h01, Fin.sum_univ_two]
        simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false]
        have hZ01 : ∀ w, inZ w = if inZ w = 1 then 1 else 0 := fun w => by
          dsimp only [inZ]; by_cases h : ∃ z ∈ Z, 28 + z.val = w <;> simp [h]
        rw [← hZ01 (in0 g), ← hZ01 (in1 g)]
      rw [hsum_eq]
      classical
      have hDlen_pos : 0 < D.gates.length := by
        obtain ⟨g0, _⟩ := Finset.card_pos.mp (by omega : 0 < Owned.card)
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) g0.isLt
      let f : Fin D.gates.length → Fin D.gates.length × Fin 2 := fun z =>
        if hz : z ∈ Z \ Z_roots then (hZ_nroot z hz).choose else (⟨0, hDlen_pos⟩, 0)
      refine Finset.card_le_card_of_injOn f (fun z hz => ?_) (fun z1 hz1 z2 hz2 heq => ?_)
      · dsimp only [f]; rw [dif_pos (Finset.mem_coe.mp hz)]; exact (hZ_nroot z (Finset.mem_coe.mp hz)).choose_spec.1
      · dsimp only [f] at heq; rw [dif_pos (Finset.mem_coe.mp hz1), dif_pos (Finset.mem_coe.mp hz2)] at heq
        have h1 := (hZ_nroot z1 (Finset.mem_coe.mp hz1)).choose_spec.2
        have h2 := (hZ_nroot z2 (Finset.mem_coe.mp hz2)).choose_spec.2
        rw [heq] at h1
        exact Fin.ext (by omega)
    have hZ_in_G0 : Z_in G0' ≤ 2 * G0'.card := by
      have hle : ∑ g ∈ G0', (inZ (in0 g) + inZ (in1 g)) ≤ ∑ _g ∈ G0', 2 :=
        Finset.sum_le_sum (fun g _ => by dsimp only [inZ]; split_ifs <;> omega)
      rw [Finset.sum_const, smul_eq_mul, mul_comm] at hle
      exact hle
    have hZ_in_J : Z_in J ≤ J.card := by
      have hle : ∑ g ∈ J, (inZ (in0 g) + inZ (in1 g)) ≤ ∑ _g ∈ J, 1 := by
        refine Finset.sum_le_sum (fun g hg => ?_)
        have hgR : g ∈ R_gates := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hg).1).1
        have hgnZ : g ∉ Z := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hg).1).2
        have hne_emp : (Sings (28 + g.val)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          exact hgnZ (Finset.mem_filter.mpr ⟨hgR, hemp⟩)
        have hgop : (D.gates.get g).op = .or := by
          rcases (hDMono (D.gates.get g) (List.get_mem _ _)).1 with hop | hop
          · exfalso; obtain ⟨q, hq⟩ := hne_emp; rw [hSings_and g hop] at hq; exact Finset.notMem_empty _ hq
          · exact hop
        rw [hSings_or_in g hgop] at hne_emp
        obtain ⟨q, hq⟩ := hne_emp
        rcases Finset.mem_union.mp hq with h0 | h1
        · have hz0 : inZ (in0 g) = 0 := by
            dsimp only [inZ]; rw [if_neg]; rintro ⟨z, hz, heq⟩
            rw [← heq, (Finset.mem_filter.mp hz).2] at h0; exact Finset.notMem_empty _ h0
          dsimp only [inZ] at hz0 ⊢; rw [hz0]; split_ifs <;> omega
        · have hz1 : inZ (in1 g) = 0 := by
            dsimp only [inZ]; rw [if_neg]; rintro ⟨z, hz, heq⟩
            rw [← heq, (Finset.mem_filter.mp hz).2] at h1; exact Finset.notMem_empty _ h1
          dsimp only [inZ] at hz1 ⊢; rw [hz1]; split_ifs <;> omega
      rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
      exact hle
    have hOut_sum : Z_in OutSet = Z_in G0' + Z_in J + Z_in U_I := by
      dsimp only [OutSet, Z_in]
      rw [Finset.sum_union hOut_disj2, Finset.sum_union hOut_disj1]
    have hZ_split : Z.card = Z_roots.card + (Z \ Z_roots).card := by
      have hsub : Z_roots ⊆ Z := Finset.filter_subset _ _
      have h := Finset.card_sdiff_add_card_inter Z Z_roots
      rw [Finset.inter_eq_right.mpr hsub] at h; omega
    omega
  have hZ_eq : Z.card = Owned.card + G0'.card := by
    have hpart : Z = Owned ∪ G0' := by
      ext g; simp only [G0', Finset.mem_union, Finset.mem_sdiff]
      exact ⟨fun hg => by by_cases h : g ∈ Owned <;> [exact Or.inl h; exact Or.inr ⟨hg, h⟩],
             fun h => by rcases h with h | ⟨h, _⟩ <;> [exact hOwned_sub_Z h; exact h]⟩
    have hdisj : Disjoint Owned G0' := by
      rw [Finset.disjoint_left]; intro g h1 h2; exact (Finset.mem_sdiff.mp h2).2 h1
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hTotal_gates : Owned.card + U_I.card + G0'.card + J.card ≤ D.gates.length := by
    have hdisj1 : Disjoint Owned U_I := Disjoint.mono_left hOwned_sub_Z hU_I_disj_Z.symm
    have hdisj2 : Disjoint (Owned ∪ U_I) G0' := by
      rw [Finset.disjoint_left]; intro g h1 h2
      rcases Finset.mem_union.mp h1 with hO | hU
      · exact (Finset.mem_sdiff.mp h2).2 hO
      · exact (Finset.disjoint_left.mp hU_I_disj_Z) hU (Finset.mem_sdiff.mp h2).1
    have hdisj3 : Disjoint (Owned ∪ U_I ∪ G0') J := by
      rw [Finset.disjoint_left]; intro g h1 h2
      rcases Finset.mem_union.mp h1 with hOU | hG
      · rcases Finset.mem_union.mp hOU with hO | hU
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2 (hOwned_sub_Z hO)
        · exact (Finset.mem_sdiff.mp h2).2 hU
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2 (Finset.mem_sdiff.mp hG).1
    have hle := Finset.card_le_univ (Owned ∪ U_I ∪ G0' ∪ J)
    rw [Finset.card_union_of_disjoint hdisj3, Finset.card_union_of_disjoint hdisj2,
        Finset.card_union_of_disjoint hdisj1, Fintype.card_fin] at hle
    exact hle
  have hDlen : D.gates.length ≤ 60 := by simpa [CircuitLowerBounds.Circuit.size] using hDSize
  omega
