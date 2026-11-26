import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8145_1
    (h_and : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4;
      have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5);
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 → x6.size ≤ x8.size) →
      (26 : ℕ) ≤ x6.output → x6.output < (26 : ℕ) + x6.size → (2 : ℕ) ≤ x6.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (∃ (x8 : Fin x6.gates.length), (x6.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (26 : ℕ) + ↑x8 ≠ x6.output ∧ (x6.wires (List.ofFn (x4 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true) →
      (64 : ℕ) ≤ x6.size)
    (h_or : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4;
      have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5);
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 → x6.size ≤ x8.size) →
      (26 : ℕ) ≤ x6.output → x6.output < (26 : ℕ) + x6.size → (2 : ℕ) ≤ x6.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∃ (x8 : Fin x6.gates.length), (x6.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (26 : ℕ) + ↑x8 ≠ x6.output ∧ (x6.wires (List.ofFn (x4 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true) →
      (64 : ℕ) ≤ x6.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) => ∃ (x8 : Fin x5.gates.length), (x5.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5.wires (List.ofFn (x4 x6 x7))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 → x6.size ≤ x8.size) → x5 x6 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ)) → (64 : ℕ) ≤ x6.size := by
  dsimp only
  intro x6 hx3 hmin ⟨x8, hx8_op, hx8_val⟩
  have h_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
    intro gs; induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega
  have h_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs; induction gs with
    | nil => intro w; exact List.prefix_refl w
    | cons g gs ih => intro w; exact (List.prefix_append w [_]).trans (ih _)
  have hlt : x6.output < 26 + x6.size := by
    by_contra hge
    have hge' : 26 + x6.size ≤ x6.output := Nat.le_of_not_lt hge
    have h0 : x6.eval (List.ofFn (fun _ : Fin 26 => true)) = false := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
      have hlen : (x6.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (fun _ : Fin 26 => true))).length = 26 + x6.size := by
        rw [h_len, List.length_ofFn]; rfl
      exact List.getD_eq_default _ _ (hlen ▸ hge')
    have h1 : x6.eval (List.ofFn (fun _ : Fin 26 => true)) = true :=
      (hx3.2.2 (fun _ => true)).mpr ⟨0, 0, by simp, rfl, rfl⟩
    rw [h0] at h1
    exact Bool.noConfusion h1
  have hge : 26 ≤ x6.output := by
    by_contra hlt26
    have hlt26' : x6.output < 26 := Nat.lt_of_not_le hlt26
    let f : Fin 26 → Bool := fun i => decide (i.val = x6.output)
    have hf_eval : x6.eval (List.ofFn f) = true := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
      have hpref := h_pref x6.gates (List.ofFn f)
      have hlen : (List.ofFn f).length = 26 := by simp
      have hget : (x6.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn f)).getD x6.output false = (List.ofFn f).getD x6.output false := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        have hlt_len : x6.output < (List.ofFn f).length := hlen.symm ▸ hlt26'
        obtain ⟨rest, hrest⟩ := hpref
        rw [← hrest, List.getElem?_append_left hlt_len]
      rw [hget, List.getD_eq_getElem _ _ (hlen.symm ▸ hlt26'), List.getElem_ofFn]
      simp [f]
    obtain ⟨a, b, _, ha, hb⟩ := (hx3.2.2 f).mp hf_eval
    simp only [f, decide_eq_true_eq] at ha hb
    have hne : (Fin.castAdd 13 a : Fin 26).val ≠ (Fin.natAdd 13 b : Fin 26).val := by
      simp [Fin.castAdd, Fin.natAdd]; omega
    exact hne (ha.trans hb.symm)
  have hne : 26 + x8.val ≠ x6.output := by
    intro heq
    have heval_f : x6.eval (List.ofFn (fun x6_1 : Fin 26 => decide (x6_1 = 0 ∨ x6_1 = 1))) = true := by
      simpa only [PEqualNP.CircuitLowerBounds.Circuit.eval, heq] using hx8_val
    obtain ⟨a, b, _, _, hb⟩ := (hx3.2.2 _).mp heval_f
    simp only [decide_eq_true_eq] at hb
    have hbn : (Fin.natAdd 13 b : Fin 26).val ≥ 13 := by simp [Fin.natAdd]
    rcases hb with hb | hb <;> { have := congrArg Fin.val hb; omega }
  have h2 : 2 ≤ x6.size := by
    have h1 := x8.isLt
    change x8.val < x6.size at h1
    omega
  have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - 26) ∈ x6.gates := by
    have hi : x6.output - 26 < x6.gates.length := by change x6.output - 26 < x6.size; omega
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x6 (x6.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    simpa using (hx3.1 _ hmem).1
  rcases hop with hand | hor
  · exact h_and x6 hx3 hmin hge hlt h2 hand ⟨x8, hx8_op, hne, hx8_val⟩
  · exact h_or x6 hx3 hmin hge hlt h2 hor ⟨x8, hx8_op, hne, hx8_val⟩
