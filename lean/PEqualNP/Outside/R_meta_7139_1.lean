import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7139_1
    (h_and_and : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 → (37 : ℕ) ≤ x3.size → x3.size ≤ (62 : ℕ) →
        ∀ (x7 x8 : Fin ((26 : ℕ) + x3.size)), x7 ≠ x8 → (26 : ℕ) ≤ ↑x7 → (26 : ℕ) ≤ ↑x8 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (↑x7 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (↑x8 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x10 x11 : Finset (Fin (13 : ℕ))),
          ((∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x10, x2 x13 x12) ∨ ∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x2 x12 x13) →
          have x13 : Fin (26 : ℕ) → Bool := fun (x13 : Fin (26 : ℕ)) => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd (13 : ℕ) x14);
          have x14 : List Bool := x3.wires (List.ofFn x13);
          (x14.getD (↑x7) Bool.false || x14.getD (↑x8) Bool.false) = Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, x2 x15 x16)) →
        False)
    (h_or_or : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 → (37 : ℕ) ≤ x3.size → x3.size ≤ (62 : ℕ) →
        ∀ (x7 x8 : Fin ((26 : ℕ) + x3.size)), x7 ≠ x8 → (26 : ℕ) ≤ ↑x7 → (26 : ℕ) ≤ ↑x8 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (↑x7 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (↑x8 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ (x10 x11 : Finset (Fin (13 : ℕ))),
          ((∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x10, x2 x13 x12) ∨ ∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x2 x12 x13) →
          have x13 : Fin (26 : ℕ) → Bool := fun (x13 : Fin (26 : ℕ)) => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd (13 : ℕ) x14);
          have x14 : List Bool := x3.wires (List.ofFn x13);
          (x14.getD (↑x7) Bool.false || x14.getD (↑x8) Bool.false) = Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, x2 x15 x16)) →
        False)
    (h_mixed : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x3 → (37 : ℕ) ≤ x3.size → x3.size ≤ (62 : ℕ) →
        ∀ (x7 x8 : Fin ((26 : ℕ) + x3.size)), x7 ≠ x8 → (26 : ℕ) ≤ ↑x7 → (26 : ℕ) ≤ ↑x8 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (↑x7 - (26 : ℕ))).op ≠ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (↑x8 - (26 : ℕ))).op →
        (∀ (x10 x11 : Finset (Fin (13 : ℕ))),
          ((∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x10, x2 x13 x12) ∨ ∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x2 x12 x13) →
          have x13 : Fin (26 : ℕ) → Bool := fun (x13 : Fin (26 : ℕ)) => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd (13 : ℕ) x14);
          have x14 : List Bool := x3.wires (List.ofFn x13);
          (x14.getD (↑x7) Bool.false || x14.getD (↑x8) Bool.false) = Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, x2 x15 x16)) →
        False)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     (37 : ℕ) ≤ x3.size →       x3.size ≤ (62 : ℕ) →         ∀ (x7 x8 : Fin ((26 : ℕ) + x3.size)),           x7 ≠ x8 →             (∀ (x10 x11 : Finset (Fin (13 : ℕ))),                 ((∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x10, x2 x13 x12) ∨ ∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x2 x12 x13) →                   have x13 : Fin (26 : ℕ) → Bool := fun (x13 : Fin (26 : ℕ)) => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd (13 : ℕ) x14);                   have x14 : List Bool := x3.wires (List.ofFn x13);                   (x14.getD (↑x7) Bool.false || x14.getD (↑x8) Bool.false) = Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, x2 x15 x16)) →               False := by
  dsimp only
  intro x3 hm h37 h62 x7 x8 hne hq
  have h_pref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs; induction gs with
    | nil => intro w; exact List.prefix_refl w
    | cons g gs ih => intro w; exact (List.prefix_append w [_]).trans (ih _)
  have get_input : ∀ (f : Fin 26 → Bool) (w : ℕ) (hw : w < 26),
      (x3.wires (List.ofFn f)).getD w false = f ⟨w, hw⟩ := by
    intro f w hw
    obtain ⟨rest, hrest⟩ := h_pref x3.gates (List.ofFn f)
    have hlen : (List.ofFn f).length = 26 := by simp
    rw [PEqualNP.CircuitLowerBounds.Circuit.wires, ← hrest, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (hlen.symm ▸ hw), ← List.getD_eq_getElem?_getD,
      List.getD_eq_getElem _ _ (hlen.symm ▸ hw), List.getElem_ofFn]
  have wire_ge_26 : ∀ (w : Fin (26 + x3.size)),
      (∀ (x10 x11 : Finset (Fin 13)),
        ((∃ x12 : Fin 13, ∀ x13 ∈ x10, ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x13 = x12 + x4) ∨
         ∃ x12 : Fin 13, ∀ x13 ∈ x11, ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x12 = x13 + x4) →
        have x13 : Fin 26 → Bool := fun x13 => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd 13 x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd 13 x14);
        (x3.wires (List.ofFn x13)).getD w.val false = true →
        Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x15 = x16 + x4) = true) →
      26 ≤ w.val := by
    intro w hw_imp
    by_contra hlt26
    have hw : w.val < 26 := Nat.lt_of_not_le hlt26
    by_cases hw13 : w.val < 13
    · let p : Fin 13 := ⟨w.val, hw13⟩
      let l : Fin 13 := p + 1
      have hsup : (∃ x12 : Fin 13, ∀ x13 ∈ ({p} : Finset (Fin 13)), ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x13 = x12 + x4) ∨
          ∃ x12 : Fin 13, ∀ x13 ∈ ({l} : Finset (Fin 13)), ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x12 = x13 + x4 :=
        Or.inl ⟨p, fun q hq' => ⟨0, by simp, by simp [Finset.mem_singleton.mp hq']⟩⟩
      let f : Fin 26 → Bool := fun x13 => Decidable.decide ((∃ x14 ∈ ({p} : Finset (Fin 13)), x13 = Fin.castAdd 13 x14) ∨ ∃ x14 ∈ ({l} : Finset (Fin 13)), x13 = Fin.natAdd 13 x14)
      have hf : f ⟨w.val, hw⟩ = true := by
        simp only [f, Finset.mem_singleton, exists_eq_left, decide_eq_true_eq]
        exact Or.inl (Fin.ext (by simp [p]))
      have hget : (x3.wires (List.ofFn f)).getD w.val false = true := (get_input f w.val hw).trans hf
      have htrue := hw_imp {p} {l} hsup hget
      rw [decide_eq_true_eq] at htrue
      rcases htrue with ⟨x15, hx15, x16, hx16, d, hd, heq⟩
      rw [Finset.mem_singleton.mp hx15, Finset.mem_singleton.mp hx16] at heq
      have hd_eq : (12 : Fin 13) = d := by
        have h1 : p - l = d := by rw [heq]; exact add_sub_cancel_left l d
        have h2 : p - (p + 1) = d := h1
        rw [show (12 : Fin 13) = -1 from rfl]
        simpa using h2
      have hmem : (12 : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := hd_eq ▸ hd
      revert hmem; decide
    · let l : Fin 13 := ⟨w.val - 13, by omega⟩
      let p : Fin 13 := l + 2
      have hsup : (∃ x12 : Fin 13, ∀ x13 ∈ ({p} : Finset (Fin 13)), ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x13 = x12 + x4) ∨
          ∃ x12 : Fin 13, ∀ x13 ∈ ({l} : Finset (Fin 13)), ∃ x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x12 = x13 + x4 :=
        Or.inr ⟨l, fun q hq' => ⟨0, by simp, by simp [Finset.mem_singleton.mp hq']⟩⟩
      let f : Fin 26 → Bool := fun x13 => Decidable.decide ((∃ x14 ∈ ({p} : Finset (Fin 13)), x13 = Fin.castAdd 13 x14) ∨ ∃ x14 ∈ ({l} : Finset (Fin 13)), x13 = Fin.natAdd 13 x14)
      have hf : f ⟨w.val, hw⟩ = true := by
        simp only [f, Finset.mem_singleton, exists_eq_left, decide_eq_true_eq]
        exact Or.inr (Fin.ext (by simp [l]; omega))
      have hget : (x3.wires (List.ofFn f)).getD w.val false = true := (get_input f w.val hw).trans hf
      have htrue := hw_imp {p} {l} hsup hget
      rw [decide_eq_true_eq] at htrue
      rcases htrue with ⟨x15, hx15, x16, hx16, d, hd, heq⟩
      rw [Finset.mem_singleton.mp hx15, Finset.mem_singleton.mp hx16] at heq
      have hd_eq : (2 : Fin 13) = d := by
        have h1 : p - l = d := by rw [heq]; exact add_sub_cancel_left l d
        have h2 : l + 2 - l = d := h1
        simpa using h2
      have hmem : (2 : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := hd_eq ▸ hd
      revert hmem; decide
  have h26_7 : 26 ≤ x7.val := wire_ge_26 x7 (fun x10 x11 hsup hget => by
    have := hq x10 x11 hsup
    rw [hget, Bool.true_or] at this
    exact this.symm)
  have h26_8 : 26 ≤ x8.val := wire_ge_26 x8 (fun x10 x11 hsup hget => by
    have := hq x10 x11 hsup
    rw [hget, Bool.or_true] at this
    exact this.symm)
  have gate_ao : ∀ i : ℕ, i < x3.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x3 i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x3 i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro i hi
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt x3 i ∈ x3.gates := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    simpa using (hm _ hmem).1
  have hop7 := gate_ao (x7.val - 26) (by omega)
  have hop8 := gate_ao (x8.val - 26) (by omega)
  rcases hop7 with h7and | h7or <;> rcases hop8 with h8and | h8or
  · exact h_and_and x3 hm h37 h62 x7 x8 hne h26_7 h26_8 h7and h8and hq
  · exact h_mixed x3 hm h37 h62 x7 x8 hne h26_7 h26_8 (by rw [h7and, h8or]; intro h; cases h) hq
  · exact h_mixed x3 hm h37 h62 x7 x8 hne h26_7 h26_8 (by rw [h7or, h8and]; intro h; cases h) hq
  · exact h_or_or x3 hm h37 h62 x7 x8 hne h26_7 h26_8 h7or h8or hq
