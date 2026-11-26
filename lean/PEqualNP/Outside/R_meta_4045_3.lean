import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_4045_3
    (hAnd : ∀ (x1 : Circuit) (x2 : (Fin 26 → Bool) → ℕ → Bool),
      (∀ (x3 : ℕ) (x4 : Gate), x1.gates[x3]? = some x4 → (x4.op = GateOp.and ∨ x4.op = GateOp.or) ∧ ∃ x6 x7, x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < 26 + x3 ∧ x7 < 26 + x3) →
      x1.size ≤ 62 → 26 ≤ x1.output → x1.output < 26 + x1.size →
      (∃ g : Gate, x1.gates[x1.output - 26]? = some g ∧ g.op = GateOp.and) →
      (∀ (x5 : Fin 26 → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 false) →
      (∀ (x6 : Fin 26 → Bool), x2 x6 x1.output = true ↔ ∃ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) ∧ x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) →
      ∃ (x7 : Fin 26) (x8 : Finset ℕ), 5 ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 x12 : Bool) (x13 : ℕ), x13 < 26 + x9 ∧ ∀ (x14 : Fin 26 → Bool), x14 x7 = false → x2 x14 (26 + x9) = (x11 && x2 x14 x13 || x12))
    (hOr : ∀ (x1 : Circuit) (x2 : (Fin 26 → Bool) → ℕ → Bool),
      (∀ (x3 : ℕ) (x4 : Gate), x1.gates[x3]? = some x4 → (x4.op = GateOp.and ∨ x4.op = GateOp.or) ∧ ∃ x6 x7, x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < 26 + x3 ∧ x7 < 26 + x3) →
      x1.size ≤ 62 → 26 ≤ x1.output → x1.output < 26 + x1.size →
      (∃ g : Gate, x1.gates[x1.output - 26]? = some g ∧ g.op = GateOp.or) →
      (∀ (x5 : Fin 26 → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 false) →
      (∀ (x6 : Fin 26 → Bool), x2 x6 x1.output = true ↔ ∃ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) ∧ x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) →
      ∃ (x7 : Fin 26) (x8 : Finset ℕ), 5 ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 x12 : Bool) (x13 : ℕ), x13 < 26 + x9 ∧ ∀ (x14 : Fin 26 → Bool), x14 x7 = false → x2 x14 (26 + x9) = (x11 && x2 x14 x13 || x12)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) → x1.size ≤ (62 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) → (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  intro x1 x2 hLegal hSize hVal hSpec
  have hWiresLen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp; omega
  have hWiresPrefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun k => w'.getD k false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih _ _ (by simp; omega)]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp [List.getElem?_append_left hi]
  have hOutLt : x1.output < 26 + x1.size := by
    by_contra hge
    have hle : 26 + x1.size ≤ x1.output := Nat.le_of_not_lt hge
    let f00 : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13))
    have hTrue : x2 f00 x1.output = true := (hSpec f00).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    rw [hVal f00 x1.output] at hTrue
    unfold Circuit.wires at hTrue
    have hFullLen : (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn f00)).length = 26 + x1.size := by
      rw [hWiresLen, List.length_ofFn]; rfl
    rw [List.getD_eq_default _ _ (by rw [hFullLen]; exact hle)] at hTrue
    cases hTrue
  have hOutGe : 26 ≤ x1.output := by
    by_contra hlt
    have hlt26 : x1.output < 26 := Nat.lt_of_not_ge hlt
    let fAll : Fin 26 → Bool := fun k => decide (k.val = x1.output)
    have hEval : x2 fAll x1.output = true := by
      rw [hVal fAll x1.output]
      unfold Circuit.wires
      rw [hWiresPrefix _ _ _ (by simp [hlt26])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hlt26, fAll]
    have hEdge := (hSpec fAll).mp hEval
    rcases hEdge with ⟨a, b, _, ha, hb⟩
    simp only [fAll, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at ha hb
    omega
  have hIdx : x1.output - 26 < x1.gates.length := by
    change x1.output - 26 < x1.size
    omega
  have hg : x1.gates[x1.output - 26]? = some x1.gates[x1.output - 26] := List.getElem?_eq_getElem hIdx
  rcases (hLegal (x1.output - 26) _ hg).1 with hOp | hOp
  · exact hAnd x1 x2 hLegal hSize hOutGe hOutLt ⟨_, hg, hOp⟩ hVal hSpec
  · exact hOr x1 x2 hLegal hSize hOutGe hOutLt ⟨_, hg, hOp⟩ hVal hSpec
