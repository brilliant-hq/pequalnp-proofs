import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19016

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Wire lemmas adapted from the published proof of L-meta-18800.
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_append_lt {α : Type*} (d : α) (l1 l2 : List α) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getElem_append_left hi,
      List.getD_eq_getElem _ _ hi]

theorem foldl_w_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wstep]; omega)]
    exact getD_append_lt false w _ i hi


private theorem singleton_output {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (h : C.output < n) : C.eval (List.ofFn x) = x ⟨C.output, h⟩ := by
  change (C.gates.foldl wstep (List.ofFn x)).getD C.output false = _
  rw [foldl_w_prefix _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
    List.getElem_ofFn]

private theorem impossible (C : Circuit) (h : C.output < 26)
    (valid : ∀ (x : Fin 26 → Bool), C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 13, a - b ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
        x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true) : False := by
  let x : Fin 26 → Bool := fun i => decide (i.val = C.output)
  have ht : C.eval (List.ofFn x) = true := by
    rw [singleton_output C x h]
    simp [x]
  obtain ⟨a, b, _, ha, hb⟩ := (valid x).mp ht
  have hl : a.val = C.output := of_decide_eq_true ha
  have hr : 13 + b.val = C.output := of_decide_eq_true hb
  omega

end PEqualNP.Outside.L_meta_19016

theorem PEqualNP.Outside.L_meta_19016 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = Bool.true ∧ x5 x12 ∧ x4 x12 x8 = Bool.false ∧ x10 x13 x8 ∧ x1.output < (26 : ℕ) := by
  rintro ⟨C, h⟩
  dsimp only at h
  rcases h with ⟨_, _, _, heval, _, _, _, _, _, _, _, _, _, _, _, hout⟩
  exact PEqualNP.Outside.L_meta_19016.impossible C hout heval
