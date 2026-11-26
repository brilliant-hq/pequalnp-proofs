import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18759

private lemma foldl_wires_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (k : ℕ) (hk : k < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD k false =
      w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    rw [ih _ hk', List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk,
      List.getElem_append_left hk]

private lemma eval_of_output_lt {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (x : Fin n → Bool) (h : C.output < n) :
    C.eval (List.ofFn x) = x ⟨C.output, h⟩ := by
  have hk : C.output < (List.ofFn x).length := by simp [h]
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
  rw [foldl_wires_prefix C.gates (List.ofFn x) C.output hk, List.getD_eq_getElem _ _ hk,
    List.getElem_ofFn]

end PEqualNP.Outside.L_meta_18759

theorem PEqualNP.Outside.L_meta_18759 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (32 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (32 : ℕ)) (x7 : Fin (32 : ℕ)), (↑x6 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x7 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x6 (0 : ℕ)).testBit (↑x7 - (16 : ℕ)) = Bool.true) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (79 : ℕ) ≤ x1.size) := by
  intro x1 hout _ _ hfun
  let x4 : Fin 32 → Bool := fun i => decide (i.val = x1.output)
  have hev : x1.eval (List.ofFn x4) = true := by
    rw [PEqualNP.Outside.L_meta_18759.eval_of_output_lt x1 x4 hout]
    simp [x4]
  obtain ⟨x5, x6, ⟨h5lt, h6ge, _⟩, hx5, hx6⟩ := (hfun x4).mp hev
  simp only [x4, decide_eq_true_eq] at hx5 hx6
  omega
