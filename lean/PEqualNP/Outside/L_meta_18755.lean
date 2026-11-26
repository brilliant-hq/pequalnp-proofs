import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18755

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

end PEqualNP.Outside.L_meta_18755

theorem PEqualNP.Outside.L_meta_18755 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) := by
  intro x1 hout _ _ hfun _
  let x4 : Fin 42 → Bool := fun i => decide (i.val = x1.output)
  have hev : x1.eval (List.ofFn x4) = true := by
    rw [PEqualNP.Outside.L_meta_18755.eval_of_output_lt x1 x4 hout]
    simp [x4]
  obtain ⟨x5, x6, ⟨h5lt, h6ge, _⟩, hx5, hx6⟩ := (hfun x4).mp hev
  simp only [x4, decide_eq_true_eq] at hx5 hx6
  omega
