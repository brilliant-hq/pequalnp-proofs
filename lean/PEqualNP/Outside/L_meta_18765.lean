import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18765

private lemma foldl_wires_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_wires_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    rw [ih _ hi']
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

private lemma wires_length (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  foldl_wires_length C.gates x

private lemma wires_getD_input (C : PEqualNP.CircuitLowerBounds.Circuit) {n : ℕ}
    (x : Fin n → Bool) (t : Fin n) :
    (C.wires (List.ofFn x)).getD t.val false = x t := by
  have ht : t.val < (List.ofFn x).length := by simp
  rw [PEqualNP.CircuitLowerBounds.Circuit.wires, foldl_wires_prefix C.gates (List.ofFn x) t.val ht]
  rw [List.getD_eq_getElem _ _ ht, List.getElem_ofFn]

end PEqualNP.Outside.L_meta_18765

theorem PEqualNP.Outside.L_meta_18765 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x7 ∈ x2.gates, x7.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → x3 ≠ ↑x5 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x12.size ≤ x2.size + (2 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x12 ∧ (∀ x15 ∈ x12.gates, x15.inputs.Nodup) ∧ x13 ≠ x14 ∧ x13 < x1 + x12.size ∧ x14 < x1 + x12.size ∧ ∀ (x15 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x12 x1 x15 x13 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || PEqualNP.BlindGate.wireValue x2 x1 x15 x4) ∧ PEqualNP.BlindGate.wireValue x12 x1 x15 x14 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || x15 x5)) := by
  intro n C r s t hAO2 hNodup hr hs hrs hrt
  let g1 : PEqualNP.CircuitLowerBounds.Gate :=
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [r, s] }
  let g2 : PEqualNP.CircuitLowerBounds.Gate :=
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [r, t.val] }
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates ++ [g1, g2], output := C.output }
  refine ⟨D, n + C.size, n + C.size + 1, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact hAO2.1 g hg
      · exact Or.inr rfl
      · exact Or.inr rfl
    · intro j hj i hi
      simp only [D, List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hlt : j < C.gates.length
      · have hget : PEqualNP.MetaComplexity.NestedCover.gateAt D j =
            PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
          simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hlt,
            List.getElem_append_left hlt]
        rw [hget] at hi
        exact hAO2.2.1 j hlt i hi
      · by_cases hjeq : j = C.gates.length
        · subst hjeq
          have hget : PEqualNP.MetaComplexity.NestedCover.gateAt D C.gates.length = g1 := by
            simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
            simp
          rw [hget] at hi
          simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact hr
          · exact hs
        · have hjeq2 : j = C.gates.length + 1 := by omega
          subst hjeq2
          have hget : PEqualNP.MetaComplexity.NestedCover.gateAt D (C.gates.length + 1) = g2 := by
            simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]
            have : C.gates.length + 1 - C.gates.length = 1 := by omega
            simp [this]
          rw [hget] at hi
          simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · change i < n + C.gates.length at hr; omega
          · have := t.isLt; omega
    · intro g hg
      simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact hAO2.2.2 g hg
      · rfl
      · rfl
  · intro g hg
    simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hNodup g hg
    · simp [g1, hrs]
    · simp [g2, hrt]
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]; omega
  · intro x
    let w := C.wires (List.ofFn x)
    have hlen : w.length = n + C.size := by
      simpa [w] using (PEqualNP.Outside.L_meta_18765.wires_length C (List.ofFn x)).trans (by simp)
    let v1 := g1.op.eval (g1.inputs.map fun i => w.getD i false)
    let w1 := w ++ [v1]
    let v2 := g2.op.eval (g2.inputs.map fun i => w1.getD i false)
    have hw : D.wires (List.ofFn x) = w1 ++ [v2] := by
      simp [D, w1, w, v1, v2, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append]
    have hlen1 : w1.length = n + C.size + 1 := by simp [w1, hlen]
    have hv1 : v1 = (w.getD r false || w.getD s false) := by
      simp [v1, g1, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have hwr1 : w1.getD r false = w.getD r false := by
      have hlt : r < w.length := by omega
      rw [List.getD_eq_getElem _ _ (by simp [w1]; omega), List.getD_eq_getElem _ _ hlt]
      exact List.getElem_append_left hlt
    have hwt1 : w1.getD t.val false = x t := by
      have hlt : t.val < w.length := by have := t.isLt; omega
      rw [List.getD_eq_getElem _ _ (by simp [w1]; omega), List.getElem_append_left hlt]
      rw [← List.getD_eq_getElem _ _ hlt]
      exact PEqualNP.Outside.L_meta_18765.wires_getD_input C x t
    have hv2 : v2 = (w.getD r false || x t) := by
      simp only [v2, g2, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [hwr1, hwt1]
    constructor
    · simp only [PEqualNP.BlindGate.wireValue, hw]
      have hlt : n + C.size < w1.length := by omega
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt]
      have : w1[n + C.size]'hlt = v1 := by
        simp only [w1]
        rw [List.getElem_append_right (by omega)]
        have : n + C.size - w.length = 0 := by omega
        simp [this]
      rw [this, hv1]
    · simp only [PEqualNP.BlindGate.wireValue, hw, ← hlen1]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simpa [w] using hv2
