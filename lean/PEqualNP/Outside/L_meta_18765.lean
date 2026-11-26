import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18765_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_append_left_lt (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (a : List Bool) (v : Bool) :
    (a ++ [v]).getD a.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, wstep]; omega

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep w g) (by simp [wstep]; omega)]
    exact getD_append_left_lt w _ i hi

theorem main_proof :
    ∀ (n : ℕ) (C : Circuit) (r s : ℕ) (t : Fin n), IsAO2 n C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → r < n + C.size → s < n + C.size →
      r ≠ s → r ≠ t.val →
      ∃ (D : Circuit) (a b : ℕ), D.size ≤ C.size + 2 ∧ IsAO2 n D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧ a ≠ b ∧ a < n + D.size ∧ b < n + D.size ∧
        ∀ x : Fin n → Bool,
          wireValue D n x a = (wireValue C n x r || wireValue C n x s) ∧
          wireValue D n x b = (wireValue C n x r || x t) := by
  intro n C r s t hao hnd hr hs hrs hrt
  let g1 : Gate := ⟨GateOp.or, [r, s]⟩
  let g2 : Gate := ⟨GateOp.or, [r, t.val]⟩
  let D : Circuit := ⟨C.gates ++ [g1, g2], C.output⟩
  have hDsz : D.size = C.size + 2 := by simp [D, Circuit.size]
  refine ⟨D, n + C.size, n + C.size + 1, by omega, ?_, ?_, by omega, by omega, by omega, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hao.1 g h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact Or.inr rfl
    · intro j hj i hi
      have hj' : j < C.gates.length + 2 := by simpa [D] using hj
      by_cases hlt : j < C.gates.length
      · have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt D j = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, D, List.getElem?_append_left hlt]
        rw [hgat] at hi
        exact hao.2.1 j hlt i hi
      · by_cases heq : j = C.gates.length
        · subst heq
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt D C.gates.length = g1 := by
            simp [PEqualNP.MetaComplexity.NestedCover.gateAt, D]
          rw [hgat] at hi
          simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
          simp only [Circuit.size] at hr hs
          rcases hi with rfl | rfl <;> omega
        · have heq2 : j = C.gates.length + 1 := by omega
          subst heq2
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt D (C.gates.length + 1) = g2 := by
            simp [PEqualNP.MetaComplexity.NestedCover.gateAt, D, List.getElem?_append_right (by omega : C.gates.length ≤ C.gates.length + 1)]
          rw [hgat] at hi
          simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
          have ht : t.val < n := t.isLt
          simp only [Circuit.size] at hr
          rcases hi with rfl | rfl <;> omega
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hao.2.2 g h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> rfl
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hnd g h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · simp [g1, hrs]
      · simp [g2, hrt]
  · intro x
    let ws := C.gates.foldl wstep (List.ofFn x)
    have hws_len : ws.length = n + C.size := by
      simp [ws, foldl_len, List.length_ofFn, Circuit.size]
    have hDw : D.wires (List.ofFn x) = (ws ++ [ws.getD r false || ws.getD s false]) ++
        [((ws ++ [ws.getD r false || ws.getD s false]).getD r false) ||
         ((ws ++ [ws.getD r false || ws.getD s false]).getD t.val false)] := by
      change ((C.gates ++ [g1, g2]).foldl wstep (List.ofFn x)) = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      simp [ws, wstep, g1, g2, GateOp.eval]
    have htr : ws.getD t.val false = x t := by
      rw [foldl_getD_lt C.gates (List.ofFn x) t.val (by simp [List.length_ofFn, t.isLt])]
      simp [List.getD_eq_getElem?_getD, t.isLt]
    have hlen1 : (ws ++ [ws.getD r false || ws.getD s false]).length = n + C.size + 1 := by
      simp [hws_len]
    have hgetr : (ws ++ [ws.getD r false || ws.getD s false]).getD r false = ws.getD r false :=
      getD_append_left_lt ws _ r (by omega)
    have hgett : (ws ++ [ws.getD r false || ws.getD s false]).getD t.val false = x t := by
      rw [getD_append_left_lt ws _ t.val (by have := t.isLt; omega), htr]
    constructor
    · simp only [BlindGate.wireValue, hDw]
      rw [getD_append_left_lt _ _ (n + C.size) (by omega), ← hws_len, getD_snoc_eq]
      rfl
    · simp only [BlindGate.wireValue, hDw]
      rw [← hlen1, getD_snoc_eq, hgetr, hgett]
      rfl

end PEqualNP.Outside.L_meta_18765_aux

theorem PEqualNP.Outside.L_meta_18765 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x7 ∈ x2.gates, x7.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → x3 ≠ ↑x5 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x12.size ≤ x2.size + (2 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x12 ∧ (∀ x15 ∈ x12.gates, x15.inputs.Nodup) ∧ x13 ≠ x14 ∧ x13 < x1 + x12.size ∧ x14 < x1 + x12.size ∧ ∀ (x15 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x12 x1 x15 x13 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || PEqualNP.BlindGate.wireValue x2 x1 x15 x4) ∧ PEqualNP.BlindGate.wireValue x12 x1 x15 x14 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || x15 x5))  := by
  exact PEqualNP.Outside.L_meta_18765_aux.main_proof
