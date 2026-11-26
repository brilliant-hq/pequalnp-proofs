import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18904
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private def tick (w : List ℕ) (g : Gate) : List ℕ :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  w ++ [if g.op.eval [false,true] = true then a ||| b else a &&& b]

private theorem extend (n : ℕ) (gs : List Gate) (g : Gate)
    (old : IsAO2 n ⟨gs, 0⟩) (op : g.op = .and ∨ g.op = .or)
    (len : g.inputs.length = 2) (earlier : ∀ i ∈ g.inputs, i < n + gs.length) :
    IsAO2 n ⟨gs ++ [g], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with e | e
    · exact old.1 z e
    · exact (List.mem_singleton.mp e).symm ▸ op
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs at hi
    by_cases h : j < gs.length
    · rw [List.getD_append _ _ _ _ h] at hi
      exact old.2.1 j h i hi
    · have same : j = gs.length := by simp at hj; omega
      subst j
      have read : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [read] at hi
      exact earlier i hi
  · intro z hz
    rcases List.mem_append.mp hz with e | e
    · exact old.2.2 z e
    · exact (List.mem_singleton.mp e).symm ▸ len

private theorem build (xs : List ℕ) (value : ℕ → ℕ) (k : ℕ)
    (initial : ∀ i < xs.length, value i = xs.getD i 0)
    (step : ∀ j < k, ∃ a < xs.length + j, ∃ b < xs.length + j,
      value (xs.length+j) = value a ||| value b ∨ value (xs.length+j) = value a &&& value b) :
    ∃ gs : List Gate, gs.length = k ∧ IsAO2 xs.length ⟨gs, 0⟩ ∧
      (gs.foldl tick xs).length = xs.length + k ∧
      ∀ i < xs.length + k, (gs.foldl tick xs).getD i 0 = value i := by
  induction k with
  | zero =>
    refine ⟨[], rfl, ?_, by simp, ?_⟩
    · simp [IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack]
    · simpa using fun i hi => (initial i hi).symm
  | succ k ih =>
    obtain ⟨gs, count, fits, len, values⟩ := ih (fun j hj => step j (by omega))
    obtain ⟨a, ha, b, hb, h⟩ := step k (by omega)
    let op : GateOp := if value (xs.length+k) = value a ||| value b then .or else .and
    let g : Gate := ⟨op,[a,b]⟩
    have kind : g.op = .and ∨ g.op = .or := by unfold g op; split <;> simp
    let w := gs.foldl tick xs
    have va : w.getD a 0 = value a := values a ha
    have vb : w.getD b 0 = value b := values b hb
    have append : tick w g = w ++ [value (xs.length + k)] := by
      unfold tick g op
      split
      · rename_i e
        simp [GateOp.eval, e, -List.getD_eq_getElem?_getD]
        change w.getD a 0 ||| w.getD b 0 = _
        rw [va, vb]
      · rename_i e
        have e' := h.resolve_left e
        simp [GateOp.eval, e', -List.getD_eq_getElem?_getD]
        change w.getD a 0 &&& w.getD b 0 = _
        rw [va, vb]
    refine ⟨gs ++ [g], by simp [count], extend _ _ _ fits kind rfl ?_, ?_, ?_⟩
    · intro i hi
      rcases (by simpa [g] using hi : i = a ∨ i = b) with rfl | rfl
      · simpa [count] using ha
      · simpa [count] using hb
    · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (tick w g).length = _
      rw [append]
      simp [w, len, Nat.add_assoc]
    · intro i hi
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (tick w g).getD i 0 = _
      rw [append]
      by_cases old : i < xs.length + k
      · exact (List.getD_append _ _ _ _ (len.symm ▸ old)).trans (values i old)
      · have ix : i = xs.length + k := by omega
        subst i
        rw [← len]
        simp [w, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_18904
open PEqualNP.Outside.L_meta_18904 PEqualNP.CircuitLowerBounds PEqualNP.TopForm in
theorem PEqualNP.Outside.L_meta_18904 : ∀ (x1 : List ℕ) (x2 : ℕ) (x3 : ℕ → ℕ), (∀ x4 < x1.length, x3 x4 = x1.getD x4 (0 : ℕ)) → (∀ x5 < x2, ∃ x7 < x1.length + x5, ∃ x8 < x1.length + x5, x3 (x1.length + x5) = x3 x7 ||| x3 x8 ∨ x3 (x1.length + x5) = x3 x7 &&& x3 x8) → ∀ x6 < x1.length + x2, ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size ≤ x2 ∧ PEqualNP.TopForm.IsAO2 x1.length x8 ∧ (List.foldl (fun (x9 : List ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) => x9 ++ [if x10.op.eval [Bool.false, Bool.true] = Bool.true then x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) ||| x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ) else x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) &&& x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)]) x1 x8.gates).getD x8.output (0 : ℕ) = x3 x6 := by
  intro xs k value initial step chosen hc
  obtain ⟨gs, size, fits, _, values⟩ := build xs value k initial step
  exact ⟨⟨gs, chosen⟩, size.le, fits, values chosen hc⟩
