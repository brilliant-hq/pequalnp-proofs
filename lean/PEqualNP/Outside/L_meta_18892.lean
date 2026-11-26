import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18892

open PEqualNP.CircuitLowerBounds

private def wireDominates (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

private theorem getD_snoc (ws : List Bool) (b : Bool) (i : ℕ) :
    (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
  by_cases hi : i < ws.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (ne_of_lt hi)]
  by_cases he : i = ws.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
       List.getD_eq_default _ _ (by omega)]

private theorem snoc_extends {xs ys : List Bool} {a b : Bool}
    (h : wireDominates xs ys) (hab : a = true → b = true) :
    wireDominates (xs ++ [a]) (ys ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [getD_snoc, ← h.1]
  rw [getD_snoc] at hi
  split_ifs at hi ⊢
  · exact hab hi
  · exact h.2 i hi

private theorem gate_extends {g : Gate} (hop : g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : wireDominates xs ys) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) = true →
    g.op.eval (g.inputs.map (fun i => ys.getD i false)) = true := by
  rcases hop with e | e
  · simpa only [e, GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true]
      using (fun ha (i : ℕ) (hi : i ∈ g.inputs) => h.2 i (ha i hi) :
        (∀ i ∈ g.inputs, xs.getD i false = true) → (∀ i ∈ g.inputs, ys.getD i false = true))
  · simpa only [e, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
      using (fun ⟨i, hi, ha⟩ => ⟨i, hi, h.2 i ha⟩ :
        (∃ i ∈ g.inputs, xs.getD i false = true) → (∃ i ∈ g.inputs, ys.getD i false = true))

private theorem fold_extends (gs : List Gate) {xs ys : List Bool}
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (h : wireDominates xs ys) :
    wireDominates (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) xs)
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
      (snoc_extends h (gate_extends (ops g (by simp)) h))

end PEqualNP.Outside.L_meta_18892

open PEqualNP.Outside.L_meta_18892 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18892 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 x2 x1 → Monotone fun (x5 : Fin x2 → Bool) => PEqualNP.BlindGate.wireValue x1 x2 x5 x3 := by
  intro C n j fit x y hxy
  have support : wireDominates (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases ok : i < n
    · have xOk : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using ok
      have yOk : i < (List.ofFn y).length := by simpa only [List.length_ofFn] using ok
      rw [List.getD_eq_getElem _ _ xOk, List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ yOk, List.getElem_ofFn]
      exact Bool.eq_true_of_true_le (hi ▸ hxy ⟨i, ok⟩)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ok)] at hi
      contradiction
  have f := fold_extends C.gates fit.1 support
  change (C.wires (List.ofFn x)).getD j false ≤ (C.wires (List.ofFn y)).getD j false
  cases val : (C.wires (List.ofFn x)).getD j false
  · simp
  · exact (f.2 j val) ▸ le_rfl
