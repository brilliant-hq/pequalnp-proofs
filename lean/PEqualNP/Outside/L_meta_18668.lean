import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18668

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


end PEqualNP.Outside.L_meta_18668

open PEqualNP.Outside.L_meta_18668 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18668 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (24 : ℕ) → Bool), (∀ (x5 : Fin (24 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro C fit x y hxy k hk
  have ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fit g hg).1
  have support : wireDominates (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases ok : i < 24
    · have xOk : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using ok
      have yOk : i < (List.ofFn y).length := by simpa only [List.length_ofFn] using ok
      rw [List.getD_eq_getElem _ _ xOk, List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ yOk, List.getElem_ofFn]
      exact hxy ⟨i, ok⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi
  exact (fold_extends C.gates ops support).2 k hk

