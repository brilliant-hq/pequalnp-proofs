import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18425

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def supported (x y z : List Bool) : Prop :=
  x.length = z.length ∧ y.length = z.length ∧ ∀ i,
    z.getD i false = true → x.getD i false = true ∨ y.getD i false = true

private theorem reading (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (ne_of_lt h)]
  by_cases hEq : i = w.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right hEq, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

private theorem append_supported {x y z : List Bool} {a b c : Bool}
    (h : supported x y z) (hn : c = true → a = true ∨ b = true) :
    supported (x ++ [a]) (y ++ [b]) (z ++ [c]) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro i hi
  rw [reading] at hi
  rw [reading, reading, h.1, h.2.1]
  split_ifs at hi ⊢
  · exact hn hi
  · exact h.2.2 _ hi

private theorem or_supported {x y z : List Bool} {g : Gate}
    (op : g.op = .or) (h : supported x y z) :
    g.op.eval (g.inputs.map (fun i => z.getD i false)) = true →
    g.op.eval (g.inputs.map (fun i => x.getD i false)) = true ∨
      g.op.eval (g.inputs.map (fun i => y.getD i false)) = true := by
  simp only [op, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
  rintro ⟨i, hi, hz⟩
  rcases h.2.2 i hz with hx | hy
  · exact Or.inl ⟨i, hi, hx⟩
  · exact Or.inr ⟨i, hi, hy⟩

private def evaluate (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private theorem evaluate_supported (gs : List Gate) {x y z : List Bool}
    (ops : ∀ g ∈ gs, g.op = .or) (h : supported x y z) :
    supported (evaluate gs x) (evaluate gs y) (evaluate gs z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g tail ih =>
    exact ih (fun j hj => ops j (List.mem_cons_of_mem _ hj))
      (append_supported h (or_supported (ops g (by simp)) h))

private def a (i : Fin 26) : Bool := decide (i = 0)
private def b (i : Fin 26) : Bool := decide (i = 13)
private def both (i : Fin 26) : Bool := a i || b i

private def edge (f : Fin 26 → Bool) : Prop :=
  ∃ p q : Fin 13, (p = q ∨ p = q + 1 ∨ p = q + 3 ∨ p = q + 9) ∧
    f (Fin.castAdd 13 p) = true ∧ f (Fin.natAdd 13 q) = true

instance (f : Fin 26 → Bool) : Decidable (edge f) := by
  unfold edge
  infer_instance

private theorem inputSupport : supported (List.ofFn a) (List.ofFn b) (List.ofFn both) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i h
  by_cases hi : i < 26
  · have al : i < (List.ofFn a).length := by simpa only [List.length_ofFn] using hi
    have bl : i < (List.ofFn b).length := by simpa only [List.length_ofFn] using hi
    have cl : i < (List.ofFn both).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_eq_getElem _ _ cl, List.getElem_ofFn] at h
    rw [List.getD_eq_getElem _ _ al, List.getD_eq_getElem _ _ bl,
        List.getElem_ofFn, List.getElem_ofFn]
    simpa only [both, Bool.or_eq_true] using h
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    cases h

end PEqualNP.Outside.L_meta_18425

open PEqualNP.Outside.L_meta_18425 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18425 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → x1.size ≤ (63 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → ∃ (x6 : Fin (26 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧ x7.size + (5 : ℕ) ≤ x1.size ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), x7.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), (x9 = x10 ∨ x9 = x10 + (1 : Fin (13 : ℕ)) ∨ x9 = x10 + (3 : Fin (13 : ℕ)) ∨ x9 = x10 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x9 ≠ x6 ∧ Fin.natAdd (13 : ℕ) x10 ≠ x6 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true := by
  intro C fit noAnd _ eq
  have ops : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    have notAnd : g.op ≠ .and := by
      intro h
      exact noAnd ⟨⟨i, hi⟩, (congrArg Gate.op e).trans h⟩
    first
    | exact (fit.1 g hg).resolve_left notAnd
    | simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, notAnd, false_or] using fit.1 g hg
  have deny (f : Fin 26 → Bool) (hf : ¬edge f) : C.eval (List.ofFn f) = false := by
    cases h : C.eval (List.ofFn f)
    · rfl
    · exact False.elim (hf ((eq f).mp h))
  have et : C.eval (List.ofFn both) = true := (eq both).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
  have ea := deny a (by decide +kernel)
  have eb := deny b (by decide +kernel)
  have out : C.eval (List.ofFn a) = true ∨ C.eval (List.ofFn b) = true :=
    (evaluate_supported C.gates ops inputSupport).2.2 C.output et
  rcases out with ha | hb
  · cases ea.symm.trans ha
  · cases eb.symm.trans hb
