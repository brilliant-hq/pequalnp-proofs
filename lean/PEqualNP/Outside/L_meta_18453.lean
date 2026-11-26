import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18453

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

private def a : List Bool := PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))
private def b : List Bool := PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin 13)) ({0} : Finset (Fin 13))
private def pair : List Bool := PEqualNP.GenericRejection.incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))

private theorem probes : supported a b pair := by
  have core : ∀ i : Fin 26, pair.getD i.val false = true →
      a.getD i.val false = true ∨ b.getD i.val false = true := by decide +kernel
  refine ⟨by decide, by decide, ?_⟩
  intro i hi
  by_cases ok : i < 26
  · exact core ⟨i, ok⟩ hi
  · have length : pair.length = 26 := by decide
    rw [List.getD_eq_default _ _ (by omega)] at hi
    cases hi

end PEqualNP.Outside.L_meta_18453

open PEqualNP.Outside.L_meta_18453 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18453 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (64 : ℕ) ≤ x1.size := by
  intro C fit noAnd computes _ _
  have ops : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    have notAnd : g.op ≠ .and := by
      intro h
      exact noAnd ⟨⟨i, hi⟩, (congrArg Gate.op e).trans h⟩
    have op := (fit g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, notAnd, false_or] using op
  have ha : C.eval a = false := (computes {0} ∅).trans (by decide +kernel)
  have hb : C.eval b = false := (computes ∅ {0}).trans (by decide +kernel)
  have hp : C.eval pair = true := (computes {0} {0}).trans (by decide +kernel)
  have out : C.eval a = true ∨ C.eval b = true := (evaluate_supported C.gates ops probes).2.2 C.output hp
  rcases out with ea | eb
  · cases ha.symm.trans ea
  · cases hb.symm.trans eb
