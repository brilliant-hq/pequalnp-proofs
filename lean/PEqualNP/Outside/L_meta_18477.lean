import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18477

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

private def single (j i : Fin 32) : Bool := decide (i = j)
private def leftWire (p : Fin 32) : Fin 32 := p
private def rightWire (q : Fin 32) : Fin 32 := q
private def eligible (p q : Fin 32) : Prop := p.val < 16 ∧ 16 ≤ q.val ∧ (([195, 32908, 281, 562, 1124, 2464, 12608, 25216, 34560, 19457, 38914, 4613, 9226, 10260, 20520, 49232] : List ℕ).getD p.val 0).testBit (q.val-16) = true

instance (p q : Fin 32) : Decidable (eligible p q) := by
  unfold eligible
  infer_instance

private def edge (x : Fin 32 → Bool) : Prop :=
  ∃ p q : Fin 32, eligible p q ∧ x (leftWire p) = true ∧ x (rightWire q) = true

private theorem different (p q : Fin 32) (hn : eligible p q) : leftWire p ≠ rightWire q := by
  have hp := hn.1
  have hq := hn.2.1
  intro h
  have e := congrArg Fin.val h
  change p.val = q.val at e
  omega

private def a := single (leftWire 0)
private def b := single (rightWire 16)
private def pair (i : Fin 32) : Bool := a i || b i

private theorem inputSupport : supported (List.ofFn a) (List.ofFn b) (List.ofFn pair) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i h
  by_cases hi : i < 32
  · have al : i < (List.ofFn a).length := by simpa only [List.length_ofFn] using hi
    have bl : i < (List.ofFn b).length := by simpa only [List.length_ofFn] using hi
    have cl : i < (List.ofFn pair).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_eq_getElem _ _ cl, List.getElem_ofFn] at h
    rw [List.getD_eq_getElem _ _ al, List.getD_eq_getElem _ _ bl,
        List.getElem_ofFn, List.getElem_ofFn]
    simpa only [pair, Bool.or_eq_true] using h
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    cases h

end PEqualNP.Outside.L_meta_18477

open PEqualNP.Outside.L_meta_18477 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18477 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (32 : ℕ)) (x6 : Fin (32 : ℕ)), (↑x5 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x6 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x5 (0 : ℕ)).testBit (↑x6 - (16 : ℕ)) = Bool.true) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → (79 : ℕ) ≤ x1.size := by
  intro C fit noAnd computes
  have equivalence (x : Fin 32 → Bool) : C.eval (List.ofFn x) = true ↔ edge x := computes x
  have ops : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    have notAnd : g.op ≠ .and := by
      intro h
      exact noAnd ⟨⟨i, hi⟩, (congrArg Gate.op e).trans h⟩
    have op := (fit g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, notAnd, false_or] using op
  have singletonFalse (j : Fin 32) : C.eval (List.ofFn (single j)) = false := by
    cases h : C.eval (List.ofFn (single j))
    · rfl
    · obtain ⟨p, q, hEdge, hl, hr⟩ := (equivalence _).mp h
      have lp : leftWire p = j := by simpa only [single, decide_eq_true_eq] using hl
      have rq : rightWire q = j := by simpa only [single, decide_eq_true_eq] using hr
      exact False.elim (different p q hEdge (lp.trans rq.symm))
  have yes : C.eval (List.ofFn pair) = true :=
    (equivalence pair).mpr ⟨0, 16, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have out : C.eval (List.ofFn a) = true ∨ C.eval (List.ofFn b) = true :=
    (evaluate_supported C.gates ops inputSupport).2.2 C.output yes
  rcases out with ha | hb
  · cases (singletonFalse (leftWire 0)).symm.trans ha
  · cases (singletonFalse (rightWire 16)).symm.trans hb
