import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4075_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) → PEqualNP.NotBracket.notCount x2 + (15 : ℕ) ≤ x2.size →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro c C a b fan budget P V aOnly bOnly sup
  by_contra none
  by_cases hn : PEqualNP.NotBracket.notCount C + (15 : ℕ) ≤ C.size
  · exact none (dense c C a b fan budget hn aOnly bOnly sup)
  · have joint : ∀ x : Fin 10 → Bool, (V x a && V x b) = P x := by
      intro x
      cases pval : P x with
      | true =>
        have s := sup x pval
        rw [s.1, s.2]
        rfl
      | false =>
        cases va : V x a with
        | false => rfl
        | true =>
          cases vb : V x b with
          | false => rfl
          | true => exact (none ⟨x, pval, va, vb⟩).elim
    let step := fun (w : List Bool) (h : PEqualNP.CircuitLowerBounds.Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
    have len : ∀ (L : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (L.foldl step w).length = w.length + L.length := by
      intro L
      induction L with
      | nil => intro w; rfl
      | cons h hs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have atEnd : ∀ (l : List Bool) (v : Bool), (l ++ [v]).getD l.length false = v := by
      intro l v
      simp
    let k : ℕ := if c = true then 1 else 2
    let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, k]⟩
    let andGate : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: (C.gates ++ [andGate]), 11 + C.size⟩
    have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro h hh
      rcases List.mem_cons.mp hh with e | hh
      · rw [e]
        exact ⟨Or.inl rfl, Nat.le_refl 2⟩
      · rcases List.mem_append.mp hh with h1 | h1
        · exact fan h h1
        · rw [List.mem_singleton] at h1
          rw [h1]
          exact ⟨Or.inl rfl, Nat.le_refl 2⟩
    have first : ∀ x : Fin 10 → Bool, step (List.ofFn x) g0 = List.ofFn x ++ [x 0 && if c = true then x 1 else x 2] := by
      intro x
      show List.ofFn x ++ [List.all [(List.ofFn x).getD 0 false, (List.ofFn x).getD k false] id] = _
      by_cases hc : c = true <;> simp [k, hc, List.getD_eq_getElem?_getD]
    have evalD : ∀ (x3 : Fin (10 : ℕ) → Bool), D.eval (List.ofFn x3) = P x3 := by
      intro x
      have hl : (C.wires (step (List.ofFn x) g0)).length = 11 + C.size := by
        have e := len C.gates (step (List.ofFn x) g0)
        have e2 : (step (List.ofFn x) g0).length = 11 := by simp [step]
        rw [e2] at e
        exact e
      have top := atEnd (C.wires (step (List.ofFn x) g0)) (andGate.op.eval (andGate.inputs.map fun i => (C.wires (step (List.ofFn x) g0)).getD i false))
      rw [hl] at top
      change ((C.gates ++ [andGate]).foldl step (step (List.ofFn x) g0)).getD (11 + C.size) false = P x
      rw [List.foldl_append]
      change (C.wires (step (List.ofFn x) g0) ++ [andGate.op.eval (andGate.inputs.map fun i => (C.wires (step (List.ofFn x) g0)).getD i false)]).getD (11 + C.size) false = P x
      rw [top, first x, ← joint x]
      show List.all [V x a, V x b] id = (V x a && V x b)
      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
    have bd := bound D fanD evalD
    have z : ([andGate].filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h hh
      rw [List.mem_singleton] at hh
      rw [hh]
      intro hd
      have e := of_decide_eq_true hd
      cases e
    have hg0 : ¬(decide (g0.op = PEqualNP.CircuitLowerBounds.GateOp.not) = true) := by
      intro hd
      have e := of_decide_eq_true hd
      cases e
    have nc : PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount C := by
      change ((g0 :: (C.gates ++ [andGate])).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = (C.gates.filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
      rw [List.filter_cons_of_neg (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) hg0, List.filter_append, List.length_append, z, List.length_nil, Nat.add_zero]
    have dl : D.size = C.size + 2 := by
      change (g0 :: (C.gates ++ [andGate])).length = C.gates.length + 2
      rw [List.length_cons, List.length_append, List.length_singleton]
    omega
