import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside

/-- Replace the first gate by an extra input and lower the gate budget by one. -/
theorem R_meta_4817_731
    (hAnd : ∀ (C : Circuit) (k : Fin 12) (i j : Fin 13),
      FanInTwo C → C.size ≤ 16 → ∃ x : Fin 10 → Bool,
        let base := List.ofFn x ++ [x 0 && x 2]
        let w := base ++ [!base.getD k.val false]
        C.eval (w ++ [w.getD i.val false && w.getD j.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hOr : ∀ (C : Circuit) (k : Fin 12) (i j : Fin 13),
      FanInTwo C → C.size ≤ 16 → ∃ x : Fin 10 → Bool,
        let base := List.ofFn x ++ [x 0 && x 2]
        let w := base ++ [!base.getD k.val false]
        C.eval (w ++ [w.getD i.val false || w.getD j.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hNot : ∀ (C : Circuit) (k : Fin 12) (i : Fin 13),
      FanInTwo C → C.size ≤ 16 → ∃ x : Fin 10 → Bool,
        let base := List.ofFn x ++ [x 0 && x 2]
        let w := base ++ [!base.getD k.val false]
        C.eval (w ++ [!w.getD i.val false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),
    PEqualNP.MetaComplexity.FanInTwo x1 →
    x1.size ≤ (17 : ℕ) →
    ∃ (x5 : Fin (10 : ℕ) → Bool),
      have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];
      x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠
        (fun (x7 : Fin (10 : ℕ) → Bool) =>
          x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) ||
          x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) ||
          x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) ||
          x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) ||
          x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) ||
          x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) ||
          x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
          x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
          x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
          x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
          x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
          x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
          x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
          x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
          x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5 := by
  rintro ⟨gates, o⟩ k hFan hSize
  let target (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let w (k : Fin 12) (x : Fin 10 → Bool) : List Bool :=
    let base := List.ofFn x ++ [x 0 && x 2]
    base ++ [!base.getD k.val false]
  change ∃ x, (Circuit.mk gates o).eval (w k x) ≠ target x
  have missing (k' : Fin 12) (x : Fin 10 → Bool) (i : ℕ) (hi : 12 ≤ i) :
      (w k' x).getD i false = false := by
    exact List.getD_eq_default _ _ (by simpa [w] using hi)
  cases gates with
  | nil =>
    -- An empty circuit reads one of the given wires, or the default false.
    let zero : Fin 10 → Bool := fun _ => false
    let edge₁ : Fin 10 → Bool := fun v => decide (v.val = 3 ∨ v.val = 4)
    let edge₂ : Fin 10 → Bool := fun v => decide (v.val = 6 ∨ v.val = 8)
    have len (x : Fin 10 → Bool) : (List.ofFn x ++ [x 0 && x 2]).length = 11 := by
      simp
    change ∃ x, (w k x).getD o false ≠ target x
    by_cases hv : o < 10
    · have readVertex (x : Fin 10 → Bool) : (w k x).getD o false = x ⟨o, hv⟩ := by
        have h₁ : o < (List.ofFn x ++ [x 0 && x 2]).length := by
          rw [len]
          exact Nat.lt_succ_of_lt hv
        have h₂ : o < (List.ofFn x).length := by simpa using hv
        dsimp only [w]
        rw [List.getD_append _ _ _ _ h₁, List.getD_append _ _ _ _ h₂,
          List.getD_eq_getElem _ _ h₂, List.getElem_ofFn]
      by_cases he : o = 3 ∨ o = 4
      · refine ⟨edge₂, ?_⟩
        rw [readVertex]
        change decide (o = 6 ∨ o = 8) ≠ true
        have h : ¬ (o = 6 ∨ o = 8) := by
          rcases he with h₃ | h₄ <;> subst o <;> decide
        rw [decide_eq_false h]
        exact Bool.noConfusion
      · refine ⟨edge₁, ?_⟩
        rw [readVertex]
        change decide (o = 3 ∨ o = 4) ≠ true
        rw [decide_eq_false he]
        exact Bool.noConfusion
    · by_cases hq : o = 10
      · subst o
        refine ⟨edge₁, ?_⟩
        dsimp only [w]
        rw [List.getD_append _ _ _ _ (by rw [len]; decide),
          List.getD_append_right _ _ _ _ (by rw [List.length_ofFn])]
        exact Bool.noConfusion
      · by_cases hn : o = 11
        · subst o
          refine ⟨zero, ?_⟩
          dsimp only [w]
          rw [List.getD_append_right _ _ _ _ (by rw [len]), len]
          change (!(List.replicate 11 false).getD k.val false) ≠ false
          simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq,
            Bool.not_false]
          exact Bool.noConfusion
        · refine ⟨edge₁, ?_⟩
          have ho₁ : 11 ≤ o := Nat.succ_le_of_lt
            (lt_of_le_of_ne (Nat.le_of_not_gt hv) (Ne.symm hq))
          have ho₂ : 12 ≤ o := Nat.succ_le_of_lt (lt_of_le_of_ne ho₁ (Ne.symm hn))
          rw [missing k edge₁ o ho₂]
          exact Bool.noConfusion
  | cons g gs =>
    let tail := Circuit.mk gs o
    have hTail : FanInTwo tail :=
      fun t ht => hFan t (List.mem_cons_of_mem _ ht)
    have hBound : tail.size ≤ 16 := by
      change gs.length + 1 ≤ 17 at hSize
      change gs.length ≤ 16
      exact Nat.le_of_succ_le_succ hSize
    let idx (i : ℕ) : Fin 13 :=
      if h : i < 12 then ⟨i, Nat.lt_succ_of_lt h⟩ else 12
    have read (x : Fin 10 → Bool) (i : ℕ) :
        (w k x).getD (idx i).val false = (w k x).getD i false := by
      by_cases h : i < 12
      · simp only [idx, dite_eq_left h]
      · rw [missing k x i (Nat.le_of_not_gt h)]
        rw [show idx i = (12 : Fin 13) from dite_eq_right h]
        exact missing k x 12 (Nat.le_refl _)
    have hg := hFan g (List.mem_cons_self ..)
    have hl : g.inputs.length ≤ 2 := hg.2
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa using hg.1
    rcases g with ⟨op, l⟩
    change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
    change l.length ≤ 2 at hl
    change ∃ x, tail.eval
      (w k x ++ [op.eval (l.map fun i => (w k x).getD i false)]) ≠ target x
    rcases hop with rfl | rfl | rfl
    · cases l with
      | nil =>
        obtain ⟨x, hx⟩ := hNot tail k 12 hTail hBound
        change tail.eval (w k x ++ [!(w k x).getD 12 false]) ≠ target x at hx
        rw [missing k x 12 (Nat.le_refl _)] at hx
        exact ⟨x, hx⟩
      | cons a rest =>
        cases rest with
        | nil =>
          obtain ⟨x, hx⟩ := hAnd tail k (idx a) (idx a) hTail hBound
          change tail.eval (w k x ++
            [(w k x).getD (idx a).val false && (w k x).getD (idx a).val false]) ≠
            target x at hx
          refine ⟨x, ?_⟩
          change tail.eval (w k x ++ [((w k x).getD a false && true)]) ≠ target x
          simpa only [read, Bool.and_self, Bool.and_true] using hx
        | cons b rest =>
          cases rest with
          | nil =>
            obtain ⟨x, hx⟩ := hAnd tail k (idx a) (idx b) hTail hBound
            change tail.eval (w k x ++
              [(w k x).getD (idx a).val false && (w k x).getD (idx b).val false]) ≠
              target x at hx
            refine ⟨x, ?_⟩
            change tail.eval (w k x ++
              [(w k x).getD a false && ((w k x).getD b false && true)]) ≠ target x
            simpa only [read, Bool.and_true] using hx
          | cons c rest => simp at hl
    · cases l with
      | nil =>
        obtain ⟨x, hx⟩ := hOr tail k 12 12 hTail hBound
        change tail.eval (w k x ++
          [(w k x).getD 12 false || (w k x).getD 12 false]) ≠ target x at hx
        rw [missing k x 12 (Nat.le_refl _)] at hx
        exact ⟨x, hx⟩
      | cons a rest =>
        cases rest with
        | nil =>
          obtain ⟨x, hx⟩ := hOr tail k (idx a) (idx a) hTail hBound
          change tail.eval (w k x ++
            [(w k x).getD (idx a).val false || (w k x).getD (idx a).val false]) ≠
            target x at hx
          refine ⟨x, ?_⟩
          change tail.eval (w k x ++ [((w k x).getD a false || false)]) ≠ target x
          simpa only [read, Bool.or_self, Bool.or_false] using hx
        | cons b rest =>
          cases rest with
          | nil =>
            obtain ⟨x, hx⟩ := hOr tail k (idx a) (idx b) hTail hBound
            change tail.eval (w k x ++
              [(w k x).getD (idx a).val false || (w k x).getD (idx b).val false]) ≠
              target x at hx
            refine ⟨x, ?_⟩
            change tail.eval (w k x ++
              [(w k x).getD a false || ((w k x).getD b false || false)]) ≠ target x
            simpa only [read, Bool.or_false] using hx
          | cons c rest => simp at hl
    · cases l with
      | nil =>
        obtain ⟨x, hx⟩ := hNot tail k 12 hTail hBound
        change tail.eval (w k x ++ [!(w k x).getD 12 false]) ≠ target x at hx
        rw [missing k x 12 (Nat.le_refl _)] at hx
        exact ⟨x, hx⟩
      | cons a rest =>
        obtain ⟨x, hx⟩ := hNot tail k (idx a) hTail hBound
        change tail.eval (w k x ++ [!(w k x).getD (idx a).val false]) ≠ target x at hx
        refine ⟨x, ?_⟩
        change tail.eval (w k x ++ [!(w k x).getD a false]) ≠ target x
        simpa only [read] using hx

end PEqualNP.Outside
