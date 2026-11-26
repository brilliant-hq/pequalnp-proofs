import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18666 : ∀ (x1 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop) [x2 : DecidableRel x1],   have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x1 x5 x4 → x3 x5 = Bool.false);   have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x1 x5 x6 → x4 x6 = Bool.false);   ∀ (x5 : Fin ((12 : ℕ) + (12 : ℕ)) → Bool), (¬∃ (x6 : Fin (12 : ℕ)) (x7 : Fin (12 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (12 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (12 : ℕ) x7) = Bool.true) → ∃ (x7 : Fin (12 : ℕ) → Bool), x4 (x3 x7) = x7 ∧ ∀ (x8 : Fin ((12 : ℕ) + (12 : ℕ))), x5 x8 = Bool.true → Fin.addCases x7 (x3 x7) x8 = Bool.true := by
  dsimp only
  intro R inst input independent
  let left : Fin 12 → Bool := fun i => input (Fin.castAdd 12 i)
  let right : Fin 12 → Bool := fun j => input (Fin.natAdd 12 j)
  let freeR (a : Fin 12 → Bool) (j : Fin 12) :=
    decide (∀ i, R i j → a i = false)
  let freeL (b : Fin 12 → Bool) (i : Fin 12) :=
    decide (∀ j, R i j → b j = false)
  let B := freeR left
  let A := freeL B
  have includeLeft (i : Fin 12) (hi : left i = true) : A i = true := by
    apply decide_eq_true
    intro j edge
    apply decide_eq_false
    intro all
    exact Bool.noConfusion (hi.symm.trans (all i edge))
  have stable : freeR A = B := by
    funext j
    apply Bool.eq_iff_iff.mpr
    refine ⟨?_, ?_⟩
    · intro hj
      apply decide_eq_true
      intro i edge
      cases h : left i
      · rfl
      · have hA := includeLeft i h
        have no : A i = false := (of_decide_eq_true hj) i edge
        exact Bool.noConfusion (hA.symm.trans no)
    · intro hj
      apply decide_eq_true
      intro i edge
      apply decide_eq_false
      intro all
      exact Bool.noConfusion (hj.symm.trans (all j edge))
  refine ⟨A, ?_, ?_⟩
  · change freeL (freeR A) = A
    rw [stable]
  · change ∀ i, input i = true → Fin.addCases A (freeR A) i = true
    rw [stable]
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j hj
      simpa using includeLeft j hj
    · intro j hj
      simp only [Fin.addCases_right]
      apply decide_eq_true
      intro k edge
      cases h : left k
      · rfl
      · exact (independent ⟨k, j, edge, h, hj⟩).elim

