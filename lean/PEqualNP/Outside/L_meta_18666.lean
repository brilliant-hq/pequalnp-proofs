import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18666 : ∀ (x1 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop) [x2 : DecidableRel x1],   have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x1 x5 x4 → x3 x5 = Bool.false);   have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x1 x5 x6 → x4 x6 = Bool.false);   ∀ (x5 : Fin ((12 : ℕ) + (12 : ℕ)) → Bool), (¬∃ (x6 : Fin (12 : ℕ)) (x7 : Fin (12 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (12 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (12 : ℕ) x7) = Bool.true) → ∃ (x7 : Fin (12 : ℕ) → Bool), x4 (x3 x7) = x7 ∧ ∀ (x8 : Fin ((12 : ℕ) + (12 : ℕ))), x5 x8 = Bool.true → Fin.addCases x7 (x3 x7) x8 = Bool.true := by
  intro R inst
  dsimp only
  intro x safe
  let A : Fin 12 → Bool := fun i => x (Fin.castAdd 12 i)
  let cols (a : Fin 12 → Bool) (j : Fin 12) := decide (∀ i, R i j → a i = false)
  let rows (b : Fin 12 → Bool) (i : Fin 12) := decide (∀ j, R i j → b j = false)
  let B := cols A
  let D := rows B
  have cb (a : Fin 12 → Bool) (j : Fin 12) :
      cols a j = true ↔ ∀ i, R i j → a i = false := by simp [cols]
  have rb (b : Fin 12 → Bool) (i : Fin 12) :
      rows b i = true ↔ ∀ j, R i j → b j = false := by simp [rows]
  have extA i (hi : A i = true) : D i = true := by
    apply (rb B i).2
    intro j hR
    cases hj : B j with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (hi.symm.trans ((cb A j).1 hj i hR)))
  have eq : cols D = B := by
    funext j
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hj
      apply (cb A j).2
      intro i hR
      cases hi : A i with
      | false => rfl
      | true => exact False.elim (Bool.noConfusion ((extA i hi).symm.trans ((cb D j).1 hj i hR)))
    · intro hj
      apply (cb D j).2
      intro i hR
      cases hi : D i with
      | false => rfl
      | true => exact False.elim (Bool.noConfusion (hj.symm.trans ((rb B i).1 hi j hR)))
  change ∃ d, rows (cols d) = d ∧ ∀ i, x i = true → Fin.addCases d (cols d) i = true
  refine ⟨D,by rw [eq],?_⟩
  intro i
  refine Fin.addCases (fun k hk => ?_) (fun j hj => ?_) i
  · simpa using extA k hk
  · simp only [Fin.addCases_right,eq]
    apply (cb A j).2
    intro k hR
    cases hk : A k with
    | false => rfl
    | true => exact (safe ⟨k,j,hR,hk,hj⟩).elim
