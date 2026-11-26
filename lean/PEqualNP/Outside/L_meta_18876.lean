import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18876 : ∃ (x1 : Fin (12 : ℕ)) (x2 : Fin (13 : ℕ)), x1.succ = x2 ∨ x1.succ = x2 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (9 : Fin ((12 : ℕ) + (1 : ℕ))) := by
  exact ⟨0, 1, Or.inl (by decide)⟩
