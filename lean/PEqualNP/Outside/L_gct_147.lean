import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_147_aux

noncomputable def q147 : Polynomial ℤ :=
  3249 + 51984 * Polynomial.X + 367880 * Polynomial.X ^ 2 + 1670896 * Polynomial.X ^ 3 +
  5646720 * Polynomial.X ^ 4 + 15329584 * Polynomial.X ^ 5 + 34985690 * Polynomial.X ^ 6 +
  69133968 * Polynomial.X ^ 7 + 120770346 * Polynomial.X ^ 8 + 189412368 * Polynomial.X ^ 9 +
  269857152 * Polynomial.X ^ 10 + 352364880 * Polynomial.X ^ 11 + 424439765 * Polynomial.X ^ 12 +
  473750560 * Polynomial.X ^ 13 + 491286876 * Polynomial.X ^ 14 + 473750560 * Polynomial.X ^ 15 +
  424439765 * Polynomial.X ^ 16 + 352364880 * Polynomial.X ^ 17 + 269857152 * Polynomial.X ^ 18 +
  189412368 * Polynomial.X ^ 19 + 120770346 * Polynomial.X ^ 20 + 69133968 * Polynomial.X ^ 21 +
  34985690 * Polynomial.X ^ 22 + 15329584 * Polynomial.X ^ 23 + 5646720 * Polynomial.X ^ 24 +
  1670896 * Polynomial.X ^ 25 + 367880 * Polynomial.X ^ 26 + 51984 * Polynomial.X ^ 27 +
  3249 * Polynomial.X ^ 28

lemma factor147 :
    (-Polynomial.C 57 + Polynomial.C 912 * Polynomial.X ^ 5 - Polynomial.C 969 * Polynomial.X ^ 6 + Polynomial.C 969 * Polynomial.X ^ 16 - Polynomial.C 912 * Polynomial.X ^ 17 + Polynomial.C 57 * Polynomial.X ^ 22 : Polynomial ℤ) ^ 2 - (Polynomial.C 272 * Polynomial.X - Polynomial.C 374 * Polynomial.X ^ 2 + Polynomial.C 646 * Polynomial.X ^ 10 - Polynomial.C 646 * Polynomial.X ^ 12 + Polynomial.C 374 * Polynomial.X ^ 20 - Polynomial.C 272 * Polynomial.X ^ 21 : Polynomial ℤ) ^ 2 = (Polynomial.X - 1 : Polynomial ℤ) ^ 16 * q147 := by
  unfold q147
  simp only [map_ofNat]
  ring

end PEqualNP.Outside.L_gct_147_aux

theorem PEqualNP.Outside.L_gct_147 : (Polynomial.X - 1 : Polynomial ℤ) ^ 16 ∣ (-Polynomial.C 57 + Polynomial.C 912 * Polynomial.X ^ 5 - Polynomial.C 969 * Polynomial.X ^ 6 + Polynomial.C 969 * Polynomial.X ^ 16 - Polynomial.C 912 * Polynomial.X ^ 17 + Polynomial.C 57 * Polynomial.X ^ 22 : Polynomial ℤ) ^ 2 - (Polynomial.C 272 * Polynomial.X - Polynomial.C 374 * Polynomial.X ^ 2 + Polynomial.C 646 * Polynomial.X ^ 10 - Polynomial.C 646 * Polynomial.X ^ 12 + Polynomial.C 374 * Polynomial.X ^ 20 - Polynomial.C 272 * Polynomial.X ^ 21 : Polynomial ℤ) ^ 2 ∧ ¬ (Polynomial.X - 1 : Polynomial ℤ) ^ 17 ∣ (-Polynomial.C 57 + Polynomial.C 912 * Polynomial.X ^ 5 - Polynomial.C 969 * Polynomial.X ^ 6 + Polynomial.C 969 * Polynomial.X ^ 16 - Polynomial.C 912 * Polynomial.X ^ 17 + Polynomial.C 57 * Polynomial.X ^ 22 : Polynomial ℤ) ^ 2 - (Polynomial.C 272 * Polynomial.X - Polynomial.C 374 * Polynomial.X ^ 2 + Polynomial.C 646 * Polynomial.X ^ 10 - Polynomial.C 646 * Polynomial.X ^ 12 + Polynomial.C 374 * Polynomial.X ^ 20 - Polynomial.C 272 * Polynomial.X ^ 21 : Polynomial ℤ) ^ 2 := by
  rw [PEqualNP.Outside.L_gct_147_aux.factor147]
  refine ⟨⟨PEqualNP.Outside.L_gct_147_aux.q147, rfl⟩, ?_⟩
  rintro ⟨r, hr⟩
  have h16 : (Polynomial.X - 1 : Polynomial ℤ) ^ 16 ≠ 0 := by
    intro h0
    have hev := congrArg (Polynomial.eval (0 : ℤ)) h0
    simp at hev
  have hq : PEqualNP.Outside.L_gct_147_aux.q147 = (Polynomial.X - 1 : Polynomial ℤ) * r := by
    apply mul_left_cancel₀ h16
    calc (Polynomial.X - 1 : Polynomial ℤ) ^ 16 * PEqualNP.Outside.L_gct_147_aux.q147
        = (Polynomial.X - 1 : Polynomial ℤ) ^ 17 * r := hr
      _ = (Polynomial.X - 1 : Polynomial ℤ) ^ 16 * ((Polynomial.X - 1 : Polynomial ℤ) * r) := by ring
  have hev := congrArg (Polynomial.eval (1 : ℤ)) hq
  simp [PEqualNP.Outside.L_gct_147_aux.q147] at hev
