import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8577_2
    (hTranspose : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (n + n) C →
      (∀ (x : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C x =
        Decidable.decide (∃ (a b : Fin n), (a, b) ∈ E ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd n b) = Bool.true)) →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size = C.size ∧ PEqualNP.TopForm.IsAO2 (n + n) C' ∧
        (∀ (x : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C' x =
          Decidable.decide (∃ (a b : Fin n), (a, b) ∈ E.image Prod.swap ∧ x (Fin.castAdd n a) = Bool.true ∧ x (Fin.natAdd n b) = Bool.true)))
    (hLeftDeg1 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 + (1 : ℕ) < x2.card → x1 + x1 ≤ x4.size →
      (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) →
      (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      (∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) →
      x2.card + x1 ≤ x4.size + (1 : ℕ)) :
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 + (1 : ℕ) < x2.card → x1 + x1 ≤ x4.size → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ)) := by
  intro x1 x2 x3 x4 hCard hSz hC4 hPerm hAO hFun hDeg
  rcases hDeg with hL | ⟨v, hv⟩
  · exact hLeftDeg1 x1 x2 x3 x4 hCard hSz hC4 hPerm hAO hFun hL
  · obtain ⟨C', hC'sz, hC'AO, hC'Fun⟩ := hTranspose x1 x2 x4 hAO hFun
    have hEcard : (x2.image Prod.swap).card = x2.card :=
      Finset.card_image_of_injective x2 Prod.swap_injective
    have hmem : ∀ a b : Fin x1, (a, b) ∈ x2.image Prod.swap ↔ (b, a) ∈ x2 := by
      intro a b
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨⟨p, q⟩, hpq, heq⟩
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact hpq
      · intro h
        exact Finset.mem_image.mpr ⟨(b, a), h, rfl⟩
    have hC4' : ∀ (a b c d : Fin x1), a ≠ b → c ≠ d →
        ¬((a, c) ∈ x2.image Prod.swap ∧ (a, d) ∈ x2.image Prod.swap ∧
          (b, c) ∈ x2.image Prod.swap ∧ (b, d) ∈ x2.image Prod.swap) := by
      intro a b c d hab hcd ⟨h1, h2, h3, h4⟩
      exact hC4 c d a b hcd hab ⟨(hmem a c).mp h1, (hmem b c).mp h3, (hmem a d).mp h2, (hmem b d).mp h4⟩
    have hPerm' : ∀ a : Fin x1, (a, x3.symm a) ∈ x2.image Prod.swap := by
      intro a
      rw [hmem]
      simpa using hPerm (x3.symm a)
    have hL' : ∃ u : Fin x1, ∀ w : Fin x1, (u, w) ∈ x2.image Prod.swap → w = x3.symm u := by
      refine ⟨v, fun w hw => ?_⟩
      have hw' : (w, v) ∈ x2 := (hmem v w).mp hw
      have hxv : x3 w = v := hv w hw'
      exact (Equiv.eq_symm_apply x3).mpr hxv
    have hres := hLeftDeg1 x1 (x2.image Prod.swap) x3.symm C'
      (by omega) (by omega) hC4' hPerm' hC'AO hC'Fun hL'
    omega
