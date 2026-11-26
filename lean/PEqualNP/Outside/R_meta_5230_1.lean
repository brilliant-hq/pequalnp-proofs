import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5230_1
    (h_nocentreless : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
      x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 →
      PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
      have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
      have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;
      have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;
      have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;
      (∀ x15 ∈ x14, have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;
        (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →
      (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) →
      x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → x11.card ≤ (16 : ℕ) → (18 : ℕ) ≤ x3.size + x11.card →
      x12 = ∅ → (1 : ℕ) ≤ x13.card →
      ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 →
      (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ x14.card →
      x14.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False)
    (h_centreless : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
      x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 →
      PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
      have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
      have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;
      have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;
      have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;
      (∀ x15 ∈ x14, have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;
        (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →
      (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) →
      x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → x11.card ≤ (16 : ℕ) → (18 : ℕ) ≤ x3.size + x11.card →
      (1 : ℕ) ≤ x12.card →
      ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 →
      (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card →
      (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False)
    : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;             have x14 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             (∀ x15 ∈ x14,                 have x17 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x15;                 (∀ x18 ∈ x17 (0 : Fin (2 : ℕ)), ∀ x20 ∈ x17 (1 : Fin (2 : ℕ)), x1.Adj x18 x20) ∧ ((x17 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x17 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →               (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ x14, ∃ (x20 : Fin (2 : ℕ)), ∃ x21 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x19 x20) x21 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x16 x17) = Bool.true) → x3.size ≤ (21 : ℕ) → (4 : ℕ) ≤ x11.card → ∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x19 → (7 : ℕ) ≤ x19.card + x11.card → x19.card ≤ (x14 \ x12).card → (0 : ℕ) < (2 : ℕ) * x12.card + x13.card → (x14 \ x12).card + (2 : ℕ) * x12.card + x13.card ≤ x3.size + x11.card - (17 : ℕ) → False := by
  classical
  intro x1 inst x3 x4 x5 hG hleast htop hjunk hcone
  dsimp only
  intro hside hreach hsize hU4 x19 hmin h19_7 h19_le hpos hub
  have hU_sub : PEqualNP.TopForm.Ustar x1 x3 ⊆ x1.edgeFinset := Finset.sdiff_subset
  have hG_card : x1.edgeFinset.card ≤ 16 := by
    let ks : List ℕ := [9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97]
    let es : Finset (Sym2 (Fin 11)) :=
      (ks.map (fun x6 : ℕ => s(Fin.ofNat 11 (x6 / 11), Fin.ofNat 11 (x6 % 11)))).toFinset
    have h_sub : x1.edgeFinset ⊆ es := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : x1.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        rw [hG] at hadj
        rcases hadj with ⟨_, hmem | hmem⟩
        · rw [List.mem_map] at hmem
          rcases hmem with ⟨k, hk, hpair⟩
          have h1 : k / 11 = u.val := (Prod.ext_iff.mp hpair).1
          have h2 : k % 11 = v.val := (Prod.ext_iff.mp hpair).2
          have hu : Fin.ofNat 11 (k / 11) = u := Fin.ext (by simp [Fin.ofNat, h1, Nat.mod_eq_of_lt u.isLt])
          have hv : Fin.ofNat 11 (k % 11) = v := Fin.ext (by simp [Fin.ofNat, h2, Nat.mod_eq_of_lt v.isLt])
          rw [← hu, ← hv]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
        · rw [List.mem_map] at hmem
          rcases hmem with ⟨k, hk, hpair⟩
          have h1 : k / 11 = v.val := (Prod.ext_iff.mp hpair).1
          have h2 : k % 11 = u.val := (Prod.ext_iff.mp hpair).2
          have hv : Fin.ofNat 11 (k / 11) = v := Fin.ext (by simp [Fin.ofNat, h1, Nat.mod_eq_of_lt v.isLt])
          have hu : Fin.ofNat 11 (k % 11) = u := Fin.ext (by simp [Fin.ofNat, h2, Nat.mod_eq_of_lt u.isLt])
          rw [← hu, ← hv, Sym2.eq_swap]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
    exact (Finset.card_le_card h_sub).trans ((List.toFinset_card_le _).trans (by simp [ks]))
  have hU16 : (PEqualNP.TopForm.Ustar x1 x3).card ≤ 16 := (Finset.card_le_card hU_sub).trans hG_card
  have h18 : 18 ≤ x3.size + (PEqualNP.TopForm.Ustar x1 x3).card := by omega
  by_cases hc : (PEqualNP.TopForm.centreless x1 x3).card = 0
  · have hc_empty : PEqualNP.TopForm.centreless x1 x3 = ∅ := Finset.card_eq_zero.mp hc
    have h13_pos : 1 ≤ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by omega
    rw [hc_empty, Finset.sdiff_empty] at h19_le hub
    simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at hub
    exact h_nocentreless x1 x3 x4 x5 hG hleast htop hjunk hcone hside hreach hsize hU4 hU16 h18 hc_empty h13_pos x19 hmin h19_7 h19_le hub
  · have hc_pos : 1 ≤ (PEqualNP.TopForm.centreless x1 x3).card := Nat.pos_of_ne_zero hc
    exact h_centreless x1 x3 x4 x5 hG hleast htop hjunk hcone hside hreach hsize hU4 hU16 h18 hc_pos x19 hmin h19_7 h19_le hub
