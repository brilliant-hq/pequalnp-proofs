import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18397_5
    (h1 : ∀ (a b : ℕ) (π : Fin a → Fin b) (C : PEqualNP.CircuitLowerBounds.Circuit) (j w : ℕ),
      j < C.size → w < a+j → PEqualNP.TopForm.IsAO2 a C →
      (∀ z, PEqualNP.CleanedNonEdge.wireVal a C (a+j) (z ∘ π) = PEqualNP.CleanedNonEdge.wireVal a C w (z ∘ π)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 b D ∧ D.size + 1 = C.size ∧
        ∀ z, PEqualNP.MetaComplexity.circuitFun b D z = PEqualNP.MetaComplexity.circuitFun a C (z ∘ π))
    (h2 : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let sq := fun H : Finset (Fin n × Fin m) => ∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ H ∧ (a,d) ∈ H ∧ (b,c) ∈ H ∧ (b,d) ∈ H)
      let mat := fun K : Finset (Fin n × Fin m) => Set.InjOn Prod.fst (K : Set (Fin n × Fin m)) ∧ Set.InjOn Prod.snd (K : Set (Fin n × Fin m))
      let ev := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (H : Finset (Fin n × Fin m)) => ∀ z, PEqualNP.MetaComplexity.circuitFun (n+m) D z =
        decide (∃ a b, (a,b) ∈ H ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true)
      sq E → M ⊆ E → mat M → PEqualNP.TopForm.IsAO2 (n+m) C → ev C E →
      (∀ (f : Fin n → Fin n) (g : Fin m → Fin m),
        let H := E.image (Prod.map f g)
        sq H → (∃ K ⊆ H, mat K ∧ E.card+M.card ≤ H.card+K.card+1) →
        ∀ j < C.size, ∀ w < n+m+j, ∃ z, let x := z ∘ (Fin.addCases (fun a => Fin.castAdd m (f a)) (fun b => Fin.natAdd n (g b)))
          PEqualNP.CleanedNonEdge.wireVal (n+m) C (n+m+j) x ≠ PEqualNP.CleanedNonEdge.wireVal (n+m) C w x) → E.card+M.card ≤ C.size+1)
    (h3 : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)),
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
      M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
      Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card) : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C sqE leg semE _
  classical
  let sq := fun H : Finset (Fin n × Fin m) => ∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ H ∧ (a,d) ∈ H ∧ (b,c) ∈ H ∧ (b,d) ∈ H)
  let mat := fun K : Finset (Fin n × Fin m) => Set.InjOn Prod.fst (K : Set (Fin n × Fin m)) ∧ Set.InjOn Prod.snd (K : Set (Fin n × Fin m))
  let ev := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (H : Finset (Fin n × Fin m)) => ∀ z, PEqualNP.MetaComplexity.circuitFun (n+m) D z =
        decide (∃ a b, (a,b) ∈ H ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true)
  have bound (s : ℕ) : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (F M : Finset (Fin n × Fin m)),
      D.size = s → sq F → M ⊆ F → mat M → PEqualNP.TopForm.IsAO2 (n+m) D → ev D F →
        F.card+M.card ≤ D.size+1 := by
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro D F M sz hs hm hmat hd he
      by_contra! fail
      apply (not_le_of_gt fail) (h2 n m F M D hs hm hmat hd he ?_)
      intro f g
      dsimp only
      rintro hs' ⟨K,hK,mK,cost⟩ j hj w hw
      by_contra eqv
      push Not at eqv
      let π : Fin (n+m) → Fin (n+m) := Fin.addCases (fun a => Fin.castAdd m (f a)) (fun b => Fin.natAdd n (g b))
      let H := F.image (Prod.map f g)
      obtain ⟨D',hd',sz',he'⟩ := h1 (n+m) (n+m) π D j w hj hw hd eqv
      have semH : ev D' H := by
        intro z
        rw [he', he]
        congr 1
        apply propext
        constructor
        · rintro ⟨a,b,hab,ha,hb⟩
          exact ⟨f a,g b,Finset.mem_image.mpr ⟨(a,b),hab,rfl⟩,by simpa [π] using ha,by simpa [π] using hb⟩
        · rintro ⟨a,b,hab,ha,hb⟩
          obtain ⟨⟨u,v⟩,hu,eq⟩ := Finset.mem_image.mp hab
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
          exact ⟨u,v,hu,by simpa [π] using ha,by simpa [π] using hb⟩
      have small := ih D'.size (by omega) D' H K rfl hs' hK mK hd' semH
      change F.card+M.card ≤ H.card+K.card+1 at cost
      omega
  obtain ⟨M,A,B,sub,ml,mr,cov,dual⟩ := h3 n m E
  have le := bound C.size C E M rfl sqE sub ⟨ml,mr⟩ leg semE
  exact ⟨A,B,cov,by omega⟩
