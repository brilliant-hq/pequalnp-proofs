import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19403

open PEqualNP.AndCount

private lemma build
    (n k : ℕ)
    (N : Finset (Finset (Fin n)))
    (B : Fin k → Finset (Fin n))
    (Z : Fin k → Fin 2 → Finset (Finset (Fin n)))
    (P : Fin k → Finset (Finset (Fin n)))
    (hSched : ∀ (i : Fin k), ∀ p ∈ P i, ∀ (b : Fin 2),
      (∃ v ∈ B i, v ∈ p ∧ ∀ z ∈ Z i b, v ∉ z) ∨
      ∃ j < i, p ∈ P j ∧ Z i b ⊆ Z j 0 ∪ Z j 1) :
    ∃ C : AndCountCircuit n,
      C.WellFormed ∧
      C.size = k ∧
      (∀ v : Fin n,
        ((Finset.univ : Finset (Fin C.size)).filter
          (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤
        ((Finset.univ : Finset (Fin k)).filter (fun i => v ∈ B i)).card) ∧
      (∀ z ∈ N, C.eval z = false) ∧
      (∀ i : Fin k, N ⊆ Z i 0 ∪ Z i 1 → ∀ p ∈ P i, ∀ q : Finset (Fin n),
        p ⊆ q → C.eval q = true) := by
  classical
  let U : Fin k → Finset (Finset (Fin n)) := fun i => Z i 0 ∪ Z i 1
  let C : AndCountCircuit n := {
    size := k
    leftVars := fun i => (B i).filter (fun v => ∀ z ∈ Z i 0, v ∉ z)
    leftGates := fun i => Finset.univ.filter (fun j : Fin k => j < i ∧ Z i 0 ⊆ U j)
    rightVars := fun i => (B i).filter (fun v => ∀ z ∈ Z i 1, v ∉ z)
    rightGates := fun i => Finset.univ.filter (fun j : Fin k => j < i ∧ Z i 1 ⊆ U j)
    outVars := ∅
    outGates := Finset.univ.filter (fun i : Fin k => N ⊆ U i)
  }
  have hWF : C.WellFormed := by
    intro i
    constructor
    · intro j hj
      exact (Finset.mem_filter.mp hj).2.1
    · intro j hj
      exact (Finset.mem_filter.mp hj).2.1
  have hSound : ∀ d (i : Fin k), ∀ z ∈ U i, C.gateValFuel z d i = false := by
    intro d
    induction d with
    | zero =>
      intro i z _
      rfl
    | succ d ih =>
      intro i z hz
      simp only [AndCountCircuit.gateValFuel]
      rcases Finset.mem_union.mp hz with hz0 | hz1
      · have hL : AndCountCircuit.sideTrue z (C.leftVars i) (C.leftGates i) i
            (C.gateValFuel z d) = false := by
          unfold AndCountCircuit.sideTrue
          rw [decide_eq_false_iff_not]
          rintro (⟨v, hv, hvz⟩ | ⟨j, hj, _, hval⟩)
          · exact (Finset.mem_filter.mp hv).2 z hz0 hvz
          · have hsub : Z i 0 ⊆ U j := (Finset.mem_filter.mp hj).2.2
            have hfalse := ih j z (hsub hz0)
            rw [hfalse] at hval
            cases hval
        rw [hL, Bool.false_and]
      · have hR : AndCountCircuit.sideTrue z (C.rightVars i) (C.rightGates i) i
            (C.gateValFuel z d) = false := by
          unfold AndCountCircuit.sideTrue
          rw [decide_eq_false_iff_not]
          rintro (⟨v, hv, hvz⟩ | ⟨j, hj, _, hval⟩)
          · exact (Finset.mem_filter.mp hv).2 z hz1 hvz
          · have hsub : Z i 1 ⊆ U j := (Finset.mem_filter.mp hj).2.2
            have hfalse := ih j z (hsub hz1)
            rw [hfalse] at hval
            cases hval
        rw [hR, Bool.and_false]
  have hComp : ∀ d (i : Fin k), i.val < d → ∀ p ∈ P i, ∀ q : Finset (Fin n),
      p ⊆ q → C.gateValFuel q d i = true := by
    intro d
    induction d with
    | zero =>
      intro i hi
      omega
    | succ d ih =>
      intro i hi p hp q hpq
      simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true]
      constructor
      · unfold AndCountCircuit.sideTrue
        rw [decide_eq_true_eq]
        rcases hSched i p hp 0 with ⟨v, hvB, hvp, hvZ⟩ | ⟨j, hji, hpj, hsub⟩
        · exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hvB, hvZ⟩, hpq hvp⟩
        · have hjlt : j.val < d := by
            have : j.val < i.val := hji
            omega
          exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hsub⟩, hji,
            ih j hjlt p hpj q hpq⟩
      · unfold AndCountCircuit.sideTrue
        rw [decide_eq_true_eq]
        rcases hSched i p hp 1 with ⟨v, hvB, hvp, hvZ⟩ | ⟨j, hji, hpj, hsub⟩
        · exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hvB, hvZ⟩, hpq hvp⟩
        · have hjlt : j.val < d := by
            have : j.val < i.val := hji
            omega
          exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hsub⟩, hji,
            ih j hjlt p hpj q hpq⟩
  refine ⟨C, hWF, rfl, ?_, ?_, ?_⟩
  · intro v
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with hL | hR
    · exact (Finset.mem_filter.mp hL).1
    · exact (Finset.mem_filter.mp hR).1
  · intro z hz
    unfold AndCountCircuit.eval
    rw [decide_eq_false_iff_not]
    rintro (⟨v, hv, _⟩ | ⟨i, hi, hval⟩)
    · exact Finset.notMem_empty v hv
    · have hsub : N ⊆ U i := (Finset.mem_filter.mp hi).2
      have hfalse := hSound k i z (hsub hz)
      change C.gateValFuel z k i = true at hval
      rw [hfalse] at hval
      cases hval
  · intro i hNi p hp q hpq
    unfold AndCountCircuit.eval
    rw [decide_eq_true_eq]
    refine Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNi⟩, ?_⟩
    exact hComp k i i.isLt p hp q hpq

end PEqualNP.Outside.L_meta_19403

theorem PEqualNP.Outside.L_meta_19403 : ∀ (x1 x2 : ℕ) (x3 : Finset (Finset (Fin x1))) (x4 : Fin x2 → Finset (Fin x1)) (x5 : Fin x2 → Fin (2 : ℕ) → Finset (Finset (Fin x1))) (x6 : Fin x2 → Finset (Finset (Fin x1))),   have x7 : Finset (Fin x2) := Finset.univ;   have x8 : Fin x2 → Finset (Finset (Fin x1)) := fun (x8 : Fin x2) => x5 x8 (0 : Fin (2 : ℕ)) ∪ x5 x8 (1 : Fin (2 : ℕ));   (∀ (x9 : Fin x2), ∀ x10 ∈ x6 x9, ∀ (x12 : Fin (2 : ℕ)), (∃ x13 ∈ x4 x9, x13 ∈ x10 ∧ ∀ x14 ∈ x5 x9 x12, x13 ∉ x14) ∨ ∃ x13 < x9, x10 ∈ x6 x13 ∧ x5 x9 x12 ⊆ x8 x13) →     ∃ (x10 : PEqualNP.AndCount.AndCountCircuit x1),       x10.WellFormed ∧         x10.size = x2 ∧           (have x11 : Finset (Fin x10.size) := Finset.univ;             ∀ (x12 : Fin x1), {x13 ∈ x11 | x12 ∈ x10.leftVars x13 ∨ x12 ∈ x10.rightVars x13}.card ≤ {x13 ∈ x7 | x12 ∈ x4 x13}.card) ∧             (∀ x11 ∈ x3, x10.eval x11 = Bool.false) ∧ ∀ (x11 : Fin x2), x3 ⊆ x8 x11 → ∀ x13 ∈ x6 x11, ∀ (x15 : Finset (Fin x1)), x13 ⊆ x15 → x10.eval x15 = Bool.true := by
  intro x1 x2 x3 x4 x5 x6
  dsimp only
  intro hSched
  exact PEqualNP.Outside.L_meta_19403.build x1 x2 x3 x4 x5 x6 hSched
