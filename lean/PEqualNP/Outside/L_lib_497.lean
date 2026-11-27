import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_497_aux

open MvPolynomial PEqualNP.ProofComplexity

theorem degX {n : ℕ} (i : Fin n) : (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 1 :=
  (totalDegree_X i).le

theorem factor_eq {n : ℕ} (l : Fin n × Bool) :
    (if l.2 = true then (1 : MvPolynomial (Fin n) (ZMod 2)) + X l.1 else X l.1) =
      X l.1 + (if l.2 = true then 1 else 0) := by
  split_ifs <;> ring

theorem deg_const (b : Bool) :
    ((if b = true then (1 : MvPolynomial (Fin n) (ZMod 2)) else 0)).totalDegree = 0 := by
  split_ifs <;> simp

theorem deg_factor_le {n : ℕ} (l : Fin n × Bool) :
    (if l.2 = true then (1 : MvPolynomial (Fin n) (ZMod 2)) + X l.1 else X l.1).totalDegree ≤ 1 := by
  rw [factor_eq]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact degX _
  · rw [deg_const]; exact Nat.zero_le _

theorem deg_clausePoly_le {n : ℕ} (C : Clause (Fin n)) :
    (clausePoly C).totalDegree ≤ C.card := by
  unfold clausePoly
  calc _ ≤ ∑ l ∈ C, (if l.2 = true then (1 : MvPolynomial (Fin n) (ZMod 2)) + X l.1
          else X l.1).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _l ∈ C, 1 := Finset.sum_le_sum (fun l _ => deg_factor_le l)
    _ = C.card := by simp

theorem deg_prodX_le {n : ℕ} (T : Finset (Fin n)) :
    (∏ i ∈ T, (X i : MvPolynomial (Fin n) (ZMod 2))).totalDegree ≤ T.card := by
  calc _ ≤ ∑ i ∈ T, (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree :=
        totalDegree_finsetProd _ _
    _ ≤ ∑ _i ∈ T, 1 := Finset.sum_le_sum (fun i _ => degX i)
    _ = T.card := by simp

theorem deg_rest {n : ℕ} (C : Clause (Fin n)) :
    clausePoly C - ∏ l ∈ C, (X l.1 : MvPolynomial (Fin n) (ZMod 2)) = 0 ∨
      (clausePoly C - ∏ l ∈ C, (X l.1 : MvPolynomial (Fin n) (ZMod 2))).totalDegree + 1 ≤ C.card := by
  classical
  induction C using Finset.induction_on with
  | empty => left; simp [clausePoly]
  | insert a s ha ih =>
    right
    have hP : clausePoly (insert a s) =
        (X a.1 + (if a.2 = true then 1 else 0)) * clausePoly s := by
      unfold clausePoly; rw [Finset.prod_insert ha, factor_eq]
    rw [hP, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hsplit : (X a.1 + (if a.2 = true then 1 else 0)) * clausePoly s -
        X a.1 * ∏ l ∈ s, (X l.1 : MvPolynomial (Fin n) (ZMod 2)) =
        X a.1 * (clausePoly s - ∏ l ∈ s, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) +
          (if a.2 = true then 1 else 0) * clausePoly s := by ring
    rw [hsplit]
    have h2 : ((if a.2 = true then (1 : MvPolynomial (Fin n) (ZMod 2)) else 0) * clausePoly s).totalDegree
        ≤ s.card := by
      refine (totalDegree_mul _ _).trans ?_
      rw [deg_const]; simpa using deg_clausePoly_le s
    refine Nat.succ_le_succ ((totalDegree_add _ _).trans (max_le ?_ h2))
    rcases ih with h0 | hlt
    · rw [h0, mul_zero]; simp
    · refine (totalDegree_mul _ _).trans ?_
      have := degX a.1
      omega

end PEqualNP.Outside.L_lib_497_aux

open PEqualNP.Outside.L_lib_497_aux in
theorem PEqualNP.Outside.L_lib_497 : (∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (S : Finset (Fin n)) (C : PEqualNP.ProofComplexity.Clause (Fin n)),
  S.Nonempty → (C.image Prod.fst) ⊆ S →
  (∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) →
  PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card (PEqualNP.ProofComplexity.clausePoly C) →
  ∃ q : MvPolynomial (Fin n) (ZMod 2), q.totalDegree < S.card ∧
    PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card ((∏ i ∈ S, MvPolynomial.X i) + q)) := by
  classical
  intro n F S C hS hV hcons hder
  open MvPolynomial PEqualNP.ProofComplexity in
  set V := C.image Prod.fst with hVdef
  set T := S \ V with hTdef
  have hinj : Set.InjOn Prod.fst (C : Set (Fin n × Bool)) := by
    intro a ha b hb hab
    obtain ⟨i, x⟩ := a; obtain ⟨j, y⟩ := b
    simp only at hab; subst hab
    by_contra hne
    have hxy : x ≠ y := fun h => hne (by rw [h])
    cases x <;> cases y
    · exact hxy rfl
    · exact hcons i ⟨hb, ha⟩
    · exact hcons i ⟨ha, hb⟩
    · exact hxy rfl
  have hVcard : V.card = C.card := Finset.card_image_of_injOn hinj
  have hM : ∏ l ∈ C, (MvPolynomial.X l.1 : MvPolynomial (Fin n) (ZMod 2)) = ∏ i ∈ V, MvPolynomial.X i :=
    (Finset.prod_image (fun a ha b hb h => hinj ha hb h)).symm
  have hTV : (∏ i ∈ T, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2))) * ∏ i ∈ V, MvPolynomial.X i =
      ∏ i ∈ S, MvPolynomial.X i := Finset.prod_sdiff hV
  have hcard : T.card + C.card = S.card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hV
    rw [hVcard] at h1; exact h1

  have key : ∀ T' ⊆ T, PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card
      ((∏ i ∈ T', (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2))) * PEqualNP.ProofComplexity.clausePoly C) := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => intro _; simpa using hder
    | insert a s ha ih =>
      intro hsub
      have hs : s ⊆ T := (Finset.subset_insert a s).trans hsub
      rw [Finset.prod_insert ha, mul_assoc]
      refine PEqualNP.ProofComplexity.PCDerivable.mulX a (ih hs) ?_
      rw [← mul_assoc, ← Finset.prod_insert ha]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 := deg_prodX_le (insert a s)
      have h2 := deg_clausePoly_le C
      have h3 := Finset.card_le_card hsub
      omega
  refine ⟨(∏ i ∈ T, MvPolynomial.X i) *
      (PEqualNP.ProofComplexity.clausePoly C - ∏ l ∈ C, (MvPolynomial.X l.1 : MvPolynomial (Fin n) (ZMod 2))), ?_, ?_⟩
  · rcases deg_rest C with h0 | hlt
    · rw [h0, mul_zero]; simpa using hS.card_pos
    · refine (MvPolynomial.totalDegree_mul _ _).trans_lt ?_
      have := deg_prodX_le (n := n) T
      omega
  · have e : (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod 2))) +
        (∏ i ∈ T, MvPolynomial.X i) * (PEqualNP.ProofComplexity.clausePoly C -
          ∏ l ∈ C, (MvPolynomial.X l.1 : MvPolynomial (Fin n) (ZMod 2))) =
        (∏ i ∈ T, MvPolynomial.X i) * PEqualNP.ProofComplexity.clausePoly C := by
      rw [← hTV, ← hM]; ring
    rw [e]; exact key T (le_refl _)
