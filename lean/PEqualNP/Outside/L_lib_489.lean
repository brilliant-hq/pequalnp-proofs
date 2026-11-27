import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_489 : (∀ (n r : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), r ≤ n →
  let levels := (Finset.univ : Finset (Fin n)).powersetCard r
  (levels.sum (fun S => (F.filter (fun C => (C.image Prod.fst) ⊆ S)).card)) =
    F.sum (fun C => let k := (C.image Prod.fst).card
                     if k ≤ r then (n-k).choose (r-k) else 0)) := by
  intro n r F _hr
  dsimp only
  have hswap :
      ((Finset.univ : Finset (Fin n)).powersetCard r).sum
        (fun S => (F.filter (fun C => C.image Prod.fst ⊆ S)).card) =
      F.sum (fun C => (((Finset.univ : Finset (Fin n)).powersetCard r).filter
        (fun S => C.image Prod.fst ⊆ S)).card) := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun C _hC => ?_
  set A : Finset (Fin n) := C.image Prod.fst
  set k : ℕ := A.card
  by_cases hk : k ≤ r
  · rw [if_pos hk]
    have hbij :
        (((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun S => A ⊆ S)).card =
        (Aᶜ.powersetCard (r - k)).card := by
      refine Finset.card_bij (fun S _ => S \ A) ?_ ?_ ?_
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_compl] at hx ⊢
          exact hx.2
        · have hadd := Finset.card_sdiff_add_card_eq_card hS.2
          have hSc : S.card = r := hS.1.2
          omega
      · intro S₁ hS₁ S₂ hS₂ hEq
        simp only [Finset.mem_filter] at hS₁ hS₂
        calc
          S₁ = (S₁ \ A) ∪ A := (Finset.sdiff_union_of_subset hS₁.2).symm
          _ = (S₂ \ A) ∪ A := by rw [hEq]
          _ = S₂ := Finset.sdiff_union_of_subset hS₂.2
      · intro T hT
        simp only [Finset.mem_powersetCard] at hT
        have hdisj : Disjoint T A := by
          refine Finset.disjoint_left.mpr fun x hxT hxA => ?_
          exact (Finset.mem_compl.mp (hT.1 hxT)) hxA
        refine ⟨T ∪ A, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
          rw [Finset.card_union_of_disjoint hdisj, hT.2]
          omega
        · ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hxT | hxA, hnotA⟩
            · exact hxT
            · exact (hnotA hxA).elim
          · intro hxT
            exact ⟨Or.inl hxT, Finset.disjoint_left.mp hdisj hxT⟩
    rw [hbij, Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin]
  · rw [if_neg hk]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S hS hAS
    simp only [Finset.mem_powersetCard] at hS
    have hle : A.card ≤ S.card := Finset.card_le_card hAS
    omega
