import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_467_aux

theorem fwd (n m : ℕ) (A : Fin m → Finset (Fin (3 * n))) (hA : ∀ i, (A i).card = 3)
    (S : Finset (Fin m)) (hS : S.card ≤ n) (hc : ∀ x, ∃ i ∈ S, x ∈ A i)
    (x : Fin (3 * n)) (i j : Fin m) (hi : i ∈ S) (hj : j ∈ S) (hxi : x ∈ A i) (hxj : x ∈ A j) :
    i = j := by
  by_contra hne
  have hsub : (Finset.univ : Finset (Fin (3 * n))) ⊆ (S.erase j).biUnion A ∪ (A j).erase x := by
    intro y _
    obtain ⟨k, hk, hyk⟩ := hc y
    by_cases hkj : k = j
    · subst hkj
      by_cases hyx : y = x
      · subst hyx
        exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, hxi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hyx, hyk⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨k, Finset.mem_erase.2 ⟨hkj, hk⟩, hyk⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((S.erase j).biUnion A) ((A j).erase x)
  have h3 : ((S.erase j).biUnion A).card ≤ ∑ k ∈ S.erase j, (A k).card := Finset.card_biUnion_le
  have h4 : ∑ k ∈ S.erase j, (A k).card = (S.erase j).card * 3 := by
    rw [Finset.sum_congr rfl (fun k _ => hA k)]; simp
  have h5 := Finset.card_erase_of_mem hj
  have h6 := Finset.card_erase_of_mem hxj
  have h7 : 0 < S.card := Finset.card_pos.2 ⟨j, hj⟩
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  rw [hA j] at h6
  omega

end PEqualNP.Outside.L_lib_467_aux

theorem PEqualNP.Outside.L_lib_467 : ∀ (n m : ℕ) (A : Fin m → Finset (Fin (3 * n))), (∀ i, (A i).card = 3) →
  ((∃ S : Finset (Fin m), S.card ≤ n ∧ ∀ x, ∃ i ∈ S, x ∈ A i) ↔
   ∃ S : Finset (Fin m), ∀ x : Fin (3 * n), ∃! i : Fin m, i ∈ S ∧ x ∈ A i) := by
  intro n m A hA
  constructor
  · rintro ⟨S, hS, hc⟩
    refine ⟨S, fun x => ?_⟩
    obtain ⟨i, hi, hxi⟩ := hc x
    exact ⟨i, ⟨hi, hxi⟩, fun j ⟨hj, hxj⟩ =>
      PEqualNP.Outside.L_lib_467_aux.fwd n m A hA S hS hc x j i hj hi hxj hxi⟩
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_, fun x => ?_⟩
    · have hd : (S : Set (Fin m)).PairwiseDisjoint A := by
        intro i hi j hj hij
        rw [Function.onFun, Finset.disjoint_left]
        intro x hxi hxj
        exact hij ((hS x).unique ⟨hi, hxi⟩ ⟨hj, hxj⟩)
      have h1 := Finset.card_biUnion hd
      have h2 : (S.biUnion A).card ≤ 3 * n := by
        simpa using Finset.card_le_univ (S.biUnion A)
      have h4 : ∑ k ∈ S, (A k).card = S.card * 3 := by
        rw [Finset.sum_congr rfl (fun k _ => hA k)]; simp
      omega
    · obtain ⟨i, ⟨hi, hxi⟩, _⟩ := hS x
      exact ⟨i, hi, hxi⟩
