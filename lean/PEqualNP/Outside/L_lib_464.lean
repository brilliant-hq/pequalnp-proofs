import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_464_aux

theorem split (n : ℕ) (w : Fin n → ℕ) (a b : ℕ) (H : Finset (Fin n ⊕ Bool)) :
    ∑ i ∈ H, (Sum.elim w (fun c => if c then a else b) : Fin n ⊕ Bool → ℕ) i =
      (∑ i ∈ Finset.univ.filter (fun i => Sum.inl i ∈ H), w i)
        + (if Sum.inr true ∈ H then a else 0) + (if Sum.inr false ∈ H then b else 0) := by
  have h : ∑ i ∈ H, (Sum.elim w (fun c => if c then a else b) : Fin n ⊕ Bool → ℕ) i =
      ∑ i, if i ∈ H then (Sum.elim w (fun c => if c then a else b) : Fin n ⊕ Bool → ℕ) i else 0 := by
    rw [Finset.sum_ite_mem]; simp
  rw [h, Fintype.sum_sum_type, Fintype.sum_bool, Finset.sum_filter]
  simp
  omega

end PEqualNP.Outside.L_lib_464_aux

open PEqualNP.Outside.L_lib_464_aux in
theorem PEqualNP.Outside.L_lib_464 : ∀ (n t : ℕ) (w : Fin n → ℕ),
  let W := ∑ i, w i
  let v : Fin n ⊕ Bool → ℕ := Sum.elim w (fun b => if b then W + t else 2 * W - t)
  t ≤ W →
  ((∃ S : Finset (Fin n), (∑ i ∈ S, w i) = t) ↔
   ∃ H : Finset (Fin n ⊕ Bool), (∑ i ∈ H, v i) = ∑ i ∈ Hᶜ, v i) := by
  classical
  intro n t w W v ht
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨Finset.univ.filter (fun x => Sum.elim (fun i => i ∈ S) (fun b => b = false) x), ?_⟩
    rw [split n w (W + t) (2 * W - t), split n w (W + t) (2 * W - t)]
    have hc := Finset.sum_add_sum_compl S w
    have e1 : Finset.univ.filter (fun i : Fin n => Sum.inl i ∈ Finset.univ.filter
        (fun x => Sum.elim (fun i => i ∈ S) (fun b => b = false) x)) = S := by
      ext i; simp
    have e2 : Finset.univ.filter (fun i : Fin n => Sum.inl i ∈ (Finset.univ.filter
        (fun x => Sum.elim (fun i => i ∈ S) (fun b => b = false) x))ᶜ) = Sᶜ := by
      ext i; simp
    rw [e1, e2]
    simp
    change ∑ i ∈ S, w i + ∑ i ∈ Sᶜ, w i = W at hc
    omega
  · rintro ⟨H, hH⟩
    have tot := Finset.sum_add_sum_compl H v
    have hu : ∑ i, v i = W + (W + t) + (2 * W - t) := by
      simp [v, Fintype.sum_sum_type, W]; omega
    rw [hu] at tot
    simp only [v] at hH tot
    rw [split n w (W + t) (2 * W - t)] at hH tot
    set A := Finset.univ.filter (fun i : Fin n => Sum.inl i ∈ H)
    have hc : ∑ i ∈ A, w i + ∑ i ∈ Aᶜ, w i = W := Finset.sum_add_sum_compl A w
    by_cases h1 : Sum.inr true ∈ H <;> by_cases h2 : Sum.inr false ∈ H <;> simp [h1, h2] at hH tot
    · exact ⟨A, by omega⟩
    · exact ⟨Aᶜ, by omega⟩
    · exact ⟨A, by omega⟩
    · exact ⟨A, by omega⟩
