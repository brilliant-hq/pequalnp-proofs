import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_762

open Finset

-- Padding lemma, the same as our own PEqualNP.Outside.L_lib_591.pad.
theorem pad {K : Type} [Field K] {ι : Type} [Fintype ι] {α β : Type} (d : ℕ)
    (hd : Fintype.card ι ≤ d) (a : α → ι → K) (b : β → ι → K) :
    ∃ (A : α → Fin d → K) (B : β → Fin d → K),
      ∀ p q, ∑ σ, a p σ * b q σ = ∑ j : Fin d, A p j * B q j := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin d) (by simpa using hd)
  refine ⟨fun p => Function.extend e (a p) 0, fun q => Function.extend e (b q) 0, fun p q => ?_⟩
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    have hj' : ¬∃ x, e x = j := by simpa [Set.mem_range] using hj
    dsimp only
    rw [Function.extend_apply' _ _ _ hj']
    simp
  · intro σ
    simp [e.injective.extend_apply]

end PEqualNP.Outside.L_lib_762

open PEqualNP.Outside.L_lib_762 in
theorem PEqualNP.Outside.L_lib_762 : ∀ (F : Type) [Field F] (n m r : ℕ) (A : Matrix (Fin n) (Fin m) F),
  A.rank ≤ r ↔
    ∃ (u : Fin r → Fin n → F) (v : Fin r → Fin m → F), ∀ i j, A i j = ∑ k, u k i * v k j := by
  intro F _ n m r A
  constructor
  · intro hr
    let W := LinearMap.range A.mulVecLin
    let bs := Module.finBasisOfFinrankEq F W (rfl : Module.finrank F W = A.rank)
    let w : Fin m → W := fun j => ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
    have key : ∀ i j, A i j = ∑ k, (bs k : Fin n → F) i * bs.repr (w j) k := by
      intro i j
      have h := congrArg (fun x : W => (x : Fin n → F) i) (bs.sum_repr (w j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h
      have hw : (w j : Fin n → F) i = A i j := by simp [w, Matrix.mulVec_single]
      rw [← hw, ← h]
      simp only [mul_comm]
    obtain ⟨U, V, hUV⟩ := pad r (by rw [Fintype.card_fin]; exact hr) (fun i k => (bs k : Fin n → F) i)
      (fun j k => bs.repr (w j) k)
    exact ⟨fun k i => U i k, fun k j => V j k, fun i j => (key i j).trans (hUV i j)⟩
  · rintro ⟨u, v, h⟩
    have hA : A = Matrix.of (fun i k => u k i) * Matrix.of (fun k j => v k j) := by
      ext i j; simp [Matrix.mul_apply, h]
    rw [hA]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
